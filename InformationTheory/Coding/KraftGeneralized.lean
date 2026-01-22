import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Real.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

import InformationTheory.Coding.KraftNatural

namespace InformationTheory

open NNReal


/-- A `WeightModel` packages the hypotheses needed for Kraft-style bounds in a graded monoid.

It consists of:
* a cost function `cost : M → ℕ` that is additive under multiplication (`cost_mul`),
* a multiplicative weight `μ : M →* ℝ≥0`,
* and a pointwise domination condition `μ x ≤ (1 / D)^cost x`.

This abstracts the usual "weight = D^{-length}" setup: the theorem only needs a multiplicative
weight bounded by the canonical exponential weight induced by the cost. -/
structure WeightModel (M : Type*) [Monoid M] (D : ℕ) where
  cost : M → ℕ
  μ : M →* ℝ≥0
  μ_le : ∀ x, μ x ≤ ( (1 / (D : ℝ≥0)) ^ cost x : ℝ≥0 )
  cost_mul : ∀ a b, cost (a * b) = cost a + cost b

variable {M : Type*}
variable [Monoid M]

/-- The "weight" function (1/D)^ℓ(x) is a Monoid Homomorphism to (ℝ, *). -/
noncomputable def weightHom {ℓ : M → ℕ} (D_nat : ℕ)
    (h_add : ∀ a b, ℓ (a * b) = ℓ a + ℓ b) : M →* ℝ≥0 :=
  { toFun := fun x => (( (D_nat : ℝ≥0) )⁻¹) ^ ℓ x
    map_one' := by
      have : ℓ 1 + ℓ 1 = ℓ 1 := by simpa using (h_add 1 1)
      have h1 : ℓ 1 = 0 := Nat.add_left_cancel this
      simp [h1]
    map_mul' := by intro a b; simp [h_add, pow_add] }

private lemma kraft_sum_pow_eq_sum_prodTuple
    {S : Finset M} {r : ℕ} (μ : M →* ℝ≥0) :
    (∑ x ∈ S, μ x) ^ r = ∑ w : Fin r → S, μ (prodTuple w) := by
  have hS : (∑ x ∈ S, μ x) = ∑ x : S, μ x := (Finset.sum_coe_sort S μ).symm
  calc
    (∑ x ∈ S, μ x) ^ r
        = (∑ x : S, μ x) ^ r := by simp [hS]
    _ = ∑ w : Fin r → S, ∏ i : Fin r, μ (w i) := Fintype.sum_pow (f := fun x : S => μ x) r
    _ = ∑ w : Fin r → S, μ (prodTuple w) := by
          rw [Fintype.sum_congr]
          intro i
          simp [prodTuple, MonoidHom.map_list_prod, List.prod_ofFn]

private lemma pow_sub_mul_inv_pow_eq_inv_pow
    {D : ℝ≥0} (hD0 : D ≠ 0) {N c : ℕ} (hc : c ≤ N) :
    D ^ (N - c) * (D ^ N)⁻¹ = (D⁻¹) ^ c := by
  -- cancel by multiplying by D^N
  have hDN0 : D ^ N ≠ 0 := pow_ne_zero _ hD0
  have hc0 : D ^ c ≠ 0 := pow_ne_zero _ hD0
  apply mul_right_cancel₀ hDN0
  -- simplify LHS
  calc
    (D ^ (N - c) * (D ^ N)⁻¹) * D ^ N
        = D ^ (N - c) := by simp [hDN0]
    _ = (D ^ c)⁻¹ * (D ^ (N - c) * D ^ c) := by
          -- insert (D^c)⁻¹*D^c = 1 and rearrange
          calc
            D ^ (N - c) = (1 : ℝ≥0) * D ^ (N - c) := by simp
            _ = ((D ^ c)⁻¹ * D ^ c) * D ^ (N - c) := by simp [hc0]
            _ = (D ^ c)⁻¹ * (D ^ (N - c) * D ^ c) := by
                  simp [mul_assoc, mul_left_comm, mul_comm]
    _ = (D ^ c)⁻¹ * D ^ N := by
          -- rewrite D^N = D^(N-c)*D^c
          have hpow : D ^ N = D ^ (N - c) * D ^ c := by
            simpa [Nat.sub_add_cancel hc] using (pow_add D (N - c) c)
          simp [hpow]
    _ = (D⁻¹) ^ c * D ^ N := by simp [inv_pow]

private lemma sum_inv_pow_cost_prodTuple_le
    {S : Finset M} {D_nat : ℕ} {cost : M → ℕ} (r : ℕ)
    (dPos : 0 < D_nat)
    (cost_mul : ∀ a b, cost (a * b) = cost a + cost b)
    (hgrowth : ExpBounded cost D_nat)
    (hinj : ∀ r, Function.Injective (prodTuple (S := S) (r := r))) :
    (∑ w : Fin r → S, ((D_nat : ℝ≥0)⁻¹) ^ cost (prodTuple w)) ≤ (r * S.sup cost + 1 : ℝ≥0) := by
  let N := r * S.sup cost
  let D : ℝ≥0 := D_nat
  have hD0 : D ≠ 0 := by positivity
  calc  ∑ w : Fin r → S, (D⁻¹) ^ cost (prodTuple w)
      = ∑ w : Fin r → S, (D ^ (N - cost (prodTuple w))) * (D ^ N)⁻¹ := by
          apply Finset.sum_congr rfl
          intro w hw
          rw [pow_sub_mul_inv_pow_eq_inv_pow hD0]
          exact len_prodTuple_le_mul_sup cost_mul
    _ =  (∑ w : Fin r → S, D ^ (N - cost (prodTuple w))) * (D ^ N)⁻¹ := by
          simp [Finset.sum_mul]
    _  ≤ ((N + 1 : ℝ≥0) * D ^ N) * (D ^ N)⁻¹ := by
          have hNN : (∑ w : Fin r → S, D ^ (N - cost (prodTuple w)))
              ≤ (N + 1 : ℝ≥0) * D ^ N := by
            subst D
            exact_mod_cast InformationTheory.mcmillan_counting_of_inj cost_mul hgrowth hinj r
          simpa using mul_le_mul_left hNN (D ^ N)⁻¹
  simp [N, hD0]

lemma pow_sum_le_linear_bound_of_inj
    {S : Finset M} {D_nat : ℕ}
    (D_pos : 0 < D_nat)
    (m : WeightModel M D_nat)
    (hgrowth : ExpBounded m.cost D_nat)
    (hinj : ∀ r, Function.Injective (prodTuple (S := S) (r := r)))
    (r : ℕ) :
    (∑ x ∈ S, m.μ x) ^ r ≤ (r * (S.sup m.cost) + 1) := by
  calc  (∑ x ∈ S, m.μ x) ^ r
       = ∑ w : Fin r → S, m.μ (prodTuple w) := kraft_sum_pow_eq_sum_prodTuple (μ := m.μ)
    _  ≤ ∑ w : Fin r → S, ((D_nat : ℝ≥0)⁻¹) ^ m.cost (prodTuple w) := by
           refine Finset.sum_le_sum ?_
           intro w hw
           simpa using (m.μ_le (prodTuple w))
    _  ≤ (r * S.sup m.cost + 1 : ℝ≥0) := by
           simpa using
            (sum_inv_pow_cost_prodTuple_le (r := r) (dPos := D_pos) m.cost_mul hgrowth hinj)

/-- Kraft inequality under injectivity, in the abstract `WeightModel` setting.

Assuming:
* positive costs on `S`,
* the growth axiom for `cost`,
* and injectivity of `prodTuple` on `r`-tuples from `S` (a unique decoding hypothesis),

we obtain `∑ x ∈ S, μ x ≤ 1`.

This statement is formulated in terms of an arbitrary multiplicative weight `μ`,
only requiring the domination `μ x ≤ (1/D)^cost x`. -/
public lemma kraft_inequality_of_injective'
    {S : Finset M} {D_nat : ℕ}
    (D_pos : 0 < D_nat)
    (m : WeightModel M D_nat)
    (h_growth : ExpBounded m.cost D_nat)
    (h_inj : ∀ r, Function.Injective (prodTuple (S := S) (r := r))) :
    ∑ x ∈ S, m.μ x ≤ 1 := by
  -- 1. Setup contradiction
  set K : ℝ≥0 := ∑ x ∈ S, m.μ x
  by_contra hK_gt_one
  rw [not_le] at hK_gt_one
  -- 2. Use the auxiliary bound: K^r ≤ r * maxLen
  set maxLen := S.sup m.cost
  have h_bound (r : ℕ) : K ^ r ≤ r * maxLen + 1 := by
    exact_mod_cast pow_sum_le_linear_bound_of_inj D_pos m h_growth h_inj r
  -- 3. Algebraic limit argument
  -- If K > 1, then K^r grows exponentially, while r * maxLen grows linearly.
  -- We prove (r * maxLen) / K^r tends to 0, implying eventually (r * maxLen) < K^r.
  have hAbs : |1 / (K: ℝ)| < 1 := by
    rw [abs_of_pos (by positivity)]
    exact (div_lt_one (by positivity)).mpr hK_gt_one
  have h_tendh_tendsto_linsto :
      Filter.Tendsto (fun r : ℕ => (maxLen : ℝ) * r / K ^ r) Filter.atTop (nhds 0) := by
    simpa [mul_comm, mul_left_comm, mul_div_assoc] using
      ((tendsto_self_mul_const_pow_of_abs_lt_one hAbs).const_mul (maxLen : ℝ))
  have h_tendsto_geo :
      Filter.Tendsto (fun r => 1 / (K:ℝ)^r) Filter.atTop (nhds 0) := by
    -- rewrite as (1/K)^r and apply abs_lt_1 lemma
    simpa [one_div, div_eq_mul_inv, pow_mul] using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hAbs)
  have h_tendsto_sum :
      Filter.Tendsto
        (fun r : ℕ =>
          (maxLen : ℝ) * r / K ^ r + 1 / K ^ r)
        Filter.atTop (nhds 0) := by
    simpa [zero_add] using (h_tendh_tendsto_linsto.add h_tendsto_geo)

  -- 4. Derive contradiction
  have hIio : Set.Iio (1 : ℝ) ∈ nhds (0 : ℝ) := by
    simpa using (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))

  obtain ⟨r, hr_tendsto⟩ :=
    Filter.eventually_atTop.mp <|
      (h_tendsto_sum.eventually hIio)

  have hr_lt : ∀ b ≥ r,
      ↑maxLen * ↑b / ↑K ^ b + 1 / ↑K ^ b < (1 : ℝ) := by
    simpa [Set.Iio] using hr_tendsto

  -- Pick a large enough r (must be ≥ 1)
  let r_large := max r 1
  have h_strict_sum : ↑maxLen * ↑r_large / ↑K ^ r_large + 1 / ↑K ^ r_large < (1 : ℝ) :=
    hr_lt r_large (le_max_left _ _)

  have h_strict_sum :
      (maxLen : ℝ) * r_large / (K : ℝ) ^ r_large
        + (1 : ℝ) / (K : ℝ) ^ r_large < 1 := by
    have hmem :
        ( maxLen * r_large / K ^ r_large
          + (1 : ℝ) / K ^ r_large )
          ∈ {x | x < 1} := by
      exact hr_tendsto r_large (le_max_left _ _)
    simpa using hmem

  have h_strict_div :
     (maxLen * r_large + 1) / (K:ℝ)^r_large < 1 := by
    -- turn sum of fractions into one fraction
    -- (a/b + 1/b) = (a+1)/b
    simpa [add_div] using h_strict_sum

  rw [div_lt_iff₀ (pow_pos (by positivity) _)] at *
  -- Turn the ≤ bound into an ℝ inequality
  have h_le_real :
      ((K : ℝ) ^ r_large) ≤ (r_large : ℝ) * (maxLen : ℝ) + 1 := by
    -- h_bound r_large : (K:ℝ≥0)^r_large ≤ (r_large*maxLen+1)  (in ℝ≥0)
    exact_mod_cast (h_bound r_large)

  -- Turn the strict inequality into the “(r*maxLen+1) < K^r” shape
  have h_strict_real :
      (r_large : ℝ) * (maxLen : ℝ) + 1 < (K : ℝ) ^ r_large := by
    -- your h_strict_div is: ↑maxLen * ↑r_large + 1 < 1 * ↑K ^ r_large
    -- commute the product and drop the `1 *`
    simpa [mul_comm, one_mul] using h_strict_div

  -- Contradiction: K^r ≤ r*maxLen+1 < K^r
  exact (lt_irrefl ((K : ℝ) ^ r_large)) (lt_of_le_of_lt h_le_real h_strict_real)


/-- Kraft inequality for an arbitrary multiplicative weight dominated by the canonical exponential weight.

This is a convenience wrapper around `kraft_inequality_of_injective'` that avoids constructing
a `WeightModel` explicitly: given `μ : M →* ℝ` and a cost `ℓ : M → ℕ` with
`μ x ≤ (1/D)^ℓ x`, it proves `∑ x ∈ S, μ x ≤ 1` under the same growth and injectivity hypotheses. -/
theorem kraft_inequality_of_injective_of_le
    {ℓ : M → ℕ}
    {S : Finset M} {D_nat : ℕ}
    (D_pos : 0 < D_nat)
    (μ : M →* ℝ≥0)
    (h_add : ∀ a b, ℓ (a * b) = ℓ a + ℓ b)
    (h_growth : ExpBounded ℓ D_nat)
    (hμ : ∀ x, μ x ≤ (D_nat : ℝ≥0)⁻¹ ^ ℓ x)
    (h_inj : ∀ r, Function.Injective (prodTuple (S := S) (r := r))) :
    ∑ x ∈ S, μ x ≤ 1 := by
  exact kraft_inequality_of_injective' D_pos h_growth h_inj
     (m := { cost := ℓ, μ := μ, μ_le := (by simp_all), cost_mul := h_add })

theorem kraft_inequality_of_injective {ℓ : M → ℕ}
    {S : Finset M} {D_nat : ℕ}
    (D_pos : 0 < D_nat)
    (h_add : ∀ a b, ℓ (a * b) = ℓ a + ℓ b)
    (h_growth : ExpBounded ℓ D_nat)
    (h_inj : ∀ r, Function.Injective (prodTuple (S := S) (r := r))) :
    ∑ x ∈ S, ((D_nat : ℝ≥0)⁻¹) ^ (ℓ x) ≤ 1 :=
  kraft_inequality_of_injective_of_le D_pos h_add h_growth (fun _ => le_rfl) h_inj
    (μ := weightHom D_nat h_add)

/-- Kraft inequality in the canonical exponential-weight form.

This is the standard statement recovered from `kraft_inequality_of_injective_of_le`
by taking `μ x = (1/D)^ℓ x`. It is the easiest-to-use API when one already has an
additive cost function `ℓ`. -/
theorem kraft_inequality_of_injective_real {ℓ : M → ℕ}
    {S : Finset M} {D_nat : ℕ}
    (D_pos : 0 < D_nat)
    (h_add : ∀ a b, ℓ (a * b) = ℓ a + ℓ b)
    (h_growth : ExpBounded ℓ D_nat)
    (h_inj : ∀ r, Function.Injective (prodTuple (S := S) (r := r))) :
    ∑ x ∈ S, (1 / (D_nat : ℝ)) ^ (ℓ x) ≤ 1 := by
  let k := kraft_inequality_of_injective D_pos h_add h_growth h_inj
  rw [<-one_div] at *
  have : 1 / (D_nat : ℝ) = (1 / D_nat : ℝ≥0) := by simp
  rw [this]
  exact_mod_cast k

end InformationTheory
