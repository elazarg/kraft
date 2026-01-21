import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Real.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

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

/-- Growth axiom for a cost function.

`costGrowth cost D` asserts that, in any finite `T`, the number of elements of cost exactly `s`
is at most `D^s`. This is the abstract analogue of "there are at most `D^s` strings of length `s`"
in a `D`-ary alphabet. -/
def costGrowth (cost : M → ℕ) (D_nat : ℕ) : Prop :=
  ∀ (T : Finset M) (s : ℕ),
    (T.filter (fun x => cost x = s)).card ≤ D_nat ^ s

variable [Monoid M]

private lemma sum_mu_filter_le_one_of_card_le
    {T : Finset M} {s : ℕ} {D_nat : ℕ}
    (dPos : 0 < D_nat)
    (m : WeightModel M D_nat)
    (h_card : (T.filter (fun x => m.cost x = s)).card ≤ D_nat ^ s) :
    (∑ x ∈ T.filter (fun x => m.cost x = s), m.μ x) ≤ 1 := by
  let D : ℝ≥0 := D_nat
  have hD0 : D ≠ 0 := by positivity
  calc
    ∑ x ∈ T.filter (fun x => m.cost x = s), m.μ x
      ≤ ∑ x ∈ T.filter (fun x => m.cost x = s), ((1 / D) ^ s) := by
          refine Finset.sum_le_sum ?_
          intro x hx
          have hx' : m.cost x = s := (Finset.mem_filter.mp hx).right
          simpa [D, hx'] using (m.μ_le x)
    _ = ((T.filter (fun x => m.cost x = s)).card) * ((1 / D) ^ s) := by
          simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((D_nat ^ s : ℕ) ) * ((1 / D) ^ s) := by
          gcongr
    _ = 1 := by
          simp [D, hD0]

/-- The r-fold product of elements from a finite set, defined via Lists. -/
def tupleProduct {S : Finset M} {r : ℕ} (w : Fin r → S) : M :=
  (List.ofFn (fun i => (w i).1)).prod

/-- The "weight" function (1/D)^ℓ(x) is a Monoid Homomorphism to (ℝ, *). -/
noncomputable def weightHom {ℓ : M → ℕ} (D_nat : ℕ)
    (h_add : ∀ a b, ℓ (a * b) = ℓ a + ℓ b) : M →* ℝ≥0 :=
  { toFun := fun x => (( (D_nat : ℝ≥0) )⁻¹) ^ ℓ x
    map_one' := by
      have : ℓ 1 + ℓ 1 = ℓ 1 := by simpa using (h_add 1 1)
      have h1 : ℓ 1 = 0 := Nat.add_left_cancel this
      simp [h1]
    map_mul' := by intro a b; simp [h_add, pow_add] }

private lemma len_one {ℓ : M → ℕ} (h_add : ∀ a b : M, ℓ (a * b) = ℓ a + ℓ b) :
    ℓ 1 = 0 := by
  have h : ℓ 1 + ℓ 1 = ℓ 1 := by simpa using (h_add 1 1)
  exact (Nat.add_left_cancel h)

private lemma len_list_prod {ℓ : M → ℕ}
    (h_add : ∀ a b : M, ℓ (a * b) = ℓ a + ℓ b) :
    ∀ xs : List M, ℓ xs.prod = (xs.map ℓ).sum := by
  intro xs
  induction xs with
  | nil => simp [len_one h_add]
  | cons a xs ih => simp [h_add, ih]

lemma tupleProduct_len {ℓ : M → ℕ} {S : Finset M} {r : ℕ}
    (h_add : ∀ a b, ℓ (a * b) = ℓ a + ℓ b) (w : Fin r → S) :
    ℓ (tupleProduct w) = ∑ i : Fin r, ℓ ((w i).val) := by
  simp [tupleProduct, len_list_prod h_add, List.sum_ofFn]

private lemma kraft_sum_pow_eq_sum_tupleProduct
    {S : Finset M} {r : ℕ} (μ : M →* ℝ≥0) :
    (∑ x ∈ S, μ x) ^ r = ∑ w : Fin r → S, μ (tupleProduct w) := by
  have hS : (∑ x ∈ S, μ x) = ∑ x : S, μ x := (Finset.sum_coe_sort S μ).symm
  calc
    (∑ x ∈ S, μ x) ^ r
        = (∑ x : S, μ x) ^ r := by simp [hS]
    _ = ∑ w : Fin r → S, ∏ i : Fin r, μ (w i) := Fintype.sum_pow (f := fun x : S => μ x) r
    _ = ∑ w : Fin r → S, μ (tupleProduct w) := by
          rw [Fintype.sum_congr]
          intro i
          simp [tupleProduct, MonoidHom.map_list_prod, List.prod_ofFn]

lemma pow_sum_le_linear_bound_of_inj
    {S : Finset M} {D_nat : ℕ} (dPos : 0 < D_nat)
    (m : WeightModel M D_nat)
    (hgrowth : costGrowth m.cost D_nat)
    (hinj : ∀ r, Function.Injective (tupleProduct (S := S) (r := r)))
    (r : ℕ) :
    (∑ x ∈ S, m.μ x) ^ r ≤ (r * (S.sup m.cost) + 1) := by
  classical
  -- Let $maxLen = \max_{w \in S} |w|$.
  set maxLen := S.sup m.cost
  let T := Finset.image tupleProduct (Finset.univ : Finset (Fin r → S))
  have h_injective :
    ∑ w : Fin r → S, m.μ (tupleProduct w)
      ≤ ∑ s ∈ Finset.Icc 0 (r * maxLen),
          ∑ x ∈ T.filter (fun x => m.cost x = s), m.μ x := by
    rw [← Finset.sum_biUnion]
    · apply le_of_eq
      refine Finset.sum_bij (fun w _ => tupleProduct w) ?_ ?_ (by
        intro b hb
        rcases Finset.mem_biUnion.mp hb with ⟨s, -, hb⟩
        rcases Finset.mem_filter.mp hb with ⟨hb, -⟩
        rcases Finset.mem_image.mp hb with ⟨a, ha, rfl⟩
        exact ⟨a, ha, rfl⟩
      ) (by simp)
      · intro a _
        have hlen := tupleProduct_len m.cost_mul a
        simp only [T, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_filter, Finset.mem_image,
                   Finset.mem_univ, true_and]
        use m.cost (tupleProduct a)
        refine ⟨⟨?_, ?_⟩, ⟨a, rfl⟩, rfl⟩
        · -- r ≤ (tupleProduct a).length
          -- Each selected codeword has positive length (since [] ∉ S).
          -- Sum of r ones ≤ sum of the lengths.
          exact Nat.zero_le _
        · -- Upper bound: |w| ≤ r * maxLen
          -- length of r-fold product
          rw [hlen]
          -- rewrite r*maxLen as a sum and compare termwise
          -- (either of the next two styles)
          · -- style 1 (closest to your old code)
            grw [show r * maxLen = ∑ _ : Fin r, maxLen by simp]
            exact Finset.sum_le_sum (fun i _ => Finset.le_sup (a i).2)
      · intro a₁ _ a₂ _ h_eq
        exact hinj r h_eq
    · exact fun _ _ _ _ _ => Finset.disjoint_left.mpr (by grind)
  -- Since $\sum_{x \in \{0,1\}^s} 2^{-|x|} = 1$ for any $s$, we have
  -- $\sum_{s=r}^{r\ell} \sum_{x \in \{0,1\}^s} 2^{-|x|}
  --   = \sum_{s=r}^{r\ell} 1 = r\ell - r + 1 \le r\ell$.
  have h_sum_one :
      ∀ s ∈ Finset.Icc 0 (r * maxLen),
        ∑ x ∈ T.filter (fun x => m.cost x = s), m.μ x ≤ 1 := by
    intro s _
    apply sum_mu_filter_le_one_of_card_le (T := T) (s := s) dPos m
    simpa using (hgrowth (T := T) (s := s))
  have h_pow :
      (∑ x ∈ S, m.μ x) ^ r
        = ∑ w : Fin r → S, m.μ (tupleProduct w) :=
    kraft_sum_pow_eq_sum_tupleProduct (μ := m.μ)
  refine le_trans h_pow.le
    <| h_injective.trans
    <| le_trans (Finset.sum_le_sum h_sum_one) ?_
  rcases r with (_ | _ | r) <;> rcases maxLen with (_ | _ | maxLen) <;> norm_num at *

/-- Kraft inequality under injectivity, in the abstract `WeightModel` setting.

Assuming:
* positive costs on `S`,
* the growth axiom for `cost`,
* and injectivity of `tupleProduct` on `r`-tuples from `S` (a unique decoding hypothesis),

we obtain `∑ x ∈ S, μ x ≤ 1`.

This statement is formulated in terms of an arbitrary multiplicative weight `μ`,
only requiring the domination `μ x ≤ (1/D)^cost x`. -/
public lemma kraft_inequality_of_injective'
    {S : Finset M} {D_nat : ℕ}
    (D_pos : 0 < D_nat)
    (m : WeightModel M D_nat)
    (h_growth : costGrowth m.cost D_nat)
    (h_inj : ∀ r, Function.Injective (tupleProduct (S := S) (r := r))) :
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
    (h_growth : costGrowth ℓ D_nat)
    (hμ : ∀ x, μ x ≤ (D_nat : ℝ≥0)⁻¹ ^ ℓ x)
    (h_inj : ∀ r, Function.Injective (tupleProduct (S := S) (r := r))) :
    ∑ x ∈ S, μ x ≤ 1 := by
  exact kraft_inequality_of_injective' D_pos h_growth h_inj
     (m := { cost := ℓ, μ := μ, μ_le := (by simp_all), cost_mul := h_add })

theorem kraft_inequality_of_injective {ℓ : M → ℕ}
    {S : Finset M} {D_nat : ℕ}
    (D_pos : 0 < D_nat)
    (h_add : ∀ a b, ℓ (a * b) = ℓ a + ℓ b)
    (h_growth : costGrowth ℓ D_nat)
    (h_inj : ∀ r, Function.Injective (tupleProduct (S := S) (r := r))) :
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
    (h_growth : costGrowth ℓ D_nat)
    (h_inj : ∀ r, Function.Injective (tupleProduct (S := S) (r := r))) :
    ∑ x ∈ S, (1 / (D_nat : ℝ)) ^ (ℓ x) ≤ 1 := by
  let k := kraft_inequality_of_injective D_pos h_add h_growth h_inj
  rw [<-one_div] at *
  have : 1 / (D_nat : ℝ) = (1 / D_nat : ℝ≥0) := by simp
  rw [this]
  exact_mod_cast k

end InformationTheory
