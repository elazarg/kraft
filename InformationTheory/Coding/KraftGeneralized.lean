/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.NNReal.Basic
public import Mathlib.Data.Real.Basic
public import InformationTheory.Coding.KraftNatural

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Generalized Kraft Inequality for Monoids

This file proves an abstract version of the Kraft inequality for arbitrary monoids with
a length-like function, using real-valued (ℝ≥0) weights instead of natural number counting.

## Main definitions

* `WeightModel`: A structure packaging a cost function, multiplicative weight homomorphism,
  and domination condition for abstract Kraft-style bounds.
* `weightHom`: The canonical weight homomorphism `(1/D)^ℓ(x)` induced by a grading function.

## Main results

* `pow_sum_le_linear_bound_of_inj`: The key lemma showing that if products of length `r` are
  injective, then the `r`-th power of the Kraft sum is bounded linearly in `r`.
* `kraft_inequality_of_injective`: Abstract Kraft inequality for monoids where the product
  map is injective, using ℝ≥0-valued weights.
* `kraft_inequality_of_injective_real`: Real-valued version of the abstract Kraft inequality.

The proof technique uses the natural number bounds from `KraftNatural.lean` and takes limits
to obtain results for real-valued weights.

Nothing in this repo depends on this file — `KraftConverse.lean` reaches its results via
`PrefixFree`/`Coding.Kraft` instead. Kept deliberately for the `WeightModel` abstraction itself,
which is strictly more general than `Mathlib.InformationTheory.Coding.KraftMcMillan` (arbitrary
monoids and real-valued weights, not just `List`/natural-number counting). Not proposed for
upstreaming alongside `KraftNatural.lean` (see `UpstreamPlan.md`), for the same reason: it would
sit next to an already-merged proof of the same theorem.

## References

* McMillan, B. (1956), "Two inequalities implied by unique decipherability"
-/

@[expose] public section

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
noncomputable def weightHom {ℓ : M → ℕ} (base : ℕ)
    (h_add : ∀ a b, ℓ (a * b) = ℓ a + ℓ b) : M →* ℝ≥0 :=
  { toFun := fun x => (( (base : ℝ≥0) )⁻¹) ^ ℓ x
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
    {S : Finset M} {base : ℕ} {cost : M → ℕ} {r : ℕ}
    (base_pos : 0 < base)
    (cost_mul : ∀ a b, cost (a * b) = cost a + cost b)
    (hgrowth : ExpBounded cost base)
    (hinj : Function.Injective (prodTuple (S := S) (r := r))) :
    (∑ w : Fin r → S, ((base : ℝ≥0)⁻¹) ^ cost (prodTuple w)) ≤ (r * S.sup cost + 1 : ℝ≥0) := by
  let N := r * S.sup cost
  let D : ℝ≥0 := base
  have hD0 : D ≠ 0 := by positivity
  calc  ∑ w : Fin r → S, (D⁻¹) ^ cost (prodTuple w)
      = ∑ w : Fin r → S, (D ^ (N - cost (prodTuple w))) * (D ^ N)⁻¹ := by
          apply Finset.sum_congr rfl
          intro w hw
          rw [pow_sub_mul_inv_pow_eq_inv_pow hD0]
          exact len_prodTuple_le_mul_sup (prodTuple_len cost_mul) w
    _ =  (∑ w : Fin r → S, D ^ (N - cost (prodTuple w))) * (D ^ N)⁻¹ := by
          simp [Finset.sum_mul]
    _  ≤ ((N + 1 : ℝ≥0) * D ^ N) * (D ^ N)⁻¹ := by
          have hNN : (∑ w : Fin r → S, D ^ (N - cost (prodTuple w)))
              ≤ (N + 1 : ℝ≥0) * D ^ N := by
            subst D
            exact_mod_cast mcmillan_counting_of_inj cost_mul hgrowth hinj
          simpa using mul_le_mul_left hNN (D ^ N)⁻¹
  simp [N, hD0]

lemma pow_sum_le_linear_bound_of_inj
    {S : Finset M} {base : ℕ}
    (base_pos : 0 < base)
    (m : WeightModel M base)
    (hgrowth : ExpBounded m.cost base)
    {r : ℕ}
    (hinj : Function.Injective (prodTuple (S := S) (r := r))) :
    (∑ x ∈ S, m.μ x) ^ r ≤ (r * (S.sup m.cost) + 1) := by
  calc  (∑ x ∈ S, m.μ x) ^ r
       = ∑ w : Fin r → S, m.μ (prodTuple w) := kraft_sum_pow_eq_sum_prodTuple (μ := m.μ)
    _  ≤ ∑ w : Fin r → S, ((base : ℝ≥0)⁻¹) ^ m.cost (prodTuple w) := by
           refine Finset.sum_le_sum ?_
           intro w hw
           simpa using (m.μ_le (prodTuple w))
    _  ≤ (r * S.sup m.cost + 1 : ℝ≥0) := by
           simpa using
            (sum_inv_pow_cost_prodTuple_le (base_pos := base_pos) m.cost_mul hgrowth hinj)

/-- Kraft inequality under injectivity, in the abstract `WeightModel` setting.

Assuming:
* the growth axiom for `cost` (`ExpBounded`),
* and injectivity of `prodTuple` on `r`-tuples from `S` (a unique decoding hypothesis),

we obtain `∑ x ∈ S, μ x ≤ 1`.

This statement is formulated in terms of an arbitrary multiplicative weight `μ`,
only requiring the domination `μ x ≤ (1/D)^cost x`.

Proved by contradiction: if `K := ∑ x ∈ S, μ x > 1`, then `pow_sum_le_linear_bound_of_inj` gives
`K ^ r ≤ r * maxLen + 1` for every `r`, but `K > 1` makes the left side grow exponentially in
`r` while the right side only grows linearly — so `(r * maxLen + 1) / K ^ r → 0`, meaning
eventually `r * maxLen + 1 < K ^ r`, contradicting the bound. -/
public lemma kraft_inequality_of_injective'
    {S : Finset M} {base : ℕ}
    (base_pos : 0 < base)
    (m : WeightModel M base)
    (h_growth : ExpBounded m.cost base)
    (h_inj : ∀ r, Function.Injective (prodTuple (S := S) (r := r))) :
    ∑ x ∈ S, m.μ x ≤ 1 := by
  set K : ℝ≥0 := ∑ x ∈ S, m.μ x
  by_contra hK_gt_one
  rw [not_le] at hK_gt_one
  set maxLen := S.sup m.cost
  have h_bound (r : ℕ) : K ^ r ≤ r * maxLen + 1 := by
    exact_mod_cast pow_sum_le_linear_bound_of_inj base_pos m h_growth (h_inj r)
  -- If `K > 1`, then `K ^ r` grows exponentially while `r * maxLen` grows linearly.
  -- We prove `(r * maxLen) / K ^ r → 0`, implying eventually `r * maxLen + 1 < K ^ r`.
  have hAbs : |1 / (K : ℝ)| < 1 := by
    rw [abs_of_pos (by positivity)]
    exact (div_lt_one (by positivity)).mpr hK_gt_one
  have h_tendsto_lin :
      Filter.Tendsto (fun r : ℕ => (maxLen : ℝ) * r / K ^ r) Filter.atTop (nhds 0) := by
    simpa [mul_comm, mul_left_comm, mul_div_assoc] using!
      ((tendsto_self_mul_const_pow_of_abs_lt_one hAbs).const_mul (maxLen : ℝ))
  have h_tendsto_geo :
      Filter.Tendsto (fun r => 1 / (K : ℝ) ^ r) Filter.atTop (nhds 0) := by
    -- rewrite as (1/K)^r and apply abs_lt_1 lemma
    simpa [one_div, div_eq_mul_inv, pow_mul] using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hAbs)
  have h_tendsto_sum :
      Filter.Tendsto
        (fun r : ℕ => (maxLen : ℝ) * r / K ^ r + 1 / K ^ r)
        Filter.atTop (nhds 0) := by
    simpa [zero_add] using (h_tendsto_lin.add h_tendsto_geo)

  -- Derive the contradiction: pick `r` large enough that the sum above is `< 1`.
  have hIio : Set.Iio (1 : ℝ) ∈ nhds (0 : ℝ) := by
    simpa using (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨r, hr_lt⟩ := Filter.eventually_atTop.mp (h_tendsto_sum.eventually hIio)

  -- `r_large ≥ 1` and `r_large ≥ r`, so `hr_lt` applies at it.
  set r_large := max r 1 with hr_large_def
  have h_strict_sum :
      (maxLen : ℝ) * r_large / (K : ℝ) ^ r_large + (1 : ℝ) / (K : ℝ) ^ r_large < 1 :=
    hr_lt r_large (le_max_left _ _)

  have h_strict_div : (maxLen * r_large + 1 : ℝ) / (K : ℝ) ^ r_large < 1 := by
    -- turn the sum of fractions `a/b + 1/b` into the single fraction `(a+1)/b`
    simpa [add_div] using h_strict_sum

  have hKpow_pos : (0 : ℝ) < (K : ℝ) ^ r_large := pow_pos (by positivity) _
  rw [div_lt_iff₀ hKpow_pos, one_mul] at h_strict_div

  -- `h_bound r_large` says `K ^ r_large ≤ r_large * maxLen + 1`; `h_strict_div` (after
  -- commuting the product) says the reverse strictly — contradiction.
  have h_le_real : (K : ℝ) ^ r_large ≤ (r_large : ℝ) * (maxLen : ℝ) + 1 := by
    exact_mod_cast h_bound r_large
  have h_strict_real : (r_large : ℝ) * (maxLen : ℝ) + 1 < (K : ℝ) ^ r_large := by
    simpa [mul_comm] using h_strict_div

  exact lt_irrefl _ (lt_of_le_of_lt h_le_real h_strict_real)

/-- Kraft inequality for an arbitrary multiplicative weight dominated by the canonical
exponential weight.

This is a convenience wrapper around `kraft_inequality_of_injective'` that avoids constructing
a `WeightModel` explicitly: given `μ : M →* ℝ` and a cost `ℓ : M → ℕ` with
`μ x ≤ (1/D)^ℓ x`, it proves `∑ x ∈ S, μ x ≤ 1` under the same growth and injectivity hypotheses. -/
theorem kraft_inequality_of_injective_of_le
    {ℓ : M → ℕ}
    {S : Finset M} {base : ℕ}
    (base_pos : 0 < base)
    (μ : M →* ℝ≥0)
    (h_add : ∀ a b, ℓ (a * b) = ℓ a + ℓ b)
    (h_growth : ExpBounded ℓ base)
    (hμ : ∀ x, μ x ≤ (base : ℝ≥0)⁻¹ ^ ℓ x)
    (h_inj : ∀ r, Function.Injective (prodTuple (S := S) (r := r))) :
    ∑ x ∈ S, μ x ≤ 1 := by
  exact kraft_inequality_of_injective' base_pos h_growth h_inj
     (m := { cost := ℓ, μ := μ, μ_le := (by simp_all), cost_mul := h_add })

theorem kraft_inequality_of_injective {ℓ : M → ℕ}
    {S : Finset M} {base : ℕ}
    (base_pos : 0 < base)
    (h_add : ∀ a b, ℓ (a * b) = ℓ a + ℓ b)
    (h_growth : ExpBounded ℓ base)
    (h_inj : ∀ r, Function.Injective (prodTuple (S := S) (r := r))) :
    ∑ x ∈ S, ((base : ℝ≥0)⁻¹) ^ (ℓ x) ≤ 1 :=
  kraft_inequality_of_injective_of_le base_pos h_add h_growth (fun _ => le_rfl) h_inj
    (μ := weightHom base h_add)

/-- Kraft inequality in the canonical exponential-weight form.

This is the standard statement recovered from `kraft_inequality_of_injective_of_le`
by taking `μ x = (1/D)^ℓ x`. It is the easiest-to-use API when one already has an
additive cost function `ℓ`. -/
theorem kraft_inequality_of_injective_real {ℓ : M → ℕ}
    {S : Finset M} {base : ℕ}
    (base_pos : 0 < base)
    (h_add : ∀ a b, ℓ (a * b) = ℓ a + ℓ b)
    (h_growth : ExpBounded ℓ base)
    (h_inj : ∀ r, Function.Injective (prodTuple (S := S) (r := r))) :
    ∑ x ∈ S, (1 / (base : ℝ)) ^ (ℓ x) ≤ 1 := by
  let k := kraft_inequality_of_injective base_pos h_add h_growth h_inj
  rw [<-one_div] at *
  have : 1 / (base : ℝ) = (1 / base : ℝ≥0) := by simp
  rw [this]
  exact_mod_cast k

end InformationTheory
