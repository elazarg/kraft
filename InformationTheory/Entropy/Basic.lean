/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import InformationTheory.Divergence.Basic

/-!
# Shannon entropy

This file defines finite Shannon entropy, independent of any coding-theory content: neither
`entropy` nor its basic Gibbs/nonnegativity facts have anything to do with codes, uniquely
decodable or otherwise. `InformationTheory.Coding.SourceCodingLowerBound` builds on this file
(rather than the other way around) to state and prove the source coding theorem;
`InformationTheory.Entropy.ConditionalEntropy` and `InformationTheory.Entropy.Uniform` build on
it directly.

## Main definitions

* `entropy (D : ℕ) (p : I → ℝ) : ℝ := (∑ i, Real.negMulLog (p i)) / log D`, Shannon entropy in
  base `D`.

## Main results

* `entropy_nonneg` : `0 ≤ entropy D p`.
* `entropy_eq_zero_iff` : a probability mass function has zero entropy exactly when one point
  has all the mass.
* `entropy_eq_sum_neg_logb` : `entropy D p = ∑ i, -p i * logb D (p i)`, the usual
  `-∑ p log_D p` form.
* `entropy_base_change` : entropy in two nontrivial bases differs by the usual logarithmic
  conversion factor.
* `gibbs_sum_log_ratio_nonneg_of_ac` : the zero-mass-tolerant Gibbs inequality for `0 ≤ p`,
  `0 ≤ q`, `∑ q ≤ 1`, and absolute continuity `q i = 0 → p i = 0`. Rerouted through
  `klFin_nonneg` (`Divergence.Basic`), which already generalizes this exact
  statement, rather than reproving it from scratch — the two were previously independent
  elementary proofs of the same fact.

## References

* Cover & Thomas, *Elements of Information Theory*, Chapter 2
-/

@[expose] public section

namespace InformationTheory

open Real

variable {I : Type*} [Fintype I] {p q : I → ℝ}

/-- Entropy in **base D** (so measured in "D-ary digits"), defined via `negMulLog`. -/
noncomputable def entropy (D : ℕ) (p : I → ℝ) : ℝ :=
  (∑ i, Real.negMulLog (p i)) / log D

/-- `entropy` is nonnegative for a nonnegative subprobability mass function. -/
theorem entropy_nonneg (D : ℕ) (hD : 1 < D) (hp : ∀ i, 0 ≤ p i)
    (hp_sum : ∑ i, p i ≤ 1) :
    0 ≤ entropy D p := by
  have hlogD_pos : 0 < log D := log_pos (by exact_mod_cast hD)
  apply div_nonneg _ (le_of_lt hlogD_pos)
  refine Finset.sum_nonneg (fun i _ => negMulLog_nonneg (hp i) ?_)
  exact (Finset.single_le_sum (fun i _ => hp i) (Finset.mem_univ i)).trans hp_sum

private lemma negMulLog_eq_zero_iff_of_nonneg_of_le_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    negMulLog x = 0 ↔ x = 0 ∨ x = 1 := by
  constructor
  · intro h
    rcases hx0.eq_or_lt with rfl | hx0
    · simp
    rcases hx1.eq_or_lt with rfl | hx1
    · simp
    exact False.elim <| (ne_of_gt (neg_pos.mpr (mul_log_neg hx0 hx1)))
      (by simpa [negMulLog_eq_neg] using h)
  · rintro (rfl | rfl) <;> simp

/-- A probability mass function has zero entropy exactly when one point has all the mass. -/
theorem entropy_eq_zero_iff (D : ℕ) (hD : 1 < D) (hp : ∀ i, 0 ≤ p i)
    (hp_sum : ∑ i, p i = 1) :
    entropy D p = 0 ↔ ∃ i, p i = 1 := by
  classical
  have hp_le_one (i : I) : p i ≤ 1 :=
    (Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)).trans_eq hp_sum
  have hlogD : log (D : ℝ) ≠ 0 := ne_of_gt (log_pos (by exact_mod_cast hD))
  constructor
  · intro hentropy
    have hsum : ∑ i, negMulLog (p i) = 0 := by
      simpa [entropy, hlogD] using hentropy
    have hp_zero_or_one (i : I) : p i = 0 ∨ p i = 1 :=
      (negMulLog_eq_zero_iff_of_nonneg_of_le_one (hp i) (hp_le_one i)).mp
        ((Finset.sum_eq_zero_iff_of_nonneg fun j _ => negMulLog_nonneg (hp j) (hp_le_one j)).mp
          hsum i (Finset.mem_univ i))
    by_contra h
    push Not at h
    have hp_zero : ∀ i, p i = 0 := fun i => (hp_zero_or_one i).resolve_right (h i)
    simp [hp_zero] at hp_sum
  · rintro ⟨i, hi⟩
    have hsum_erase : ∑ j ∈ Finset.univ.erase i, p j = 0 := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), hi] at hp_sum
      linarith
    have hp_zero {j : I} (hji : j ≠ i) : p j = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun k _ => hp k).mp hsum_erase j (by simp [hji])
    have hsum : ∑ j, negMulLog (p j) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      by_cases hji : j = i
      · simp [hji, hi]
      · simp [hp_zero hji]
    simp [entropy, hsum]

/-- Convenience: base-`D` entropy equals the usual `∑ -p * logb_D p`. -/
theorem entropy_eq_sum_neg_logb (D : ℕ) (p : I → ℝ) :
    entropy D p = ∑ i, - p i * logb D (p i) := by
  unfold entropy
  calc
    (∑ i, negMulLog (p i)) / log D
        = (log (D : ℝ))⁻¹ * ∑ i, negMulLog (p i) := by simp [div_eq_mul_inv, mul_comm]
    _   = ∑ i, (log (D : ℝ))⁻¹ * negMulLog (p i) := by simp [Finset.mul_sum]
    _   = ∑ i, - p i * logb D (p i) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            simp [negMulLog_def, logb, div_eq_mul_inv, mul_assoc, mul_comm]

/-- Change of base for entropy. -/
theorem entropy_base_change (D E : ℕ) (hD : 1 < D) (hE : 1 < E) (p : I → ℝ) :
    entropy D p = entropy E p * (log E / log D) := by
  have hlogD : log (D : ℝ) ≠ 0 := ne_of_gt (log_pos (by exact_mod_cast hD))
  have hlogE : log (E : ℝ) ≠ 0 := ne_of_gt (log_pos (by exact_mod_cast hE))
  unfold entropy
  field_simp

/-- Finite Gibbs inequality without positivity: `p` and `q` may vanish, `q` may carry less
than the full mass (`∑ q ≤ 1`), and only the absolute-continuity condition `q i = 0 → p i = 0`
is required. This is the zero-mass-tolerant form conditional entropy needs, since marginals and
conditional slices routinely hit zero mass. A thin wrapper around `klFin_nonneg`
(`Divergence.Basic`), which already generalizes this to `∑ q ≤ ∑ p`. -/
theorem gibbs_sum_log_ratio_nonneg_of_ac
    (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (hq_nonneg : ∀ i, 0 ≤ q i) (hq_sum : ∑ i, q i ≤ 1)
    (hac : ∀ i, q i = 0 → p i = 0) :
    0 ≤ ∑ i, p i * log (p i / q i) :=
  klFin_nonneg hp_nonneg hq_nonneg hac (by rw [hp_sum]; exact hq_sum)

end InformationTheory
