/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

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
* `gibbs_sum_log_ratio_nonneg_of_ac` : the zero-mass-tolerant Gibbs inequality for `0 ≤ p`,
  `0 ≤ q`, `∑ q ≤ 1`, and absolute continuity `q i = 0 → p i = 0`. Rerouted through
  `InformationTheory.klFin_nonneg` (`Divergence.Basic`), which already generalizes this exact
  statement, rather than reproving it from scratch — the two were previously independent
  elementary proofs of the same fact.

## References

* Cover & Thomas, *Elements of Information Theory*, Chapter 2
-/

@[expose] public section

namespace InformationTheory

open Real

variable {I : Type*} [Fintype I]

/-- Entropy in **base D** (so measured in "D-ary digits"), defined via `negMulLog`. -/
noncomputable def entropy (D : ℕ) (p : I → ℝ) : ℝ :=
  (∑ i, Real.negMulLog (p i)) / log D

/-- `entropy` is nonnegative. -/
theorem entropy_nonneg (D : ℕ) (hD : 1 < D) {p : I → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hp_sum : ∑ i, p i = 1) :
    0 ≤ entropy D p := by
  have hlogD_pos : 0 < log D := log_pos (by exact_mod_cast hD)
  apply div_nonneg _ (le_of_lt hlogD_pos)
  refine Finset.sum_nonneg (fun i _ => negMulLog_nonneg (hp i) ?_)
  have : p i ≤ ∑ i, p i := Finset.single_le_sum (fun i _ => hp i) (Finset.mem_univ i)
  rwa [hp_sum] at this

/-- Finite Gibbs inequality without positivity: `p` and `q` may vanish, `q` may carry less
than the full mass (`∑ q ≤ 1`), and only the absolute-continuity condition `q i = 0 → p i = 0`
is required. This is the zero-mass-tolerant form conditional entropy needs, since marginals and
conditional slices routinely hit zero mass. A thin wrapper around `klFin_nonneg`
(`Divergence.Basic`), which already generalizes this to `∑ q ≤ ∑ p`. -/
theorem gibbs_sum_log_ratio_nonneg_of_ac
    {p q : I → ℝ}
    (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (hq_nonneg : ∀ i, 0 ≤ q i) (hq_sum : ∑ i, q i ≤ 1)
    (hac : ∀ i, q i = 0 → p i = 0) :
    0 ≤ ∑ i, p i * log (p i / q i) :=
  klFin_nonneg hp_nonneg hq_nonneg hac (by rw [hp_sum]; exact hq_sum)

end InformationTheory
