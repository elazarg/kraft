/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Interval.Finset.Nat

/-!
# Kraft Sum Helpers

This file provides helper lemmas for working with Kraft sums.

## Main results

* `sum_range_lt_one_of_sum_range_le_one`: If a sum over `k` terms is `≤ 1`, then proper prefix
  sums are `< 1`.
* `tsum_lt_one_of_partial_lt_one`: If all partial sums are `< 1`, so is the infinite sum.
-/

section Sum

/-- Helper: if a nonnegative series of length `k` sums to `≤ 1`,
then every proper prefix sum is `< 1`. -/
lemma sum_range_lt_one_of_sum_range_le_one
    {r : ℝ} (hr : 0 < r) {k n : ℕ} (hnk : n < k)
    {lNat : ℕ → ℕ}
    (h_le : (∑ t ∈ Finset.range k, r ^ lNat t) ≤ 1) :
    (∑ t ∈ Finset.range n, r ^ lNat t) < 1 := by
  -- `S(n) < S(n+1) ≤ S(k) ≤ 1`
  refine lt_of_lt_of_le ?_ h_le

  have hlt_succ : (∑ t ∈ Finset.range n, r ^ lNat t)
      < (∑ t ∈ Finset.range (n+1), r ^ lNat t) := by
    simp [Finset.sum_range_succ]
    have : 0 < r ^ lNat n := by
      exact pow_pos hr _
    linarith

  apply lt_of_lt_of_le hlt_succ

  refine le_trans ?_ le_rfl

  have hsub : Finset.range (n+1) ⊆ Finset.range k :=
    Finset.range_mono (Nat.succ_le_of_lt hnk)
  refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
  intro _ _ _
  exact le_of_lt (pow_pos hr _)

/-- From `Summable` + `tsum ≤ 1`, every proper finite prefix sum is `< 1`. -/
lemma prefix_sum_lt_one_of_tsum_le_one
    {D : ℕ} (hD : 1 < D)
    {l : ℕ → ℕ}
    (h_summable : Summable (fun n => (1 / D : ℝ) ^ l n))
    (h_sum_le_one : ∑' n, (1 / D : ℝ) ^ l n ≤ 1) :
    ∀ n, (∑ k < n, (1 / D : ℝ) ^ l k) < 1 := by
  intro n
  have h_pos : (0 : ℝ) < 1 / D :=
    one_div_pos.mpr (by exact_mod_cast Nat.zero_lt_of_lt hD)

  have h_le : (∑ k ∈ Finset.range (n+1), (1 / D : ℝ) ^ l k) ≤ 1 := by
    -- `range n ⊆ range (n+1)` and term is nonneg, so sum over n+1 ≥ sum over n,
    -- but we need ≤1, so just prove directly via `sum_le_tsum` with `n+1`
    have h_le_tsum' :
        (∑ k ∈ Finset.range (n+1), (1 / D : ℝ) ^ l k) ≤ ∑' k, (1 / D : ℝ) ^ l k :=
      Summable.sum_le_tsum _ (fun _ _ => by positivity) h_summable
    exact le_trans h_le_tsum' h_sum_le_one

  simpa [Nat.Iio_eq_range] using
    sum_range_lt_one_of_sum_range_le_one h_pos (Nat.lt_succ_self n) h_le

lemma prefix_sum_lt_one_of_fin_sum_le_one
    {D k : ℕ} (hD : 1 < D)
    {l : ℕ → ℕ}
    (h_sum : (∑ i : Fin k, (1 / (D : ℝ)) ^ l i.val) ≤ 1) :
    ∀ i : Fin k,
      (∑ t ∈ Finset.range i.val, (1 / D : ℝ) ^ l t) < 1 := by
  intro i
  refine sum_range_lt_one_of_sum_range_le_one ?_ i.isLt ?_
  · rw [one_div_pos]
    exact_mod_cast Nat.zero_lt_of_lt hD
  · -- rewrite `h_sum` from a `Fin`-sum to a `range`-sum
    have h_eq : (∑ j : Fin k, (1 / (D : ℝ)) ^ l j)
     = (∑ t ∈ Finset.range k, (1 / (D : ℝ)) ^ l t) := by
      simpa using (Fin.sum_univ_eq_sum_range (n := k) (fun t : ℕ => (1 / (D : ℝ)) ^ l t))
    simp_all only

lemma strict_prefix_of_tsum_le_one
    {D : ℕ} (hD : 1 < D) {l : ℕ → ℕ}
    (h_summable : Summable (fun i => (1 / D : ℝ) ^ l i))
    (h_sum : (∑' i, (1 / D : ℝ) ^ l i) ≤ 1) :
    ∀ n, (∑ k < n, (1 / D : ℝ) ^ l k) < 1 := by
    intro n
    have h_pos : (0 : ℝ) < 1 / D :=
      one_div_pos.mpr (by exact_mod_cast Nat.zero_lt_of_lt hD)

    have h_le_tsum : (∑ k ∈ Finset.range (n + 1), (1 / D : ℝ) ^ l k) ≤ ∑' k, (1 / D : ℝ) ^ l k :=
      Summable.sum_le_tsum _ (fun _ _ => by positivity) h_summable

    have h_le_one : (∑ k ∈ Finset.range (n + 1), (1 / D : ℝ) ^ l k) ≤ 1 :=
      le_trans h_le_tsum h_sum

    simpa [<-Nat.Iio_eq_range] using sum_range_lt_one_of_sum_range_le_one h_pos (Nat.lt_succ_self n) h_le_one

end Sum
