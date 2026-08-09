/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Topology.Algebra.InfiniteSum.Defs

/-!
# Kraft Sum Helpers

This file provides helper lemmas for working with Kraft sums.

## Main results

* `sum_range_lt_one_of_sum_range_le_one`: If a sum over `k` terms is `≤ 1`, then proper prefix
  sums are `< 1`.
* `prefix_sum_lt_one_of_tsum_le_one`: From summability and `tsum ≤ 1`, every finite prefix sum
  is `< 1`.
* `prefix_sum_lt_one_of_fin_sum_le_one`: Variant for finite sums indexed by `Fin k`.
-/

@[expose] public section

namespace InformationTheory

section Sum

/-- A proper prefix of a nonnegative finite sum bounded by `1` is strictly below `1` when its
first omitted term is positive. -/
lemma sum_range_lt_one_of_sum_range_le_one
    {f : ℕ → ℝ} (hf : ∀ i, 0 ≤ f i) {k n : ℕ} (hfn : 0 < f n) (hnk : n < k)
    (h_le : (∑ t ∈ Finset.range k, f t) ≤ 1) :
    (∑ t ∈ Finset.range n, f t) < 1 :=
  (Finset.sum_lt_sum_of_subset (Finset.range_mono hnk.le) (Finset.mem_range.mpr hnk)
      (by simp) hfn fun i _ _ => hf i).trans_le h_le

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
    sum_range_lt_one_of_sum_range_le_one (fun i => (pow_pos h_pos (l i)).le)
      (pow_pos h_pos (l n)) (Nat.lt_succ_self n) h_le

lemma prefix_sum_lt_one_of_fin_sum_le_one
    {D k : ℕ} (hD : 1 < D)
    {l : ℕ → ℕ}
    (h_sum : (∑ i : Fin k, (1 / (D : ℝ)) ^ l i.val) ≤ 1) :
    ∀ i : Fin k,
      (∑ t ∈ Finset.range i.val, (1 / D : ℝ) ^ l t) < 1 := by
  intro i
  refine sum_range_lt_one_of_sum_range_le_one (fun t => ?_) (by positivity) i.isLt ?_
  · positivity
  · -- rewrite `h_sum` from a `Fin`-sum to a `range`-sum
    have h_eq : (∑ j : Fin k, (1 / (D : ℝ)) ^ l j)
     = (∑ t ∈ Finset.range k, (1 / (D : ℝ)) ^ l t) := by
      simpa using (Fin.sum_univ_eq_sum_range (n := k) (fun t : ℕ => (1 / (D : ℝ)) ^ l t))
    simp_all only

end Sum

end InformationTheory
