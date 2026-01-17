/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Monotone.Defs

/-!
# Extension of Finite Sequences

This file provides utilities for extending finite length sequences to infinite ones.

## Main definitions

* `extShift`: Extends a length sequence on `Fin k` to a monotone sequence on `ℕ`.

## Main results

* `extShift_monotone`: The extended sequence is monotone if the original is.
-/

namespace InformationTheory

def extShift {k: ℕ} (lastL s : ℕ) (l : Fin k → ℕ) (n : ℕ) : ℕ :=
  if h : n < k then l ⟨n,h⟩ else lastL + s + (n - k + 1)

@[simp] lemma ext_shift_eq {k : ℕ} (l : Fin k → ℕ) (lastL s : ℕ) (i : Fin k) :
  extShift lastL s l i = l i := by
  -- `i.val < k` so we take the `if`-true branch, and `Fin.eta` cleans the subtype
  simp [extShift, i.isLt, Fin.eta]

lemma ext_shift_monotone (k : ℕ) (l : Fin k → ℕ) (hmono : Monotone l) (hk : k ≠ 0) (s : ℕ) :
    Monotone (extShift (l ⟨k-1, Nat.pred_lt (by simpa using hk : k.sub 0 ≠ 0)⟩) s l) := by
  intro i j hij
  by_cases hi : i < k
  · by_cases hj : j < k
    · -- both in the Fin-part
      have hij' : (⟨i, hi⟩ : Fin k) ≤ ⟨j, hj⟩ := by exact hij
      simp [extShift, hi, hj]
      exact hmono hij'
    · have hk1lt : k - 1 < k := Nat.pred_lt (by simpa using hk : k.sub 0 ≠ 0)
      have h_le_last : l ⟨i, hi⟩ ≤ l ⟨k - 1, hk1lt⟩ := by
        exact hmono (Nat.le_pred_of_lt hi)
      simp [extShift, hi, hj]
      simp_all only [Nat.le_add_right_of_le]
  · -- i ≥ k implies j ≥ k (since i ≤ j)
    have hj : ¬ j < k := by
      have : k ≤ i := le_of_not_gt hi
      exact not_lt_of_ge (le_trans this hij)
    simp [extShift, hi, hj]
    have hk_le_i : k ≤ i := le_of_not_gt hi
    have hk_le_j : k ≤ j := le_trans hk_le_i hij
    -- goal is `i ≤ j - k + k`, rewrite RHS to `j`
    simpa [Nat.sub_add_cancel hk_le_j] using hij

lemma ext_shift_apply_lt {k : ℕ} (lastL s : ℕ) (l : Fin k → ℕ) {n : ℕ} (hn : n < k) :
  extShift lastL s l n = l ⟨n, hn⟩ := by
  simp [extShift, hn]

end InformationTheory
