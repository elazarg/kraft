/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Monotone.Defs

/-!
# Extension of Finite Sequences

This file provides utilities for extending finite length sequences to infinite ones.

## Main definitions

* `extShift`: Extends a length sequence on `Fin k` to a monotone sequence on `ℕ`.

## Main results

* `extShift_eq`: Simp lemma showing `extShift` agrees with the original function on `Fin k`.
* `extShift_monotone`: The extended sequence is monotone if the original is.
-/

@[expose] public section

namespace InformationTheory

/-- Extends a finite length sequence `l : Fin k → ℕ` to all naturals by continuing
monotonically after the last element. For `n < k`, returns `l(n)`. For `n ≥ k`,
returns `lastL + s + (n - k + 1)`, where `lastL` is typically `l(k-1)` and `s` is a step size. -/
def extShift {k : ℕ} (lastL s : ℕ) (l : Fin k → ℕ) (n : ℕ) : ℕ :=
  if h : n < k then l ⟨n, h⟩ else lastL + s + (n - k + 1)

@[simp] lemma extShift_eq {k : ℕ} (l : Fin k → ℕ) (lastL s : ℕ) (i : Fin k) :
    extShift lastL s l i = l i := by
  -- `i.val < k` so we take the `if`-true branch, and `Fin.eta` cleans the subtype
  simp [extShift, i.isLt, Fin.eta]

lemma extShift_monotone (k : ℕ) (l : Fin k → ℕ) (hmono : Monotone l) (hk : k ≠ 0) (s : ℕ) :
    Monotone (extShift (l ⟨k - 1, Nat.pred_lt (by simpa using hk : k.sub 0 ≠ 0)⟩) s l) := by
  intro i j hij
  simp only [extShift]
  split_ifs with hi hj
  · exact hmono hij
  · have hlast := hmono (show (⟨i, hi⟩ : Fin k) ≤
        ⟨k - 1, Nat.pred_lt (by simpa using hk : k.sub 0 ≠ 0)⟩ from Nat.le_pred_of_lt hi)
    grind
  · grind
  · grind

end InformationTheory
