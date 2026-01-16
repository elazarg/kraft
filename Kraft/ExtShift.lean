import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Monotone.Defs

namespace Kraft

def ext_shift {k: ℕ} (Llast s : ℕ) (l : Fin k → ℕ) (n : ℕ) : ℕ :=
  if h : n < k then l ⟨n,h⟩ else Llast + s + (n - k + 1)

@[simp] lemma ext_shift_eq {k : ℕ} (l : Fin k → ℕ) (Llast s : ℕ) (i : Fin k) :
  ext_shift Llast s l i = l i := by
  -- `i.val < k` so we take the `if`-true branch, and `Fin.eta` cleans the subtype
  simp [ext_shift, i.isLt, Fin.eta]

lemma ext_shift_monotone (k : ℕ) (l : Fin k → ℕ) (hmono : Monotone l) (hk : k ≠ 0) (s : ℕ) :
    Monotone (ext_shift (l ⟨k-1, Nat.pred_lt (by simpa using hk : k.sub 0 ≠ 0)⟩) s l) := by
  intro i j hij
  by_cases hi : i < k
  · by_cases hj : j < k
    · -- both in the Fin-part
      have hij' : (⟨i, hi⟩ : Fin k) ≤ ⟨j, hj⟩ := by exact hij
      simp [ext_shift, hi, hj]
      exact hmono hij'
    · have hk1lt : k - 1 < k := Nat.pred_lt (by simpa using hk : k.sub 0 ≠ 0)
      have h_le_last : l ⟨i, hi⟩ ≤ l ⟨k - 1, hk1lt⟩ := by
        exact hmono (Nat.le_pred_of_lt hi)
      simp [ext_shift, hi, hj]
      simp_all only [Nat.le_add_right_of_le]
  · -- i ≥ k implies j ≥ k (since i ≤ j)
    have hj : ¬ j < k := by
      have : k ≤ i := le_of_not_gt hi
      exact not_lt_of_ge (le_trans this hij)
    simp [ext_shift, hi, hj]
    have hk_le_i : k ≤ i := le_of_not_gt hi
    have hk_le_j : k ≤ j := le_trans hk_le_i hij
    -- goal is `i ≤ j - k + k`, rewrite RHS to `j`
    simpa [Nat.sub_add_cancel hk_le_j] using hij

lemma ext_shift_apply_lt {k : ℕ} (Llast s : ℕ) (l : Fin k → ℕ) {n : ℕ} (hn : n < k) :
  ext_shift Llast s l n = l ⟨n, hn⟩ := by
  simp [ext_shift, hn]

end Kraft
