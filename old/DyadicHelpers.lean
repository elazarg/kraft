import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Field.Rat

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace Dyadic

/-!
# Dyadic.Basic

Small algebraic facts about dyads (powers of two) in:
* `ℕ`: monotonicity, divisibility
* `ℚ`: clean API via `ℤ`-exponents (`zpow`) so division/inverses are painless
-/

/-! ## ℕ: order and divisibility for powers of two -/

lemma two_lt : (1 : ℕ) < 2 := by decide

@[simp] lemma pow2_pos (n : ℕ) : 0 < (2^n : ℕ) := Nat.pow_pos (by decide)

@[simp] lemma pow2_ne_zero (n : ℕ) : (2^n : ℕ) ≠ 0 := by
  exact ne_of_gt (pow2_pos n)

lemma pow2_le_pow2_iff {a b : ℕ} : (2^a : ℕ) ≤ 2^b ↔ a ≤ b := by
  exact Nat.pow_le_pow_iff_right two_lt

lemma pow2_lt_pow2_iff {a b : ℕ} : (2^a : ℕ) < 2^b ↔ a < b := by
  -- strict version is derived from the non-strict one + antisymmetry
  constructor
  · intro h
    have hab : a ≤ b := (pow2_le_pow2_iff).1 (le_of_lt h)
    by_contra hna
    have hba : b ≤ a := le_of_not_gt hna
    have : (2^b : ℕ) ≤ 2^a := (pow2_le_pow2_iff).2 hba
    exact (not_lt_of_ge this) h
  · intro h
    exact Nat.pow_lt_pow_of_lt (by decide : 1 < (2:ℕ)) h

lemma pow2_dvd_pow2_iff {a b : ℕ} : (2^a : ℕ) ∣ 2^b ↔ a ≤ b := by
  exact Nat.pow_dvd_pow_iff_le_right two_lt

lemma pow2_dvd_of_le {a b : ℕ} (h : (2^a : ℕ) ≤ 2^b) : (2^a : ℕ) ∣ 2^b := by
  exact (pow2_dvd_pow2_iff).2 (pow2_le_pow2_iff.1 h)

/-- If every element is divisible by `k`, their list sum is divisible by `k`. -/
lemma sum_dvd_of_forall_dvd {k : ℕ} {L : List ℕ} (h : ∀ x ∈ L, k ∣ x) : k ∣ L.sum := by
  induction L with
  | nil => simp
  | cons a tl ih =>
      simp
      apply Nat.dvd_add
      · exact h a (by simp)
      · apply ih
        intro x hx
        exact h x (by simp [hx])

/-! ## ℚ dyads via ℤ exponents -/

/-- Dyadic rational `2^z` with `z : ℤ`. -/
def q (z : ℤ) : ℚ := (2 : ℚ) ^ z

@[simp] lemma q_zero : q 0 = (1 : ℚ) := by
  simp [q]

@[simp] lemma q_one : q 1 = (2 : ℚ) := by
  simp [q]

lemma two_ne_zero : (2 : ℚ) ≠ 0 := by norm_num

/-- Core maneuver: `2^(m-n) = 2^m * (2^n)⁻¹` (needs `n ≤ m`). -/
lemma two_pow_sub (m n : ℕ) (h : n ≤ m) :
    (2 : ℚ) ^ (m - n) = (2 : ℚ) ^ m * ((2 : ℚ) ^ n)⁻¹ := by
  simpa using (pow_sub₀ (a := (2 : ℚ)) (ha := two_ne_zero) h)

/-- Rearranged form: `2^m * (2^n)⁻¹ = 2^(m-n)` (needs `n ≤ m`). -/
lemma two_pow_mul_inv (m n : ℕ) (h : n ≤ m) :
    (2 : ℚ) ^ m * ((2 : ℚ) ^ n)⁻¹ = (2 : ℚ) ^ (m - n) := by
  simpa using (two_pow_sub m n h).symm

/-- Same, but written with the common `(2^m : ℚ)` style. -/
lemma two_pow_mul_inv' (m n : ℕ) (h : n ≤ m) :
    (2^m : ℚ) * (2^n : ℚ)⁻¹ = (2^(m - n) : ℚ) := by
  -- `(2^m : ℚ)` is definitionaly `(2:ℚ)^m`
  simpa using (two_pow_mul_inv m n h)

/-- Division form: `(2^m)/(2^n) = 2^(m-n)` (needs `n ≤ m`). -/
lemma two_pow_div (m n : ℕ) (h : n ≤ m) :
    (2^m : ℚ) / (2^n : ℚ) = (2^(m - n) : ℚ) := by
  simp [div_eq_mul_inv, two_pow_mul_inv' m n h]

/-- `2^{-(n-1)} = 2 * 2^{-n}` for `n>0`. -/
lemma inv_pow_sub_one {n : ℕ} (hn : 0 < n) :
    (2 ^ (n - 1) : ℚ)⁻¹ = 2 * (2 ^ n : ℚ)⁻¹ := by
  have h1n : 1 ≤ n := Nat.succ_le_iff.2 hn
  have hnz  : (2 ^ n : ℚ) ≠ 0 := by
    exact pow_ne_zero n (by norm_num : (2 : ℚ) ≠ 0)
  have hnz' : (2 ^ (n - 1) : ℚ) ≠ 0 := by
    exact pow_ne_zero (n - 1) (by norm_num : (2 : ℚ) ≠ 0)

  -- clear inverses
  field_simp [hnz, hnz']
  -- goal becomes `2^n = 2 * 2^(n-1)`
  calc
    (2 ^ n : ℚ) = (2 ^ (n - 1 + 1) : ℚ) := by simp [Nat.sub_add_cancel h1n]
    _ = (2 ^ (n - 1) : ℚ) * 2 := by simp [pow_succ]
    _ = 2 * (2 ^ (n - 1) : ℚ) := by ring
  ring

end Dyadic
