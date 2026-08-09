/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Interval.Finset.Nat

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Kraft Code Construction: numerator arithmetic

This file provides the interval-arithmetic core for constructing prefix-free codes from length
sequences satisfying Kraft's inequality (converse direction): `kraftNumerator` maps a monotone
length sequence to interval boundaries in base-`D` representation. The companion reordering
lemmas that reduce the general case to this monotone one live in
`ConstructionHelpers.KraftOrder` instead.

## Main definitions

* `kraftNumerator`: Maps a length sequence to interval boundaries in base-D representation.

## Main results

* `kraftNumerator.div_pow_eq_sum`: The key invariant relating numerators to Kraft partial sums.
* `kraftNumerator.add_one_mul_pow_le`: Quantitative separation of two code intervals.
* `kraftNumerator.strictMono`: Numerators increase strictly, ensuring distinct code intervals.
-/

@[expose] public section

namespace InformationTheory

open scoped Real

section Numerator
/-- Generalized interval start function for constructing prefix-free codes over alphabet of size D.

For a monotone length sequence `l`, `kraftNumerator D l n` is chosen so that
`kraftNumerator D l n / D^{l n}` equals the partial Kraft sum `Σ_{k<n} D^{-l k}`. -/
def kraftNumerator (D : ℕ) (l : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => (kraftNumerator D l n + 1) * D ^ (l (n + 1) - l n)

/-- `kraftNumerator D l n / D^{l n}` equals the partial Kraft sum `Σ_{k<n} (1/D)^{l k}`.

This is the key invariant that ensures non-overlapping D-adic intervals. -/
lemma kraftNumerator.div_pow_eq_sum {D : ℕ} (hD : 0 < D) {l : ℕ → ℕ} (h_mono : Monotone l) (n : ℕ) :
    (kraftNumerator D l n : ℝ) / D ^ l n = ∑ k ∈ Finset.range n, (1 / D : ℝ) ^ l k := by
  have hD_pos : (0 : ℝ) < D := by exact_mod_cast hD
  have hD_ne : (D : ℝ) ≠ 0 := ne_of_gt hD_pos
  induction n with
  | zero =>
    simp only [kraftNumerator, CharP.cast_eq_zero, zero_div, Finset.range_zero, Finset.sum_empty]
  | succ n ih =>
    simp only [one_div, inv_pow, Finset.sum_range_succ]
    have h_sub :
        (kraftNumerator D l (n + 1) : ℝ) = (kraftNumerator D l n + 1) * D ^ (l (n + 1) - l n) := by
      simp only [kraftNumerator, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow]
    rw [h_sub]
    simp_all only [one_div, inv_pow]
    rw [← ih]
    rw [show l (n + 1) = l n + (l (n + 1) - l n) by rw [Nat.add_sub_of_le (h_mono (Nat.le_succ n))]]
    rw [pow_add]
    field_simp
    simp only [add_tsub_cancel_left]

/-- Distinct code intervals are quantitatively separated: the interval following `i`, scaled
to the length at `j`, starts no later than the interval at `j`. -/
lemma kraftNumerator.add_one_mul_pow_le {D : ℕ} {l : ℕ → ℕ} (hmono : Monotone l)
    {i j : ℕ} (hij : i < j) :
    (kraftNumerator D l i + 1) * D ^ (l j - l i) ≤ kraftNumerator D l j := by
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases h : i = j
    · subst j
      simp [kraftNumerator]
    · have hij' : i < j := by omega
      have hli : l i ≤ l j := hmono hij'.le
      have hlj : l j ≤ l (j + 1) := hmono (Nat.le_succ j)
      have hexp : l (j + 1) - l i = (l j - l i) + (l (j + 1) - l j) := by omega
      calc
        (kraftNumerator D l i + 1) * D ^ (l (j + 1) - l i) =
            ((kraftNumerator D l i + 1) * D ^ (l j - l i)) *
              D ^ (l (j + 1) - l j) := by rw [hexp, pow_add, mul_assoc]
        _ ≤ kraftNumerator D l j * D ^ (l (j + 1) - l j) :=
          Nat.mul_le_mul_right _ (ih hij')
        _ ≤ (kraftNumerator D l j + 1) * D ^ (l (j + 1) - l j) :=
          Nat.mul_le_mul_right _ (Nat.le_succ _)
        _ = kraftNumerator D l (j + 1) := by rw [kraftNumerator]

/-- If `i < j`, dividing the numerator at `j` down to the scale at `i` cannot recover the
numerator at `i`. -/
lemma kraftNumerator.div_pow_ne_of_lt {D : ℕ} {l : ℕ → ℕ} (hD : 0 < D)
    (hmono : Monotone l) {i j : ℕ} (hij : i < j) :
    kraftNumerator D l j / D ^ (l j - l i) ≠ kraftNumerator D l i := by
  intro hdiv
  have hpow : 0 < D ^ (l j - l i) := Nat.pow_pos hD
  have hle : kraftNumerator D l i + 1 ≤
      kraftNumerator D l j / D ^ (l j - l i) :=
    (Nat.le_div_iff_mul_le hpow).2 (kraftNumerator.add_one_mul_pow_le hmono hij)
  omega

/-- Helper: turn the invariant + `< 1` into the numeric bound `A n < D^(lNat n)`. -/
lemma kraftNumerator.lt_pow_of_sum_range_lt_one
    {D : ℕ} (hD : 0 < D) {lNat : ℕ → ℕ} (hmono : Monotone lNat)
    {n : ℕ}
    (h_sum_lt1 : (∑ t ∈ Finset.range n, (1 / D : ℝ) ^ lNat t) < 1) :
    kraftNumerator D lNat n < D ^ lNat n := by
  have hD_pos_real : (0 : ℝ) < D := by exact_mod_cast hD

  have h_eq :
      (kraftNumerator D lNat n : ℝ) / (D : ℝ) ^ lNat n
        = ∑ t ∈ Finset.range n, (1 / D : ℝ) ^ lNat t :=
    kraftNumerator.div_pow_eq_sum hD hmono n

  have hden : 0 < (D : ℝ) ^ lNat n := by positivity
  have hdivlt : (kraftNumerator D lNat n : ℝ) / (D : ℝ) ^ lNat n < 1 := by
    simpa [h_eq] using h_sum_lt1

  have hlt_real : (kraftNumerator D lNat n : ℝ) < (D : ℝ) ^ lNat n := by
    -- `a/b < 1` with `0<b` gives `a < b`
    exact (div_lt_one hden).1 hdivlt

  -- cast back to `ℕ`
  exact_mod_cast hlt_real

lemma kraftNumerator.bound {D : ℕ} {l : ℕ → ℕ} (h_mono : Monotone l) (hD : 0 < D)
  (h_prefix_lt_one : ∀ n, (∑ k < n, (1 / D : ℝ) ^ l k) < 1) :
    ∀ n, kraftNumerator D l n < D ^ l n := by
  intro n
  have h_range : (∑ k ∈ Finset.range n, (1 / (D : ℝ)) ^ l k) < 1 := by
    simpa [<-Nat.Iio_eq_range] using h_prefix_lt_one n
  exact kraftNumerator.lt_pow_of_sum_range_lt_one hD h_mono h_range

/-- `kraftNumerator D l` is strictly increasing as soon as `D > 0`.

In particular it is `StrictMono` under the standing assumption `1 < D`. -/
lemma kraftNumerator.strictMono {D : ℕ} {l : ℕ → ℕ} (hD : 0 < D) :
    StrictMono (kraftNumerator D l) := by
  -- it suffices to show `A n < A (n+1)` for all `n`
  refine strictMono_nat_of_lt_succ (fun n => ?_)
  -- unfold the successor clause
  simp [kraftNumerator]
  -- let `p = D^(...)`, which is positive since `D>0`
  have hp : 0 < D ^ (l (n + 1) - l n) := Nat.pow_pos hD
  -- `A n < A n + 1 ≤ (A n + 1) * p`
  exact lt_of_lt_of_le (Nat.lt_add_one _) (Nat.le_mul_of_pos_right _ hp)

end Numerator

end InformationTheory
