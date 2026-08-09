/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
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
length sequence to interval boundaries in base-`D` representation. The companion
index-reordering machinery (`KraftOrder`, `kraftRank`, and the `exists_equiv_*_monotone` lemmas
that reduce the general case to this monotone one) lives in `ConstructionHelpers.KraftOrder`
instead — the two files share no declarations, only a common purpose, so they're kept separate.

## Main definitions

* `kraftNumerator`: Maps a length sequence to interval boundaries in base-D representation.

## Main results

* `kraftNumerator.div_pow_eq_sum`: The key invariant relating numerators to Kraft partial sums.
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
lemma kraftNumerator.div_pow_eq_sum {D : ℕ} (hD : 1 < D) {l : ℕ → ℕ} (h_mono : Monotone l) (n : ℕ) :
    (kraftNumerator D l n : ℝ) / D ^ l n = ∑ k ∈ Finset.range n, (1 / D : ℝ) ^ l k := by
  have hD_pos : (0 : ℝ) < D := by exact_mod_cast Nat.zero_lt_of_lt hD
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

/-- Closed form for `kraftNumerator` as a Nat sum of scaled powers. -/
lemma kraftNumerator.eq_sum_pow_range
    (D : ℕ) (l : ℕ → ℕ) (hmono : Monotone l) :
    ∀ n, kraftNumerator D l n = ∑ t ∈ Finset.range n, D ^ (l n - l t) := by
  intro n
  induction n with
  | zero =>
    simp [kraftNumerator]
  | succ n ih =>
    -- Notation
    have hln : l n ≤ l (n + 1) := hmono (Nat.le_succ n)
    set a : ℕ := l (n + 1) - l n

    -- Start from the RHS for `n + 1`
    -- split off last term, then factor out `D ^ a` from the prefix sum
    simp [Finset.sum_range_succ, kraftNumerator, ih]

    -- Goal after simp is essentially:
    --   (∑ t ∈ range n, D ^ (l (n + 1) - l t)) + D ^ (l (n + 1) - l n)
    -- = ((∑ t ∈ range n, D ^ (l n - l t)) + 1) * D ^ (l (n + 1) - l n)

    -- Turn the prefix sum into a factored form
    have hfac :
        (∑ t ∈ Finset.range n, D ^ (l (n + 1) - l t)) =
          D ^ a * (∑ t ∈ Finset.range n, D ^ (l n - l t)) := by
      -- rewrite each term using exponent arithmetic:
      -- (l (n + 1) - l t) = (l (n + 1) - l n) + (l n - l t)
      -- then use `pow_add` and pull out `D ^ a`
      calc
        (∑ t ∈ Finset.range n, D ^ (l (n + 1) - l t)) =
            ∑ t ∈ Finset.range n, D ^ a * D ^ (l n - l t) := by
          refine Finset.sum_congr rfl ?_
          intro t ht
          have ht' : t < n := Finset.mem_range.mp ht
          have hlt : l t ≤ l n := hmono (Nat.le_of_lt_succ (Nat.lt_succ_of_lt ht'))
          have hlt' : l t ≤ l (n + 1) := le_trans hlt hln
          -- exponent identity
          have hexp : l (n + 1) - l t = a + (l n - l t) := by
            -- `a = l (n + 1) - l n`
            dsimp [a]
            omega
          simp [hexp, pow_add, mul_comm]
        _ = D ^ a * (∑ t ∈ Finset.range n, D ^ (l n - l t)) := by
          simp [Finset.mul_sum]

    -- Now finish the `succ` step by rewriting with `hfac`; the last term is `D ^ a`.
    have hlast : D ^ (l (n + 1) - l n) = D ^ a := by simp [a]
    simp [hfac, hlast, Nat.mul_add, Nat.mul_comm]

/--
Separation property for `A = kraftNumerator D l`:
if `i < j` then you cannot have `A j / D^(l j - l i) = A i` (even assuming `l i ≤ l j`).
-/
lemma kraftNumerator.div_separated_of_lt
    {D : ℕ} {l : ℕ → ℕ} (hD : 1 < D)
    (hmono : Monotone l) :
    ∀ {i j : ℕ}, i < j →
      ¬ (l i ≤ l j ∧ kraftNumerator D l j / D ^ (l j - l i) = kraftNumerator D l i) := by
  intro i j hij
  rintro ⟨hij_len, hdiv⟩

  have hDpos : 0 < D := Nat.zero_lt_of_lt hD
  set A : ℕ → ℕ := kraftNumerator D l
  set d : ℕ := D ^ (l j - l i)
  have hdpos : 0 < d := by
    dsimp [d]
    exact Nat.pow_pos hDpos

  -- Closed forms for A i and A j
  have hAi : A i = ∑ t ∈ Finset.range i, D ^ (l i - l t) := by
    simpa [A] using (kraftNumerator.eq_sum_pow_range D l hmono i)
  have hAj : A j = ∑ t ∈ Finset.range j, D ^ (l j - l t) := by
    simpa [A] using (kraftNumerator.eq_sum_pow_range D l hmono j)

  -- The partial sum up to `i+1` sits inside the sum up to `j`
  have hsub : Finset.range (i+1) ⊆ Finset.range j := by
    -- i+1 ≤ j since i< j
    exact Finset.range_mono (Nat.succ_le_of_lt hij)

  have hle_part :
      (∑ t ∈ Finset.range (i+1), D ^ (l j - l t))
        ≤ (∑ t ∈ Finset.range j, D ^ (l j - l t)) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
    intro x hx _hx'
    exact Nat.zero_le _

  have hle_part' :
      (∑ t ∈ Finset.range (i+1), D ^ (l j - l t)) ≤ A j := by
    simpa [hAj] using hle_part

  -- Rewrite the `range (i+1)` sum as (range i) + last
  have hsplit :
      (∑ t ∈ Finset.range (i+1), D ^ (l j - l t))
        = (∑ t ∈ Finset.range i, D ^ (l j - l t)) + D ^ (l j - l i) := by
    simp [Finset.sum_range_succ]

  -- Show the prefix sum is a multiple of `d` with coefficient `A i`
  have hmul_prefix :
      (∑ t ∈ Finset.range i, D ^ (l j - l t))
        = d * (∑ t ∈ Finset.range i, D ^ (l i - l t)) := by
    -- each term: D^(l j - l t) = D^(l j - l i) * D^(l i - l t)
    -- because l t ≤ l i ≤ l j
    calc
      (∑ t ∈ Finset.range i, D ^ (l j - l t))
          = ∑ t ∈ Finset.range i, d * (D ^ (l i - l t)) := by
              refine Finset.sum_congr rfl ?_
              intro t ht
              have ht' : t < i := Finset.mem_range.mp ht
              have hti : l t ≤ l i := hmono (Nat.le_of_lt ht')
              have htj : l t ≤ l j := le_trans hti hij_len
              have hexp : (l j - l t) = (l j - l i) + (l i - l t) := by
                -- needs l t ≤ l i ≤ l j
                omega
              -- unfold d and finish
              simp [d, hexp, pow_add, mul_comm]
      _   = d * (∑ t ∈ Finset.range i, D ^ (l i - l t)) := by
              simp [Finset.mul_sum]

  -- Now assemble: sum_{t≤i} = d*(A i + 1)
  have hlower :
      d * (A i + 1) ≤ A j := by
    -- start from hle_part' and rewrite LHS
    -- LHS = (prefix over range i) + d
    -- prefix = d * (sum range i ...)
    -- sum range i ... = A i
    have : (∑ t ∈ Finset.range (i+1), D ^ (l j - l t))
              = d * (A i + 1) := by
      -- rewrite using hsplit, hmul_prefix, hAi
      calc
        (∑ t ∈ Finset.range (i+1), D ^ (l j - l t))
            = (∑ t ∈ Finset.range i, D ^ (l j - l t)) + D ^ (l j - l i) := by
                exact hsplit
        _   = d * (∑ t ∈ Finset.range i, D ^ (l i - l t)) + d := by
                simp [hmul_prefix, d]
        _   = d * (A i) + d := by
                simp [hAi]
        _   = d * (A i + 1) := by
                simp [Nat.mul_add]
    -- apply ≤ using hle_part'
    simpa [this] using hle_part'
  rw [mul_comm] at hlower
  -- Divide both sides by `d`: (A i + 1) ≤ A j / d
  have hquot_ge : A i + 1 ≤ A j / d := by
    exact (Nat.le_div_iff_mul_le hdpos).2 hlower

  -- But we assumed A j / d = A i
  have : A i + 1 ≤ A i := by simp [hdiv, A, d] at hquot_ge
  exact Nat.not_succ_le_self _ this

/-- Helper: turn the invariant + `< 1` into the numeric bound `A n < D^(lNat n)`. -/
lemma kraftNumerator.lt_pow_of_sum_range_lt_one
    {D : ℕ} (hD : 1 < D) {lNat : ℕ → ℕ} (hmono : Monotone lNat)
    {n : ℕ}
    (h_sum_lt1 : (∑ t ∈ Finset.range n, (1 / D : ℝ) ^ lNat t) < 1) :
    kraftNumerator D lNat n < D ^ lNat n := by
  have hD_pos : 0 < D := Nat.zero_lt_of_lt hD
  have hD_pos_real : (0 : ℝ) < D := by exact_mod_cast hD_pos
  have hD_ne : (D : ℝ) ≠ 0 := ne_of_gt hD_pos_real

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

lemma kraftNumerator.bound {D : ℕ} {l : ℕ → ℕ} (h_mono : Monotone l) (hD : 1 < D)
  (h_prefix_lt_one : ∀ n, (∑ k < n, (1 / D : ℝ) ^ l k) < 1) :
    ∀ n, kraftNumerator D l n < D ^ l n := by
  intro n
  have h_range : (∑ k ∈ Finset.range n, (1 / (D : ℝ)) ^ l k) < 1 := by
    simpa [<-Nat.Iio_eq_range] using h_prefix_lt_one n
  exact kraftNumerator.lt_pow_of_sum_range_lt_one hD h_mono h_range

/-- `kraftNumerator D l` is strictly increasing as soon as `D > 0`.

In particular it is `StrictMono` under the standing assumption `1 < D`. -/
lemma kraftNumerator.strictMono {D : ℕ} {l : ℕ → ℕ} (hD : 1 < D) :
    StrictMono (kraftNumerator D l) := by
  -- it suffices to show `A n < A (n+1)` for all `n`
  refine strictMono_nat_of_lt_succ (fun n => ?_)
  -- unfold the successor clause
  simp [kraftNumerator]
  -- let `p = D^(...)`, which is positive since `D>0`
  have hDpos : 0 < D := Nat.zero_lt_of_lt hD
  have hp : 0 < D ^ (l (n + 1) - l n) := Nat.pow_pos hDpos
  -- `A n < A n + 1 ≤ (A n + 1) * p`
  exact lt_of_lt_of_le (Nat.lt_add_one _) (Nat.le_mul_of_pos_right _ hp)

end Numerator

end InformationTheory
