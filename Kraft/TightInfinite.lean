/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed

import Kraft.Basic
import Kraft.Digits
import Kraft.Helpers
import Kraft.McMillan

namespace Kraft

open scoped BigOperators Real
open Nat

section Ext

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
    · -- i < k, j ≥ k: bound l⟨i⟩ by Llast, then Llast ≤ Llast+s+...
      have hk1lt : k - 1 < k := Nat.pred_lt (by simpa using hk : k.sub 0 ≠ 0)
      have h_le_last : l ⟨i, hi⟩ ≤ l ⟨k - 1, hk1lt⟩ := by
        exact hmono (Nat.le_pred_of_lt hi)
      simp [ext_shift, hi, hj]
      simp_all only [le_add_right_of_le]
  · -- i ≥ k implies j ≥ k (since i ≤ j)
    have hj : ¬ j < k := by
      have : k ≤ i := le_of_not_gt hi
      exact not_lt_of_ge (le_trans this hij)
    simp [ext_shift, hi, hj]
    -- reduce to monotonicity of (n - k + 1)
    have hsub : i - k ≤ j - k := Nat.sub_le_sub_right hij k
    have hsub1 : i - k + 1 ≤ j - k + 1 := Nat.add_le_add_right hsub 1
    simp_all only [tsub_le_iff_right]

end Ext

/-- Generalized interval start function for constructing prefix-free codes over alphabet of size D.

For a monotone length sequence `l`, `kraft_numerator D l n` is chosen so that
`kraft_numerator D l n / D^{l n}` equals the partial Kraft sum `Σ_{k<n} D^{-l k}`. -/
def kraft_numerator (D : ℕ) (l : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => (kraft_numerator D l n + 1) * D ^ (l (n + 1) - l n)

/-- `kraft_numerator D l n / D^{l n}` equals the partial Kraft sum `Σ_{k<n} (1/D)^{l k}`.

This is the key invariant that ensures non-overlapping D-adic intervals. -/
lemma kraft_numerator_div_pow_eq_sum (D : ℕ) (hD : 1 < D) (l : ℕ → ℕ) (h_mono : Monotone l) (n : ℕ) :
    (kraft_numerator D l n : ℝ) / D ^ l n = ∑ k ∈ Finset.range n, (1 / D : ℝ) ^ l k := by
  have hD_pos : (0 : ℝ) < D := by exact_mod_cast Nat.zero_lt_of_lt hD
  have hD_ne : (D : ℝ) ≠ 0 := ne_of_gt hD_pos
  induction n with
  | zero => simp only [kraft_numerator, CharP.cast_eq_zero, zero_div, Finset.range_zero, Finset.sum_empty]
  | succ n ih =>
    simp only [one_div, inv_pow, Finset.sum_range_succ]
    have h_sub : (kraft_numerator D l (n + 1) : ℝ) = (kraft_numerator D l n + 1) * D ^ (l (n + 1) - l n) := by
      simp only [kraft_numerator, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow]
    rw [h_sub]
    simp_all only [one_div, inv_pow]
    rw [← ih]
    rw [show l (n + 1) = l n + (l (n + 1) - l n) by rw [Nat.add_sub_of_le (h_mono (Nat.le_succ n))]]
    rw [pow_add]
    field_simp
    simp only [add_tsub_cancel_left]

/-- Closed form for `kraft_numerator` as a Nat sum of scaled powers. -/
lemma kraft_numerator_eq_sum_pow_range
    (D : ℕ) (l : ℕ → ℕ) (hmono : Monotone l) :
    ∀ n, kraft_numerator D l n = ∑ t ∈ Finset.range n, D ^ (l n - l t) := by
  intro n
  induction n with
  | zero =>
      simp [kraft_numerator]
  | succ n ih =>
      -- Notation
      have hln : l n ≤ l (n+1) := hmono (Nat.le_succ n)
      set a : ℕ := l (n+1) - l n

      -- Start from the RHS for `n+1`
      -- split off last term, then factor out `D^a` from the prefix sum
      simp [Finset.sum_range_succ, kraft_numerator, ih]

      -- Goal after simp is essentially:
      --   (∑ t∈range n, D^(l(n+1)-l t)) + D^(l(n+1)-l n)
      -- = ( (∑ t∈range n, D^(l n - l t)) + 1 ) * D^(l(n+1)-l n)

      -- Turn the prefix sum into a factored form
      have hfac :
          (∑ t ∈ Finset.range n, D ^ (l (n+1) - l t))
            = D ^ a * (∑ t ∈ Finset.range n, D ^ (l n - l t)) := by
        -- rewrite each term using exponent arithmetic:
        -- (l(n+1)-l t) = (l(n+1)-l n) + (l n - l t)
        -- then use `pow_add` and pull out `D^a`
        calc
          (∑ t ∈ Finset.range n, D ^ (l (n+1) - l t))
              = ∑ t ∈ Finset.range n, (D ^ a) * (D ^ (l n - l t)) := by
                  refine Finset.sum_congr rfl ?_
                  intro t ht
                  have ht' : t < n := Finset.mem_range.mp ht
                  have hlt : l t ≤ l n := hmono (Nat.le_of_lt_succ (Nat.lt_succ_of_lt ht'))
                  have hlt' : l t ≤ l (n+1) := le_trans hlt hln
                  -- exponent identity
                  have hexp : (l (n+1) - l t) = a + (l n - l t) := by
                    -- `a = l(n+1)-l n`
                    dsimp [a]
                    omega
                  -- finish
                  simp [hexp, pow_add, mul_comm]
          _   = D ^ a * (∑ t ∈ Finset.range n, D ^ (l n - l t)) := by
                  -- pull out constant
                  simp [Finset.mul_sum]

      -- Now finish the `succ` step by rewriting with `hfac`
      -- and using `l(n+1)-l n = a`
      -- also: the last term is exactly `D^a`
      have hlast : D ^ (l (n+1) - l n) = D ^ a := by simp [a]
      -- substitute and algebra
      simp [hfac, hlast, Nat.mul_add, Nat.mul_comm]

/--
Separation property for `A = kraft_numerator D l`:
if `i < j` then you cannot have `A j / D^(l j - l i) = A i` (even assuming `l i ≤ l j`).
-/
lemma kraft_numerator_div_separated_of_lt
    {D : ℕ} {l : ℕ → ℕ} (hD : 1 < D)
    (hmono : Monotone l) :
    ∀ {i j : ℕ}, i < j →
      ¬ (l i ≤ l j ∧ kraft_numerator D l j / D ^ (l j - l i) = kraft_numerator D l i) := by
  intro i j hij
  rintro ⟨hij_len, hdiv⟩

  have hDpos : 0 < D := Nat.zero_lt_of_lt hD
  set A : ℕ → ℕ := kraft_numerator D l
  set d : ℕ := D ^ (l j - l i)
  have hdpos : 0 < d := by
    dsimp [d]
    exact Nat.pow_pos hDpos

  -- Closed forms for A i and A j
  have hAi : A i = ∑ t ∈  Finset.range i, D ^ (l i - l t) := by
    simpa [A] using (kraft_numerator_eq_sum_pow_range D l hmono i)
  have hAj : A j = ∑ t ∈ Finset.range j, D ^ (l j - l t) := by
    simpa [A] using (kraft_numerator_eq_sum_pow_range D l hmono j)

  -- The partial sum up to `i+1` sits inside the sum up to `j`
  have hsub : Finset.range (i+1) ⊆ Finset.range j := by
    -- i+1 ≤ j since i< j
    exact Finset.range_mono (Nat.succ_le_of_lt hij)

  have hle_part :
      (∑ t ∈  Finset.range (i+1), D ^ (l j - l t))
        ≤ (∑ t ∈  Finset.range j, D ^ (l j - l t)) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
    intro x hx _hx'
    exact Nat.zero_le _

  have hle_part' :
      (∑ t ∈  Finset.range (i+1), D ^ (l j - l t)) ≤ A j := by
    simpa [hAj] using hle_part

  -- Rewrite the `range (i+1)` sum as (range i) + last
  have hsplit :
      (∑ t ∈  Finset.range (i+1), D ^ (l j - l t))
        = (∑ t ∈  Finset.range i, D ^ (l j - l t)) + D ^ (l j - l i) := by
    simp [Finset.sum_range_succ]

  -- Show the prefix sum is a multiple of `d` with coefficient `A i`
  have hmul_prefix :
      (∑ t ∈  Finset.range i, D ^ (l j - l t))
        = d * (∑ t ∈  Finset.range i, D ^ (l i - l t)) := by
    -- each term: D^(l j - l t) = D^(l j - l i) * D^(l i - l t)
    -- because l t ≤ l i ≤ l j
    calc
      (∑ t ∈  Finset.range i, D ^ (l j - l t))
          = ∑ t ∈  Finset.range i, d * (D ^ (l i - l t)) := by
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
      _   = d * (∑ t ∈  Finset.range i, D ^ (l i - l t)) := by
              simp [Finset.mul_sum]

  -- Now assemble: sum_{t≤i} = d*(A i + 1)
  have hlower :
      d * (A i + 1) ≤ A j := by
    -- start from hle_part' and rewrite LHS
    -- LHS = (prefix over range i) + d
    -- prefix = d * (sum range i ...)
    -- sum range i ... = A i
    have : (∑ t ∈  Finset.range (i+1), D ^ (l j - l t))
              = d * (A i + 1) := by
      -- rewrite using hsplit, hmul_prefix, hAi
      calc
        (∑ t ∈  Finset.range (i+1), D ^ (l j - l t))
            = (∑ t ∈  Finset.range i, D ^ (l j - l t)) + D ^ (l j - l i) := by
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
lemma kraft_numerator_lt_pow_of_sum_range_lt_one
    (D : ℕ) (hD : 1 < D) (lNat : ℕ → ℕ) (hmono : Monotone lNat)
    {n : ℕ}
    (h_sum_lt1 : (∑ t ∈ Finset.range n, (1 / D : ℝ) ^ lNat t) < 1) :
    kraft_numerator D lNat n < D ^ lNat n := by
  have hD_pos : 0 < D := Nat.zero_lt_of_lt hD
  have hD_pos_real : (0 : ℝ) < D := by exact_mod_cast hD_pos
  have hD_ne : (D : ℝ) ≠ 0 := ne_of_gt hD_pos_real

  have h_eq :
      (kraft_numerator D lNat n : ℝ) / (D : ℝ) ^ lNat n
        = ∑ t ∈ Finset.range n, (1 / D : ℝ) ^ lNat t :=
    kraft_numerator_div_pow_eq_sum (D := D) hD lNat hmono n

  have hden : 0 < (D : ℝ) ^ lNat n := by positivity
  have hdivlt : (kraft_numerator D lNat n : ℝ) / (D : ℝ) ^ lNat n < 1 := by
    simpa [h_eq] using h_sum_lt1

  have hlt_real : (kraft_numerator D lNat n : ℝ) < (D : ℝ) ^ lNat n := by
    -- `a/b < 1` with `0<b` gives `a < b`
    exact (div_lt_one hden).1 hdivlt

  -- cast back to `ℕ`
  exact_mod_cast hlt_real

/-- Helper: for `0 < r`, the partial sum over a proper prefix is strictly increasing. -/
lemma sum_range_succ_lt {r : ℝ} (hr : 0 < r) (lNat : ℕ → ℕ) (n : ℕ) :
    (∑ t ∈ Finset.range n, r ^ lNat t)
      < (∑ t ∈ Finset.range (n+1), r ^ lNat t) := by
  -- `sum_range_succ` gives `S(n+1) = S(n) + r^(lNat n)`, and the added term is positive.
  simp [Finset.sum_range_succ]
  have : 0 < r ^ lNat n := by
    exact pow_pos hr _
  linarith

/-- Helper: if a nonnegative series of length `k` sums to `≤ 1`,
then every proper prefix sum is `< 1`. -/
lemma sum_range_lt_one_of_sum_range_le_one
    {r : ℝ} (hr : 0 < r) {k n : ℕ} (hnk : n < k)
    (lNat : ℕ → ℕ)
    (h_le : (∑ t ∈ Finset.range k, r ^ lNat t) ≤ 1) :
    (∑ t ∈ Finset.range n, r ^ lNat t) < 1 := by
  -- `S(n) < S(n+1) ≤ S(k) ≤ 1`
  have hlt_succ : (∑ t ∈ Finset.range n, r ^ lNat t)
      < (∑ t ∈ Finset.range (n+1), r ^ lNat t) :=
    sum_range_succ_lt (r := r) hr lNat n
  have h_le_succ_k :
      (∑ t ∈ Finset.range (n+1), r ^ lNat t)
        ≤ (∑ t ∈ Finset.range k, r ^ lNat t) := by
    have hsub : Finset.range (n+1) ⊆ Finset.range k :=
      Finset.range_mono (Nat.succ_le_of_lt hnk)
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
    intro _ _ _
    exact le_of_lt (pow_pos hr _)

  have : (∑ t ∈ Finset.range n, r ^ lNat t)
      < (∑ t ∈ Finset.range k, r ^ lNat t) := by
    exact lt_of_lt_of_le hlt_succ (le_trans h_le_succ_k (le_rfl))
  exact lt_of_lt_of_le this h_le

lemma range_eq_Iio (n : ℕ) : (Finset.range n : Finset ℕ) = Finset.Iio n := by
  ext k
  simp [Finset.mem_Iio]  -- gives: k ∈ Iio n ↔ k < n, same as mem_range

/-- Core interval-engine: from monotone lengths + strict prefix Kraft bounds,
construct the integer interval starts `A` with the key separation property. -/
theorem kraft_interval_construction
    (D : ℕ) (hD : 1 < D) (l : ℕ → ℕ)
    (hmono : Monotone l)
    (h_sum_prefix : ∀ n, (∑ k < n, (1 / D : ℝ) ^ l k) < 1) :
    ∃ A : ℕ → ℕ,
      StrictMono A ∧
      (∀ n, A n < D ^ (l n)) ∧
      (∀ i j : ℕ, i < j → A j / D ^ (l j - l i) ≠ A i) := by
  refine ⟨kraft_numerator D l, ?_, ?_, ?_⟩

  · -- StrictMono A
    refine strictMono_nat_of_lt_succ ?_
    intro n
    -- unfold A
    simp [kraft_numerator]
    have hDpos : 0 < D := Nat.zero_lt_of_lt hD
    have hpowpos : 0 < D ^ (l (n + 1) - l n) := Nat.pow_pos hDpos
    -- A n < A n + 1 ≤ (A n + 1) * D^Δ
    exact lt_of_lt_of_le (Nat.lt_add_one _) (Nat.le_mul_of_pos_right _ hpowpos)

  · -- Bound: A n < D^(l n)
    intro n
    have : kraft_numerator D l n < D ^ l n := by
      have h_sum_prefix_range (n : ℕ) :
          (∑ k ∈ Finset.range n, (1 / (D : ℝ)) ^ l k) < 1 := by
        -- just change the finset on the LHS
        simpa [range_eq_Iio n] using h_sum_prefix n

      exact kraft_numerator_lt_pow_of_sum_range_lt_one
        (D := D) (hD := hD) (lNat := l) (hmono := hmono)
        (n := n) (h_sum_lt1 := h_sum_prefix_range n)
    simpa using this

  · -- Separation: no earlier interval is a prefix of a later one (in division form)
    intro i j hij
    have hij_len : l i ≤ l j := hmono (Nat.le_of_lt hij)
    intro hdiv
    have hsep :
        ¬ (l i ≤ l j ∧
            kraft_numerator D l j / D ^ (l j - l i) = kraft_numerator D l i) := by
      exact kraft_numerator_div_separated_of_lt
        (D := D) (hD := hD) (l := l) (hmono := hmono) hij
    exact hsep ⟨hij_len, hdiv⟩

lemma exists_pow_le_of_lt_one {r ε : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hε : 0 < ε) :
  ∃ N, ∀ n ≥ N, r^n < ε := by
  -- from convergence r^n → 0, we get eventually r^n ∈ Iio ε
  have hT := tendsto_pow_atTop_nhds_zero_of_lt_one (𝕜 := ℝ) hr0 hr1
  have hEv : ∀ᶠ n in Filter.atTop, r ^ n < ε := by
    have : Set.Iio ε ∈ nhds (0 : ℝ) := Iio_mem_nhds hε
    exact hT.eventually this
  rcases (Filter.eventually_atTop.1 hEv) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  exact hN n hn

lemma exists_shift_tail_lt
    (r : ℝ) (Llast : ℕ) {k : ℕ} (l : Fin k → ℕ)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (h_sum_lt : (∑ i, r ^ l i) < 1) :
    ∃ s : ℕ, (r ^ (Llast + s + 1)) / (1 - r) < (1 - (∑ i, r ^ l i)) := by
  have hden : 0 < (1 - r) := sub_pos.mpr hr1
  have hδ   : 0 < (1 - (∑ i, r ^ l i)) := sub_pos.mpr h_sum_lt

  -- r = 0 is trivial: tail = 0 and RHS > 0
  by_cases hrzero : r = 0
  · subst hrzero
    refine ⟨0, ?_⟩
    simpa using hδ

  have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hrzero)
  have hrpowpos : 0 < r ^ (Llast + 1) := pow_pos hrpos _
  have hrpowne  : (r ^ (Llast + 1)) ≠ 0 := ne_of_gt hrpowpos

  -- Choose ε so that: r^s < ε ⇒ r^(Llast+s+1) < (1-sum)*(1-r)
  let ε : ℝ := ((1 - (∑ i, r ^ l i)) * (1 - r)) / (r ^ (Llast + 1))
  have hεpos : 0 < ε := by
    have : 0 < (1 - (∑ i, r ^ l i)) * (1 - r) := mul_pos hδ hden
    exact div_pos this hrpowpos

  obtain ⟨s, hs⟩ :
      ∃ N, ∀ n ≥ N, r ^ n < ε :=
    exists_pow_le_of_lt_one (r := r) (ε := ε) hr0 hr1 hεpos
  refine ⟨s, ?_⟩
  have hs0 : r ^ s < ε := hs s (le_rfl)

  have hmul :
      (r ^ (Llast + 1)) * (r ^ s) < (r ^ (Llast + 1)) * ε :=
    mul_lt_mul_of_pos_left hs0 hrpowpos

  have hleft :
      (r ^ (Llast + 1)) * (r ^ s) = r ^ (Llast + s + 1) := by
    calc
      (r ^ (Llast + 1)) * (r ^ s) = r ^ ((Llast + 1) + s) := by
        simp [pow_add, mul_comm, mul_assoc]
      _ = r ^ (Llast + s + 1) := by
        simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

  have hrhs :
      (r ^ (Llast + 1)) * ε = (1 - (∑ i, r ^ l i)) * (1 - r) := by
    set rpow : ℝ := r ^ (Llast + 1)
    set num  : ℝ := (1 - (∑ i, r ^ l i)) * (1 - r)
    have hrpowne' : rpow ≠ 0 := by
      simpa [rpow] using hrpowne
    dsimp [ε, rpow, num]
    -- convert `rpow * (num / rpow)` into `(rpow * num) / rpow`
    calc
      (r ^ (Llast + 1)) * (num / (r ^ (Llast + 1)))
          = ((r ^ (Llast + 1)) * num) / (r ^ (Llast + 1)) := by
              simpa [mul_assoc] using (mul_div_assoc (r ^ (Llast + 1)) num (r ^ (Llast + 1))).symm
      _ = num := by simpa [mul_assoc] using (mul_div_cancel_left₀ num hrpowne')

  have hmain :
      r ^ (Llast + s + 1) < (1 - (∑ i, r ^ l i)) * (1 - r) := by
    simpa [hleft, hrhs] using hmul

  -- Divide by (1-r) > 0
  exact (div_lt_iff₀ hden).2 (by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmain)

lemma exists_shift_tail_le
    (r : ℝ) (Llast : ℕ) {k : ℕ} (l : Fin k → ℕ)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (h_sum_lt : (∑ i, r ^ l i) < 1) :
    ∃ s : ℕ, (r ^ (Llast + s + 1)) / (1 - r) ≤ (1 - (∑ i, r ^ l i)) := by
  rcases exists_shift_tail_lt (r := r) (Llast := Llast) (l := l) hr0 hr1 h_sum_lt with ⟨s, hs⟩
  exact ⟨s, le_of_lt hs⟩

lemma tsum_const_mul_geometric (r c : ℝ) (hr : |r| < 1) :
  (∑' n : ℕ, c * r^n) = c / (1 - r) := by
  simpa [<-tsum_geometric_of_abs_lt_one hr, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    (tsum_mul_left (a := c) (f := fun n : ℕ => r^n))

lemma summable_mul_geometric {r : ℝ} (hr : |r| < 1) (c : ℝ) :
  Summable (fun n : ℕ => c * r^n) := by
  -- geometric is summable, and scalar-multiplying preserves summability
  simpa [mul_assoc] using (summable_geometric_of_abs_lt_one hr).mul_left c

lemma tsum_eq_sum_range_add_tsum_add
    {α : Type _} [NormedAddCommGroup α]
    {k : ℕ}
    {f : ℕ → α} (hs : Summable f) :
    (∑' n, f n) = (Finset.sum (Finset.range k) f) + (∑' n, f (n + k)) := by
  exact (Summable.sum_add_tsum_nat_add (f := f) k hs).symm

lemma abs_one_div_nat_lt_one {D : ℕ} (hD : 1 < D) : |(1 / (D : ℝ))| < 1 := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (Nat.zero_lt_of_lt hD)
  have hD1 : (1 : ℝ) < D := by exact_mod_cast hD
  -- nonneg so abs = id
  have hnonneg : 0 ≤ (1 / (D : ℝ)) := by exact one_div_nonneg.mpr (le_of_lt hDpos)
  rw [abs_of_nonneg hnonneg]
  exact (div_lt_one hDpos).2 hD1

/-- Generalized converse of Kraft's inequality for monotone length sequences indexed by ℕ. -/
theorem kraft_inequality_tight_nat_mono_fin
    (D : ℕ) (hD : 1 < D) (l : ℕ → ℕ) (h_mono : Monotone l)
    (h_summable : Summable (fun i => (1 / D : ℝ) ^ l i))
    (h_sum : ∑' i, (1 / D : ℝ) ^ l i ≤ 1) :
    ∃ w : ℕ → List (Fin D),
      Function.Injective w ∧
      PrefixFree (Set.range w) ∧
      (∀ i, (w i).length = l i) := by
  have hD_pos : 0 < D := Nat.zero_lt_of_lt hD
  have hrpos : (0 : ℝ) < (1 / D : ℝ) :=
    one_div_pos.mpr (by exact_mod_cast hD_pos)

  -- strict prefix bounds from tsum ≤ 1 (your existing block)
  have h_sum_prefix_range :
      ∀ n, (∑ k ∈ Finset.range n, (1 / D : ℝ) ^ l k) < 1 := by
    intro n
    have h_le_tsum :
        (∑ k ∈ Finset.range (n+1), (1 / D : ℝ) ^ l k)
          ≤ ∑' k, (1 / D : ℝ) ^ l k :=
      Summable.sum_le_tsum _ (fun _ _ => by positivity) h_summable
    have h_le_one :
        (∑ k ∈ Finset.range (n+1), (1 / D : ℝ) ^ l k) ≤ 1 :=
      le_trans h_le_tsum h_sum
    exact sum_range_lt_one_of_sum_range_le_one
      (r := (1 / D : ℝ)) hrpos
      (k := n+1) (n := n) (hnk := Nat.lt_succ_self n)
      (lNat := l) h_le_one

  have h_sum_prefix :
      ∀ n, (∑ k ∈ Finset.Iio n, (1 / D : ℝ) ^ l k) < 1 := by
    intro n
    simpa [range_eq_Iio n] using h_sum_prefix_range n

  -- interval engine gives A
  obtain ⟨A, hA_strict, hA_lt, hA_sep⟩ :=
    kraft_interval_construction (D := D) (hD := hD) (l := l) (hmono := h_mono)
      (h_sum_prefix := by
        -- your theorem wants `∑ k < n`, i.e. `Iio`
        intro n
        -- `∑ k < n` is `∑ k ∈ Iio n`
        simpa [Finset.sum_Ico_eq_sum_range] using h_sum_prefix n)

  -- define w directly in Fin D
  let w : ℕ → List (Fin D) := fun n =>
    Digits.natToDigitsBEFin D (A n) (l n) hD

  refine ⟨w, ?_, ?_, ?_⟩

  · -- Injective
    intro n m hnm
    have hlen : l n = l m := by
      have := congrArg List.length hnm
      simpa [w, Digits.natToDigitsBEFin_length] using this
    have hAeq : A n = A m := by
      -- use your Digits lemma for Fin-coded digits
      apply Digits.natToDigitsBEFin_inj hD
      · exact hA_lt n
      · simpa [hlen] using hA_lt m
      · subst w
        ext
        simp_all only
    exact hA_strict.injective hAeq

  · -- PrefixFree
    intro a ha b hb hpre
    rcases ha with ⟨n, rfl⟩
    rcases hb with ⟨m, rfl⟩
    by_cases hnm : n = m
    · subst hnm; rfl
    · have hdiv :
        l n ≤ l m ∧ A m / D ^ (l m - l n) = A n := by
        -- Fin-version of your existing nat lemma
        exact (Digits.natToDigitsBEFin_prefix_iff_div hD (hA_lt n) (hA_lt m)).1 hpre
      rcases lt_or_gt_of_ne hnm with hlt | hgt
      · exact (hA_sep n m hlt) hdiv.2 |>.elim
      · have hlen_le : l m ≤ l n := h_mono (Nat.le_of_lt hgt)
        have hlen_eq : l n = l m := le_antisymm hdiv.1 hlen_le
        have : A m = A n := by
          have : l m - l n = 0 := by simp [hlen_eq]
          simpa [this] using hdiv.2
        have : n = m := hA_strict.injective this.symm
        exact (hnm this).elim

  · -- lengths
    intro i
    simp [w, Digits.natToDigitsBEFin_length]

/-- Sufficient separation condition for prefix-freeness via the `div` characterization. -/
lemma prefixFree_range_natToDigitsBEFin_of_div_separated
    {D : ℕ} {k : ℕ} {l : Fin k → ℕ} {A : ℕ → ℕ}
    (hD : 1 < D)
    (hA_lt : ∀ i : Fin k, A i.val < D ^ l i)
    (hSep :
      ∀ {i j : Fin k}, i ≠ j → ¬
        (l i ≤ l j ∧ A j.val / D ^ (l j - l i) = A i.val)) :
    Kraft.PrefixFree (Set.range (fun i : Fin k => Digits.natToDigitsBEFin  D (A i.val) (l i) (by omega))) := by
  intro a ha b hb hpre
  rcases ha with ⟨i, rfl⟩
  rcases hb with ⟨j, rfl⟩
  by_cases hij : i = j
  · subst hij; rfl
  · -- use the prefix ↔ division lemma
    have hpre' :
        (l i ≤ l j ∧ A j.val / D ^ (l j - l i) = A i.val) := by
      have := (Digits.natToDigitsBEFin_prefix_iff_div
                hD
                (hA_lt i)
                (hA_lt j)).1 hpre
      exact this
    exact (hSep (i := i) (j := j) hij hpre').elim

/-- Finite-index converse with `≤ 1`. -/
lemma kraft_inequality_tight_fin
    (D : ℕ) (hD : 1 < D) {k : ℕ}
    (l : Fin k → ℕ) (h_mono : Monotone l)
    (h_sum : (∑ i, (1 / D : ℝ) ^ l i) ≤ 1) :
    ∃ w : Fin k → List (Fin D),
      Function.Injective w ∧
      PrefixFree (Set.range w) ∧
      ∀ i, (w i).length = l i := by
  by_cases hk : k = 0
  · subst hk
    refine ⟨fun i => Fin.elim0 i, ?_, ?_, ?_⟩
    · intro i
      exact Fin.elim0 i
    · intro a ha b hb hpre
      rcases ha with ⟨i, rfl⟩
      exact Fin.elim0 i
    · intro i
      exact Fin.elim0 i

  -- extend lengths to ℕ (only matters on `< k`)
  let Llast : ℕ := l ⟨k-1, by omega⟩
  let lNat : ℕ → ℕ := ext_shift Llast 0 l
  have hmonoNat : Monotone lNat := ext_shift_monotone k l h_mono hk 0

  let A : ℕ → ℕ := kraft_numerator D lNat

  -- define codewords
  let w : Fin k → List (Fin D) := fun i =>
    Digits.natToDigitsBEFin D (A i.val) (l i) (by omega)

  -- show interval bound `A i < D^(l i)` for each `i : Fin k`
  have hA_lt : ∀ i : Fin k, A i.val < D ^ l i := by
    intro i
    have h_sum_range :
        (∑ t ∈ Finset.range k, (1 / (D : ℝ)) ^ lNat t) ≤ 1 := by
      -- start from the given h_sum as a Fin-sum
      have h_sum_fin : (∑ i : Fin k, (1 / (D : ℝ)) ^ l i) ≤ 1 := by
        simpa using h_sum

      -- rewrite that Fin-sum into the range-sum over lNat
      -- (1) replace l i by lNat i.val
      have h1 :
          (∑ i : Fin k, (1 / (D : ℝ)) ^ l i)
            = (∑ i : Fin k, (1 / (D : ℝ)) ^ lNat i.val) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        -- hi : i ∈ Finset.univ, ignore it
        -- unfold lNat = ext_shift ... and take the < k branch using i.isLt
        simp [lNat, Llast]
      have h2 :
          (∑ i : Fin k, (1 / (D : ℝ)) ^ lNat (i : ℕ))
            = (∑ t ∈ Finset.range k, (1 / (D : ℝ)) ^ lNat t) := by
        -- this is exactly the Nat-function version
        simpa using
          (Fin.sum_univ_eq_sum_range (n := k)
            (f := fun t : ℕ => (1 / (D : ℝ)) ^ lNat t))

      simp_all only [one_div]

    -- for `n = i.val`, we need the strict prefix bound `< 1`
    have hrpos : 0 < (1 / D : ℝ) := by
      exact one_div_pos.mpr (by exact_mod_cast (Nat.zero_lt_of_lt hD))
    have h_pref_lt1 :
        (∑ t ∈ Finset.range i.val, (1 / D : ℝ) ^ lNat t) < 1 := by
      exact sum_range_lt_one_of_sum_range_le_one
        (r := (1 / D : ℝ)) hrpos (k := k) (n := i.val) i.isLt lNat h_sum_range

    -- now convert invariant + `<1` into the Nat bound
    have : kraft_numerator D lNat i.val < D ^ lNat i.val :=
      kraft_numerator_lt_pow_of_sum_range_lt_one (D := D) hD lNat hmonoNat h_pref_lt1

    -- rewrite `lNat i.val = l i` and finish
    simpa [A, lNat, ext_shift_eq (l := l) (Llast := Llast) (s := 0) i] using this

  refine ⟨w, ?_, ?_, ?_⟩

  · -- Injective
    intro i j hij
    apply Fin.ext
    -- first get `A i.val = A j.val` via `natToDigitsBEFin_inj`,
    -- then strictMono injectivity for `A = kraft_numerator ...`.
    have hDpos : 0 < D := Nat.zero_lt_of_lt hD
    have hA_eq : A i.val = A j.val := by
      -- (exactly the pattern you used in the ℕ theorem’s injectivity proof)
      apply Digits.natToDigitsBEFin_inj hD
      · exact hA_lt i
      · -- get equality of widths from `hij` via lengths of `w i` and `w j`
        have hlij : l i = l j := by
          simpa [w] using (congrArg List.length hij)
        -- now rewrite the bound for `j` along `hlij`
        simpa [hlij] using (hA_lt j)
      · -- need the bound for `j` too
        have := congrArg List.length hij
        -- the `inj` lemma typically wants both bounds; provide it
        -- (you can usually discharge it by rewriting lengths and using `hA_lt j`)
        have hlij : l i = l j := by
          -- lengths of `w i` and `w j` are the widths `l i` and `l j`
          have hwi : (w i).length = l i := by simp [w, Digits.natToDigitsBEFin_length]
          have hwj : (w j).length = l j := by simp [w, Digits.natToDigitsBEFin_length]
          -- `this : (w i).length = (w j).length`
          exact by simpa [hwi, hwj] using this

        -- map values to get an equality in `List ℕ`
        have hij_val :
            (w i).map (fun x : Fin D => x.val)
              = (w j).map (fun x : Fin D => x.val) :=
          congrArg (List.map (fun x : Fin D => x.val)) hij

        simp_all only [w]

    -- strict monotonicity of `kraft_numerator` (you already proved this in the ℕ proof)
    have hA_strict : StrictMono A := by
      -- reuse the lemma you had: `StrictMono (kraft_numerator D lNat)`
      -- (its proof doesn’t use summability, only `0 < D`)
      refine strictMono_nat_of_lt_succ ?_
      intro n

      simp_all
      exact lt_of_lt_of_le (Nat.lt_add_one _) (Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega)))

    have : i.val = j.val := hA_strict.injective hA_eq
    exact this

  · -- PrefixFree
    -- package the heavy argument once
    suffices hraw :
      PrefixFree
        (Set.range (fun i : Fin k =>
          Digits.natToDigitsBEFin D (A i.val) (l i) (by omega))) by
      -- convert raw goal back to PrefixFree (Set.range w)`
      simpa [w] using hraw

    refine prefixFree_range_natToDigitsBEFin_of_div_separated hD hA_lt ?_

    intro i j hij
    -- reduce to Nat indices
    -- (1) decide which one is smaller
    rcases lt_trichotomy i.val j.val with hlt | heq | hgt
    · -- i.val < j.val
      -- Here you use the Nat lemma for the generator `A = kraft_numerator D lNat`
      -- specialized to i.val < j.val, then rewrite lNat = l on < k.
      have : ¬ (lNat i.val ≤ lNat j.val ∧ A j.val / D ^ (lNat j.val - lNat i.val) = A i.val) := by
        -- main invariant of kraft_numerator (Nat-indexed separation)
        exact kraft_numerator_div_separated_of_lt
          (D := D) (l := lNat) (hmono := hmonoNat) hD hlt
      -- now rewrite lNat at i.val and j.val into l i and l j
      -- because i.val < k and j.val < k
      simpa [lNat, ext_shift, i.isLt, j.isLt] using this
    · exact (hij (Fin.ext (by simpa using heq))).elim
    · -- i.val > j.val
      -- If l i ≤ l j holds, then (since l is monotone) impossible when i>j
      -- or you can just reduce to the lt-case by symmetry.
      -- simplest: swap roles and use the lt-case lemma, then contradict.
      have hlt' : j.val < i.val := hgt
      have : ¬ (lNat j.val ≤ lNat i.val ∧ A i.val / D ^ (lNat i.val - lNat j.val) = A j.val) := by
        exact kraft_numerator_div_separated_of_lt
          (D := D) (l := lNat) (hmono := hmonoNat) hD hlt'
      -- From the negated swapped statement, get the desired negation by
      -- noticing your target antecedent is “l i ≤ l j ∧ ... = ...”.
      -- This last step is just “not_and_or” reshuffling; do it via `intro h; ...`.
      intro h
      -- h : l i ≤ l j ∧ A j.val / ... = A i.val
      -- turn it into the swapped form using arithmetic + monotonicity;
      -- easiest is to just mark this as a tiny helper.
      apply this

      have hji : j ≤ i :=
        Fin.le_iff_val_le_val.2 (Nat.le_of_lt hgt)

      have h_lj_le_li : l j ≤ l i :=
        h_mono hji

      -- from h.1 : l i ≤ l j and monotonicity : l j ≤ l i
      have h_len_eq : l i = l j :=
        le_antisymm h.1 h_lj_le_li

      -- turn h.2 into A j = A i (because exponent becomes 0)
      have h_Aj_eq_Ai : A (↑j) = A (↑i) := by
        -- h.2 : A ↑j / D^(l j - l i) = A ↑i
        have : l j - l i = 0 := by simp [h_len_eq]
        simpa [this] using h.2

      have h_Ai_eq_Aj : A (↑i) = A (↑j) := h_Aj_eq_Ai.symm

      constructor
      · -- lNat ↑j ≤ lNat ↑i
        -- for indices < k, lNat agrees with l
        simpa [lNat, ext_shift, j.isLt, i.isLt] using h_lj_le_li
      · -- A ↑i / D^(lNat ↑i - lNat ↑j) = A ↑j
        have : lNat (↑i) - lNat (↑j) = 0 := by
          -- again, for < k this reduces to l i - l j, then uses h_len_eq
          simp [lNat, h_len_eq]
        -- now division by D^0 = 1
        simp [this, h_Ai_eq_Aj]-- goal:

  · -- Length preservation
    intro i
    simp [w]

/-- Converse of Kraft's inequality for monotone length sequences, for any finite alphabet.

Given a monotone `l : ℕ → ℕ` with summable Kraft sum ≤ 1 over an alphabet of size `|α| ≥ 2`,
there exists a prefix-free code with the given length function.

Note: Requires `Nontrivial α` (i.e., `|α| ≥ 2`) since prefix-free codes require at least 2 symbols. -/
theorem kraft_inequality_tight_nat_mono_alpha {α : Type _} [DecidableEq α] [Fintype α] [Nontrivial α]
    (l : ℕ → ℕ) (h_mono : Monotone l)
    (h_summable : Summable (fun i => (1 / Fintype.card α : ℝ) ^ l i))
    (h_sum : ∑' i, (1 / Fintype.card α : ℝ) ^ l i ≤ 1) :
    ∃ w : ℕ → List α,
      Function.Injective w ∧
      PrefixFree (Set.range w) ∧
      (∀ i, (w i).length = l i) := by
  have hcard : 1 < Fintype.card α := Fintype.one_lt_card
  -- Get the Fin D version
  obtain ⟨w_fin, h_inj_fin, h_pf_fin, h_len_fin⟩ :=
    kraft_inequality_tight_nat_mono_fin (Fintype.card α) hcard l h_mono h_summable h_sum
  -- Map through the equivalence
  let e := (Fintype.equivFin α).symm
  let w : ℕ → List α := fun n => (w_fin n).map e
  have he_inj : Function.Injective e := Equiv.injective _
  refine ⟨w, ?_, ?_, ?_⟩
  · -- Injectivity
    intro n m hnm
    have : w_fin n = w_fin m := List.map_injective_iff.mpr he_inj hnm
    exact h_inj_fin this
  · -- Prefix-freeness
    intro a ⟨n, qn⟩ b ⟨m, qm⟩ hpre
    subst a b
    have h_pre_fin : w_fin n <+: w_fin m := (List.IsPrefix.map_iff he_inj).mp hpre
    have h_eq_fin : w_fin n = w_fin m :=
      h_pf_fin (w_fin n) ⟨n, rfl⟩ (w_fin m) ⟨m, rfl⟩ h_pre_fin
    simp [w, h_eq_fin]
  · -- Length preservation
    intro i
    simp [w, h_len_fin]

/-- Finite-index converse for arbitrary alphabet with non-strict inequality ≤ 1. -/
lemma kraft_inequality_tight_finite_mono_alpha
    {α : Type _} [Fintype α] [Nontrivial α]
    {k : ℕ} (l : Fin k → ℕ) (h_mono : Monotone l)
    (h_sum : ∑ i, (1 / Fintype.card α : ℝ) ^ l i ≤ 1) :
    ∃ w : Fin k → List α,
      Function.Injective w ∧
      PrefixFree (Set.range w) ∧
      ∀ i, (w i).length = l i := by
  let D : ℕ := Fintype.card α
  have hD' : 1 < D := by
    simpa [D] using (Fintype.one_lt_card_iff_nontrivial.mpr ‹Nontrivial α›)

  -- code over Fin D using the ≤ 1 version
  obtain ⟨wD, hwD_inj, hwD_pf, hwD_len⟩ :=
    kraft_inequality_tight_fin
      (D := D) (hD := hD') (l := l) h_mono (by simpa [D] using h_sum)

  -- transport alphabet Fin D -> α
  let e : Fin D ≃ α := (Fintype.equivFin α).symm
  let w : Fin k → List α := fun i => (wD i).map e

  refine ⟨w, ?_, ?_, ?_⟩

  · -- injective
    intro i j hij
    apply hwD_inj
    have hij' : List.map e.symm (w i) = List.map e.symm (w j) :=
      congrArg (List.map e.symm) hij
    simpa [w, List.map_map, Function.comp] using hij'

  · -- prefixfree
    intro a ha b hb hpre
    rcases ha with ⟨i, rfl⟩
    rcases hb with ⟨j, rfl⟩
    have hpre' : wD i <+: wD j := by
      simpa [w] using (List.IsPrefix.map_iff e.injective).1 hpre
    have : wD i = wD j :=
      hwD_pf (wD i) ⟨i, rfl⟩ (wD j) ⟨j, rfl⟩ hpre'
    have : i = j := hwD_inj this
    subst this
    rfl

  · -- lengths
    intro i
    simp [w, hwD_len i]

/-- A strict total order on indices: first by length, then by an auxiliary embedding.

This is used to enumerate elements in an order that makes the length function monotone. -/
def KraftOrder {I : Type _} (l : I → ℕ) (e : I ↪ ℕ) (i j : I) : Prop :=
  Prod.Lex (· < ·) (· < ·) (l i, e i) (l j, e j)

/-- `KraftOrder` is equivalent to: `l i < l j` or (`l i = l j` and `e i < e j`). -/
lemma KraftOrder_iff {I : Type _} {l : I → ℕ} {e : I ↪ ℕ} {i j : I} :
    KraftOrder l e i j ↔ l i < l j ∨ (l i = l j ∧ e i < e j) :=
  Prod.lex_iff

/-- `KraftOrder` is a strict total order. -/
lemma KraftOrder_isStrictTotalOrder {I : Type _} (l : I → ℕ) (e : I ↪ ℕ) :
    IsStrictTotalOrder I (KraftOrder l e) where
  trichotomous a b := by
    simp only [KraftOrder_iff]
    rcases lt_trichotomy (l a) (l b) with h | h | h
    · exact Or.inl (Or.inl h)
    · rcases lt_trichotomy (e a) (e b) with h' | h' | h'
      · left; right
        exact ⟨h, h'⟩
      · right; left
        exact e.injective h'
      · right; right; right
        exact ⟨h.symm, h'⟩
    · exact Or.inr (Or.inr (Or.inl h))
  irrefl a h := by
    simp only [KraftOrder_iff] at h
    rcases h with h | ⟨_, h⟩ <;> exact lt_irrefl _ h
  trans a b c hab hbc := by
    simp only [KraftOrder_iff] at *
    rcases hab with hab | ⟨hab, hab'⟩ <;> rcases hbc with hbc | ⟨hbc, hbc'⟩
    · exact Or.inl (lt_trans hab hbc)
    · left
      rw [<-hbc] at *
      exact hab
    · left
      rw [<-hab] at *
      exact hbc
    · right
      rw [<-hab] at *
      exact ⟨hbc, lt_trans hab' hbc'⟩

/-- Initial segments of `KraftOrder` are finite when length fibers are finite.

Since each length has only finitely many indices (by summability), the set of
indices smaller than any given index is finite. -/
lemma KraftOrder_finite_initial_segment {I : Type _} (l : I → ℕ) (e : I ↪ ℕ)
    (h_finite : ∀ k, {i | l i = k}.Finite) (i : I) :
    {j | KraftOrder l e j i}.Finite := by
  have h_subset : {j | KraftOrder l e j i} ⊆ {j | l j < l i} ∪ {j | l j = l i} := by
    intro j hj
    simp only [KraftOrder_iff] at hj
    rcases hj with h | ⟨h, _⟩ <;> simp [h]
  refine Set.Finite.subset ?_ h_subset
  apply Set.Finite.union
  · -- Case 1: Strictly smaller lengths
    -- We rewrite the set of elements with smaller length as a bounded Union of fibers
    have h_decomp : {j | l j < l i} = ⋃ k ∈ Finset.range (l i), {j | l j = k} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_range]
      constructor
      · intro h
        use (l x)
      · intro ⟨k, hk_lt, hk_eq⟩; rw [hk_eq]; exact hk_lt
    rw [h_decomp]
    -- A finite union of finite sets is finite
    apply Set.Finite.biUnion
    · exact (Finset.range (l i)).finite_toSet
    · intro _ _
      apply h_finite
  · -- Case 2: Equal length
    exact h_finite (l i)

/-- The rank of an element is the number of elements strictly smaller in `KraftOrder`.

This gives a bijection between `I` and `ℕ` that makes `l` monotone. -/
noncomputable def kraftRank {I : Type _} (l : I → ℕ) (e : I ↪ ℕ)
    (h_finite : ∀ k, {i | l i = k}.Finite) (i : I) : ℕ :=
  (KraftOrder_finite_initial_segment l e h_finite i).toFinset.card

/-- `kraftRank` is strictly monotone with respect to `KraftOrder`. -/
lemma kraftRank_lt_of_KraftOrder {I : Type _} (l : I → ℕ) (e : I ↪ ℕ)
    (h_finite : ∀ k, {i | l i = k}.Finite) {i j : I} (h : KraftOrder l e i j) :
    kraftRank l e h_finite i < kraftRank l e h_finite j := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · -- Subset: {x | x < i} ⊆ {x | x < j} by transitivity
    intro x
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    intro h
    exact (KraftOrder_isStrictTotalOrder l e).trans x i j h (by assumption)
  · -- Strictness: i ∈ {x | x < j} but i ∉ {x | x < i}
    simp only [ne_eq, Finset.ext_iff, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_forall]
    use i
    intro hm
    rw [<-hm] at h
    unfold KraftOrder at h
    simp_all only [KraftOrder, true_iff, Prod.lex_def]
    omega

/-- `kraftRank` is surjective onto ℕ when `I` is infinite. -/
lemma kraftRank_surjective {I : Type _} [Infinite I] (l : I → ℕ) (e : I ↪ ℕ)
    (h_finite : ∀ k, {i | l i = k}.Finite) :
    Function.Surjective (kraftRank l e h_finite) := by
  have hsto := KraftOrder_isStrictTotalOrder l e
  -- kraftRank is injective (distinct elements have distinct ranks)
  have h_inj : Function.Injective (kraftRank l e h_finite) := by
    intro i j hij
    rcases hsto.trichotomous i j with h | rfl | h
    · exact absurd hij (Nat.ne_of_lt (kraftRank_lt_of_KraftOrder l e h_finite h))
    · rfl
    · exact absurd hij (Nat.ne_of_gt (kraftRank_lt_of_KraftOrder l e h_finite h))
  -- The range is an initial segment: if n is in range, so is every m < n
  have h_initial : ∀ n, (∃ i, kraftRank l e h_finite i = n) → ∀ m < n, ∃ i, kraftRank l e h_finite i = m := by
    intro n ⟨i, hi⟩ m hm
    -- The image of {j | j < i} under kraftRank is exactly {0, ..., n-1}
    have h_image : Finset.image (kraftRank l e h_finite)
        (KraftOrder_finite_initial_segment l e h_finite i).toFinset = Finset.range n := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        simp only [Finset.mem_image, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx
        obtain ⟨j, hj, rfl⟩ := hx
        exact Finset.mem_range.mpr (hi ▸ kraftRank_lt_of_KraftOrder l e h_finite hj)
      · rw [Finset.card_range, Finset.card_image_of_injective _ (fun _ _ => by
          intro a
          subst hi
          apply h_inj
          simp_all only)]
        simp_all only [kraftRank, le_refl]
    have hi := Finset.ext_iff.mp h_image m
    simp only [Finset.mem_image, Set.Finite.mem_toFinset, Set.mem_setOf_eq,
               Finset.mem_range, hm, iff_true] at hi
    obtain ⟨a, ⟨_, hl⟩⟩ := hi
    use a
  -- The range is infinite (since I is infinite and kraftRank is injective)
  have h_infinite : Set.Infinite (Set.range (kraftRank l e h_finite)) :=
    Set.infinite_range_of_injective h_inj
  -- An infinite initial segment of ℕ is all of ℕ
  rw [Set.infinite_iff_exists_gt] at h_infinite
  intro n
  obtain ⟨val_i, ⟨⟨witness_i, h_rank_eq⟩, h_n_lt_i⟩⟩ := h_infinite n
  -- We found a value `val_i` (witnessed by `witness_i`) such that `n < val_i`.
  -- Since the range is an initial segment, `n` must also be in the range.
  exact h_initial val_i ⟨witness_i, h_rank_eq⟩ n h_n_lt_i

/-- `kraftRank` is injective (distinct elements have distinct ranks). -/
lemma kraftRank_injective {I : Type _} (l : I → ℕ) (e : I ↪ ℕ)
    (h_finite : ∀ k, {i | l i = k}.Finite) :
    Function.Injective (kraftRank l e h_finite) := by
  intro i j hij
  rcases (KraftOrder_isStrictTotalOrder l e).trichotomous i j with h | rfl | h
  · exact absurd hij (Nat.ne_of_lt (kraftRank_lt_of_KraftOrder l e h_finite h))
  · rfl
  · exact absurd hij (Nat.ne_of_gt (kraftRank_lt_of_KraftOrder l e h_finite h))

/-- An infinite index type with summable Kraft sum can be reordered to make lengths monotone.

This reduces the infinite case to the monotone case by using `kraftRank` to enumerate
elements in increasing order of length.

Generalized to any base D > 1. -/
lemma exists_equiv_nat_monotone_of_infinite {I : Type _} [Infinite I] (D : ℕ) (hD : 1 < D) (l : I → ℕ)
    (h_summable : Summable (fun i => (1 / D : ℝ) ^ l i)) :
    ∃ e : ℕ ≃ I, Monotone (l ∘ e) := by
      have hD_pos : 0 < D := Nat.zero_lt_of_lt hD
      have h_countable : Countable I := by
        have := h_summable.countable_support
        simp only [one_div, Function.support, ne_eq, inv_eq_zero, pow_eq_zero_iff',
                   Nat.cast_eq_zero, Nat.pos_iff_ne_zero.mp hD_pos, false_and, not_false_eq_true] at this
        exact Set.countable_univ_iff.mp this
      -- Let `e = Encodable.encode`.
      obtain ⟨e, he⟩ : ∃ e : I ↪ ℕ, True := by
        simp
        exact countable_iff_nonempty_embedding.mp h_countable
      have h_finite : ∀ k, {i : I | l i = k}.Finite := by
        intro k
        -- f i := (1/D)^l i tends to 0 along cofinite, so eventually f i < (1/D)^k
        have hEv : ∀ᶠ i in Filter.cofinite, (1 / D : ℝ) ^ l i < (1 / D : ℝ) ^ k := by
          have hT := h_summable.tendsto_cofinite_zero
          have hnhds : Set.Iio ((1 / D : ℝ) ^ k) ∈ nhds (0 : ℝ) := by
            exact Iio_mem_nhds (by positivity)
          exact hT.eventually hnhds

        -- hence the “bad set” where ¬(f i < (1/D)^k) is finite
        have hbad :
            {i : I | ¬ ((1 / D : ℝ) ^ l i < (1 / D : ℝ) ^ k)}.Finite := by
          -- depending on imports, this is either `.1` or `mp`
          exact (Filter.eventually_cofinite.1 hEv)

        -- and {i | l i = k} ⊆ bad-set, because it would be ¬(a < a)
        refine hbad.subset ?_
        intro x hx
        -- goal: ¬ ((1/D)^l x < (1/D)^k)
        -- rewrite hx : l x = k, then use lt_irrefl
        simp_all only [not_lt, Set.mem_setOf_eq, le_refl]

      -- By definition of `kraftRank`, we know that `kraftRank` is a bijection between `I` and `ℕ`.
      have h_bij : Function.Bijective (kraftRank l e h_finite) := by
        exact ⟨ kraftRank_injective l e h_finite, kraftRank_surjective l e h_finite ⟩
      obtain ⟨e_iso, he_iso⟩ : ∃ e_iso : ℕ ≃ I, ∀ n, kraftRank l e h_finite (e_iso n) = n := by
        exact ⟨ Equiv.symm (Equiv.ofBijective _ h_bij), fun n => Equiv.apply_symm_apply (Equiv.ofBijective _ h_bij) n ⟩
      refine ⟨e_iso, fun n m hnm => ?_⟩
      contrapose! hnm
      have := kraftRank_lt_of_KraftOrder l e h_finite (KraftOrder_iff.mpr (Or.inl hnm))
      simp_all only

/-- Any finite type can be sorted by a function to ℕ.

Given a fintype `I` and a function `l : I → ℕ`, produces an equivalence
`e : Fin (card I) ≃ I` such that `l ∘ e` is monotone (i.e., maps increasing
indices to non-decreasing length values). Uses insertion sort internally. -/
lemma exists_equiv_fin_monotone {I : Type _} [Fintype I] (l : I → ℕ) :
    ∃ e : Fin (Fintype.card I) ≃ I, Monotone (l ∘ e) := by
  -- sort relation by length
  let r : I → I → Prop := fun x y => l x ≤ l y
  have r_total : IsTotal I r := ⟨fun x y => le_total _ _⟩
  have r_trans : IsTrans I r := ⟨fun _ _ _ => le_trans⟩

  -- start from the canonical list of all elements
  let xs : List I := (Finset.univ : Finset I).toList
  have xs_nodup : xs.Nodup := Finset.nodup_toList (Finset.univ : Finset I)
  have xs_len : xs.length = Fintype.card I := by simp [xs]

  -- insertionSort it
  let ys : List I := xs.insertionSort r
  have ys_pairwise : ys.Pairwise r := by
    -- `pairwise_insertionSort` needs total+trans packaged as instances
    convert (List.pairwise_insertionSort r xs)
  have ys_len : ys.length = Fintype.card I := by simp [ys, xs_len]
  have ys_nodup : ys.Nodup := by
    -- perm preserves nodup
    exact (List.Perm.nodup_iff (List.perm_insertionSort r (l := xs))).2 xs_nodup

  -- the "indexing function" into the sorted list
  let f : Fin ys.length → I := fun i => ys.get i
  have hf_inj : Function.Injective f := by
    -- nodup ↔ get is injective
    exact (List.nodup_iff_injective_get).1 ys_nodup

  -- injective + same finite card ⇒ bijective
  have hf_bij : Function.Bijective f := by
    refine (Fintype.bijective_iff_injective_and_card f).2 ?_
    refine ⟨hf_inj, ?_⟩
    -- card (Fin ys.length) = ys.length = card I
    simp [Fintype.card_fin, ys_len]

  let e0 : Fin ys.length ≃ I := Equiv.ofBijective f hf_bij
  -- cast domain from `Fin (card I)` to `Fin ys.length`
  have hcast : Fintype.card I = ys.length := by simp [ys_len]
  let cast : Fin (Fintype.card I) ≃ Fin ys.length := Fin.castOrderIso hcast

  let e : Fin (Fintype.card I) ≃ I := cast.trans e0
  refine ⟨e, ?_⟩

  -- monotone: i ≤ j ⇒ l(e i) ≤ l(e j)
  intro i j hij
  have hij' : (cast i) ≤ (cast j) := by simpa [cast] using hij
  rcases lt_or_eq_of_le hij' with hlt | heq
  · -- strict case: use pairwise_iff_get
    have hget :
        l (ys.get (cast i)) ≤ l (ys.get (cast j)) := by
      have hPW := List.pairwise_iff_get.1 ys_pairwise
      exact hPW (cast i) (cast j) hlt
    -- unfold e = cast.trans e0, and e0 is built from `f = get`
    simpa [e, cast, e0, Equiv.ofBijective, f] using hget
  · -- equal indices
    simp [e, heq]

variable {α : Type _} [DecidableEq α] [Fintype α] [Nontrivial α]

/-- **Converse of Kraft's Inequality** (general alphabet, any index set).

For any index set `I` (finite or infinite), any finite alphabet `α` with `|α| ≥ 2`,
and length function `l : I → ℕ`, if `∑' i, |α|^{-l(i)} ≤ 1`, then there exists an
injective prefix-free code `w : I → List α` with the prescribed lengths.

Requires `Nontrivial α` (i.e., `|α| ≥ 2`) since prefix-free codes need at least 2 symbols. -/
theorem kraft_inequality_tight_infinite_alpha
    {I : Type _} (l : I → ℕ)
    (h_summable : Summable (fun i ↦ (1 / Fintype.card α : ℝ) ^ l i))
    (h_sum : ∑' i, (1 / Fintype.card α : ℝ) ^ l i ≤ 1) :
    ∃ w : I → List α,
      Function.Injective w ∧
      PrefixFree (Set.range w) ∧
      ∀ i, (w i).length = l i := by
  let D := Fintype.card α
  have hcard : 1 < D := Fintype.one_lt_card
  by_cases h_finite : Finite I
  · haveI := Fintype.ofFinite I
    -- By `exists_equiv_fin_monotone`, there exists an equivalence `e : Fin (card I) ≃ I` such that `l ∘ e` is monotone.
    obtain ⟨e, he⟩ : ∃ e : Fin (Fintype.card I) ≃ I, Monotone (l ∘ e) :=
      exists_equiv_fin_monotone l
    -- By `kraft_inequality_tight_finite_mono_alpha`, there exists `w' : Fin (card I) → List α`
    obtain ⟨w', hw'_inj, hw'_pf, hw'_len⟩ := kraft_inequality_tight_finite_mono_alpha
      (fun i ↦ l (e i)) he (by
        convert h_sum using 1
        rw [tsum_fintype, ← Equiv.sum_comp e]
      )
    refine ⟨w' ∘ e.symm, ?_, ?_, ?_⟩
    · exact hw'_inj.comp e.symm.injective
    · simp only [EquivLike.range_comp]
      exact hw'_pf
    · intro i
      simp [hw'_len]
  · have h_equiv : ∃ e : ℕ ≃ I, Monotone (l ∘ e) := by
      have h_inf : Infinite I := not_finite_iff_infinite.mp h_finite
      exact exists_equiv_nat_monotone_of_infinite D hcard l h_summable
    obtain ⟨e, he⟩ := h_equiv
    have h_sum' : ∑' i : ℕ, (1 / D : ℝ) ^ l (e i) ≤ 1 := by
      convert h_sum using 1
      conv_rhs => rw [← Equiv.tsum_eq e]
    have h_summable' : Summable (fun i : ℕ => (1 / D : ℝ) ^ l (e i)) :=
      h_summable.comp_injective e.injective
    obtain ⟨w, hw_inj, hw_pf, hw_len⟩ :=
      kraft_inequality_tight_nat_mono_alpha (fun i ↦ l (e i)) he h_summable' h_sum'
    refine ⟨fun i => w (e.symm i), ?_, ?_, ?_⟩
    · exact hw_inj.comp e.symm.injective
    · intro x hx y hy hxy
      obtain ⟨i, rfl⟩ := hx
      obtain ⟨j, rfl⟩ := hy
      exact hw_pf (w (e.symm i)) ⟨e.symm i, rfl⟩ (w (e.symm j)) ⟨e.symm j, rfl⟩ hxy
    · intro i
      simp [hw_len]

/-- **Converse of Kraft's Inequality** (General Arity).

For any index set `I` (finite or infinite), any arity `D > 1`, and any embedding `ι` of `Fin D` into `α`,
if `∑ D^{-l i} ≤ 1`, then there exists an injective prefix-free code `w : I → List α`. -/
theorem kraft_tight_of_arity
  (D : ℕ) (hD : 1 < D)
  {α : Type _} (ι : Fin D ↪ α)
  {I : Type _} (l : I → ℕ)
  (h_summable : Summable (fun i => (1 / D : ℝ) ^ l i))
  (h_sum : ∑' i, (1 / D : ℝ) ^ l i ≤ 1) :
  ∃ w : I → List α,
    Function.Injective w ∧
    PrefixFree (Set.range w) ∧
    ∀ i, (w i).length = l i := by

  -- We construct a code w_D over Fin D first
  obtain ⟨w_D, hw_inj, hw_pf, hw_len⟩ : ∃ w : I → List (Fin D), Function.Injective w ∧ PrefixFree (Set.range w) ∧ ∀ i, (w i).length = l i := by
    by_cases h_finite : Finite I
    · -- Case 1: Finite I
      haveI := Fintype.ofFinite I
      obtain ⟨e, he_mono⟩ := exists_equiv_fin_monotone l
      have h_sum_fin : ∑ i : Fin (Fintype.card I), (1 / D : ℝ) ^ l (e i) ≤ 1 := by
        convert h_sum using 1
        rw [tsum_fintype, ← Equiv.sum_comp e]
      obtain ⟨w_fin, h1, h2, h3⟩ := kraft_inequality_tight_fin D hD (l ∘ e) he_mono h_sum_fin
      refine ⟨fun i => w_fin (e.symm i), ?_, ?_, ?_⟩
      · intro x y h; apply e.symm.injective; apply h1; assumption
      · intro a ha b hb; simp only [Set.mem_range] at ha hb
        obtain ⟨x, rfl⟩ := ha; obtain ⟨y, rfl⟩ := hb; apply h2; simp; simp
      · intro i; simp [h3]

    · -- Case 2: Infinite I
      haveI : Infinite I := not_finite_iff_infinite.mp h_finite
      obtain ⟨e, he_mono⟩ := exists_equiv_nat_monotone_of_infinite D hD l h_summable
      have h_sum_nat : ∑' i : ℕ, (1 / D : ℝ) ^ l (e i) ≤ 1 := by
         convert h_sum
         rw [<-Equiv.tsum_eq e]
      obtain ⟨w_fin, h1, h2, h3⟩ := kraft_inequality_tight_nat_mono_fin D hD (l ∘ e) he_mono (h_summable.comp_injective e.injective) h_sum_nat
      refine ⟨fun i => w_fin (e.symm i), ?_, ?_, ?_⟩
      · intro x y h; apply e.symm.injective; apply h1; assumption
      · intro a ha b hb; simp only [Set.mem_range] at ha hb
        obtain ⟨x, rfl⟩ := ha
        obtain ⟨y, rfl⟩ := hb
        apply h2 <;> simp
      · intro i
        simp [h3]

  -- Embed List (Fin D) into List α
  refine ⟨fun i => (w_D i).map ι, ?_, ?_, ?_⟩
  · intro x y h; apply hw_inj; apply List.map_injective_iff.mpr ι.injective h
  · intro a ha b hb hpre
    obtain ⟨x, rfl⟩ := ha; obtain ⟨y, rfl⟩ := hb
    rw [List.IsPrefix.map_iff ι.injective] at hpre
    exact congrArg (List.map ι) (hw_pf (w_D x) ⟨x, rfl⟩ (w_D y) ⟨y, rfl⟩ hpre)
  · intro i; simp [hw_len]

/-- **Converse of Kraft's Inequality** (infinite case).

For any index set `I` (finite or infinite) and length function `l : I → ℕ`,
if `∑' i, 2^{-l(i)} ≤ 1`, then there exists an injective prefix-free code
`w : I → List Bool` with the prescribed lengths.

The proof handles two cases:
- **Finite case**: Sort indices by length and apply `kraft_inequality_tight_finite_mono`
- **Infinite case**: Use equivalence with ℕ and apply `kraft_inequality_tight_nat_mono` -/
theorem kraft_inequality_tight_infinite {I : Type _} (l : I → ℕ)
    (h_summable : Summable (fun i ↦ (1 / 2 : ℝ) ^ l i))
    (h_sum : ∑' i, (1 / 2 : ℝ) ^ l i ≤ 1) :
    ∃ w : I → List Bool,
      Function.Injective w ∧
      PrefixFree (Set.range w) ∧
      ∀ i, (w i).length = l i := by
  -- an injection Fin 2 ↪ Bool
  let ι : Fin 2 ↪ Bool :=
  { toFun := (Fintype.equivFin Bool).symm
    inj'  := (Fintype.equivFin Bool).symm.injective }

  -- now specialize
  simpa using
    (kraft_tight_of_arity (D := 2) (hD := by decide) (α := Bool) ι
      (I := I) (l := l)
      (h_summable := h_summable) (h_sum := h_sum))

end Kraft
