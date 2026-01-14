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
import Kraft.ExtShift
import Kraft.KraftOrder
import Kraft.McMillan

/-!
# Constructive converses of Kraft's inequality: which lemma for which situation?

This file contains several constructive “converse Kraft” statements that look similar but
are *not* simple corollaries of each other. The differences come from two independent axes:

1. **Index type**: finite (`Fin k`) vs infinite (`ℕ`).
2. **Strength of the Kraft bound**: strict (`< 1`) vs non-strict (`≤ 1`).

In all cases the goal is to construct a code `w` with prescribed lengths that is
injective and prefix-free.

We keep multiple versions because the “obvious” reductions between them fail at the
boundary cases (especially when the Kraft sum is exactly `1`), and because the
infinite case needs analytic hypotheses (summability / `tsum`) that are irrelevant
in the finite case.

---

## A. The combinatorial core: strict prefix bounds

The *construction engine* works from **strict prefix bounds**:

*Given monotone lengths `l : ℕ → ℕ` and the property*
`∀ n, (∑ k < n, (1/D)^(l k)) < 1`,
*we build integer interval starts `A` and then define codewords by base-`D` digits of `A n`
with width `l n`.*

This yields a code `w : ℕ → List (Fin D)` that is injective and prefix-free, with
`length (w n) = l n`.

This “strict prefix” statement is the right abstraction boundary: it isolates the
interval/digits argument from any analytic reasoning about infinite series.

---

## B. Infinite index (`ℕ`): non-strict `tsum ≤ 1` implies strict prefixes

For `l : ℕ → ℕ`, the hypothesis we naturally get is a statement about an infinite series:
`Summable (fun n => (1/D)^(l n))` and `∑' n, (1/D)^(l n) ≤ 1`.

From this we can prove strict prefix bounds:
every finite prefix sum is `< 1`. Intuitively, if some prefix were `≥ 1` then adding
a positive term would push it beyond `1`, contradicting the global bound.

So the infinite “non-strict” theorem is cleanly proved as:

`(Summable + tsum ≤ 1)  ⇒  (strict prefix bounds)  ⇒  (core construction)`

This is `kraft_converse_nat_mono_tight`.

Why we keep this theorem:
- It matches the common analytic formulation (“Kraft sum ≤ 1”).
- It is the right tool when you truly have infinitely many indices.

---

## C. Finite index (`Fin k`): non-strict `∑ ≤ 1` does *not* reduce to the infinite theorem

For `l : Fin k → ℕ`, we want a code for exactly `k` words. Here we can assume only the
finite sum bound `∑ i, (1/D)^(l i) ≤ 1`, with *no* summability issues.

A tempting idea is to reduce the finite theorem to the infinite theorem by extending
`l` to `lNat : ℕ → ℕ` with a long tail of huge lengths, and then applying the infinite theorem,
finally restricting the resulting `w : ℕ → _` back to `Fin k`.

This works **only when there is strict slack**: when the finite sum is `< 1`,
we can choose the tail so small that the total still stays `≤ 1`.

However, when the finite sum is *exactly* `1` (the “tight” boundary case),
**no positive tail can be added while preserving `tsum ≤ 1`** (for `D > 1`,
the tail terms are positive, so any infinite tail increases the total beyond `1`).
Therefore:

- The finite theorem with `≤ 1` cannot, in general, be obtained as a corollary of the
  infinite theorem stated with `tsum ≤ 1`, because the reduction would require
  an extension with zero tail contribution, which is impossible.

This is the main reason we keep a *direct* finite proof for `≤ 1`
(`kraft_converse_fin_mono_tight`) rather than forcing a reduction through the infinite theorem.

---

## D. Finite index (`Fin k`): strict `< 1` *does* reduce to the infinite theorem

If we strengthen the finite hypothesis to `∑ i, (1/D)^(l i) < 1`, then the reduction
to `ℕ` becomes straightforward: extend `l` to `ℕ` with a geometric tail whose total
mass is at most the remaining slack, apply the infinite theorem, then restrict back.

So we conceptually have two finite statements:
- a “slack” version (`< 1`), which reduces cleanly to the infinite theorem;
- a “tight” version (`≤ 1`), which requires a direct finite argument.

We keep `≤ 1` because it is the natural sharp statement in the finite case, and it
captures the boundary case of exact Kraft equality.

---

## Summary: which lemma to use?

- **Need a code for `ℕ` indices, and you have an infinite-series hypothesis**:
  use `kraft_converse_nat_mono_tight` (proved via strict prefixes + core construction).

- **Need a code for `Fin k` indices with only `∑ ≤ 1`**:
  use the direct finite theorem `kraft_converse_fin_mono_tight` (no reduction via `ℕ` in general).

- **If you happen to have strict slack `∑ < 1` in the finite case**:
  you can optionally reduce through the `ℕ` theorem (tail-budget construction),
  but this is not the “tight” boundary lemma.

Even though these theorems are conceptually related, keeping them separate reflects the
real logical distinctions at the boundary `= 1` and avoids forcing unnatural analytic
assumptions into the finite setting.
-/

namespace Kraft

open scoped BigOperators Real
open Nat

section DigitPlumbing

/-- Sufficient separation condition for prefix-freeness via the `div` characterization. -/
private lemma Digits.prefixFree_range_natToDigitsBE_of_div_separated
    {D : ℕ} {k : ℕ} {l : Fin k → ℕ} {A : ℕ → ℕ}
    (hD : 1 < D)
    (hA_lt : ∀ i : Fin k, A i.val < D ^ l i)
    (hSep :
      ∀ {i j : Fin k}, i ≠ j → ¬
        (l i ≤ l j ∧ A j.val / D ^ (l j - l i) = A i.val)) :
    Kraft.PrefixFree (Set.range (fun i : Fin k => Digits.natToDigitsBE D (A i.val) (l i) (by omega))) := by
  intro a ha b hb hpre
  rcases ha with ⟨i, rfl⟩
  rcases hb with ⟨j, rfl⟩
  by_cases hij : i = j
  · subst hij; rfl
  · -- use the prefix ↔ division lemma
    have hpre' :
        (l i ≤ l j ∧ A j.val / D ^ (l j - l i) = A i.val) := by
      have := (Digits.natToDigitsBE_prefix_iff_div
                hD
                (hA_lt i)
                (hA_lt j)).1 hpre
      exact this
    exact (hSep (i := i) (j := j) hij hpre').elim

end DigitPlumbing

private lemma range_eq_Iio (n : ℕ) : (Finset.range n : Finset ℕ) = Finset.Iio n := by
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


/-- from monotone lengths + *strict* Kraft bounds on every prefix,
build an injective prefix-free code with the given lengths. -/
theorem kraft_converse_nat_mono_prefix_lt_one_fin
    (D : ℕ) (hD : 1 < D)
    (l : ℕ → ℕ) (h_mono : Monotone l)
    (h_prefix : ∀ n, (∑ k < n, (1 / D : ℝ) ^ l k) < 1) :
    ∃ w : ℕ → List (Fin D),
      Function.Injective w ∧
      PrefixFree (Set.range w) ∧
      (∀ i, (w i).length = l i) := by
  -- interval engine gives A
  obtain ⟨A, hA_strict, hA_lt, hA_sep⟩ :=
    kraft_interval_construction
      (D := D) (hD := hD) (l := l) (hmono := h_mono)
      (h_sum_prefix := h_prefix)

  -- define w directly in Fin D
  let w : ℕ → List (Fin D) := fun n =>
    Digits.natToDigitsBE D (A n) (l n) hD

  refine ⟨w, ?_, ?_, ?_⟩

  · -- Injective
    intro n m hnm
    have hlen : l n = l m := by
      have := congrArg List.length hnm
      simpa [w, Digits.natToDigitsBE_length] using this
    have hAeq : A n = A m := by
      -- use your Digits lemma for Fin-coded digits
      apply Digits.natToDigitsBE_inj hD
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
        -- prefix ↔ division characterization for BE digits
        exact (Digits.natToDigitsBE_prefix_iff_div hD (hA_lt n) (hA_lt m)).1 hpre
      rcases lt_or_gt_of_ne hnm with hlt | hgt
      · -- n < m contradicts separation
        exact (hA_sep n m hlt) hdiv.2 |>.elim
      · -- n > m: show lengths equal and hence A n = A m, contradict StrictMono
        have hlen_le : l m ≤ l n := h_mono (Nat.le_of_lt hgt)
        have hlen_eq : l n = l m := le_antisymm hdiv.1 hlen_le
        have hAeq : A m = A n := by
          have : l m - l n = 0 := by simp [hlen_eq]
          simpa [this] using hdiv.2
        have : n = m := hA_strict.injective hAeq.symm
        exact (hnm this).elim

  · -- lengths
    intro i
    simp [w, Digits.natToDigitsBE_length]

theorem kraft_converse_nat_mono_tight
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

  -- strict prefix bounds from tsum ≤ 1
  have h_prefix : ∀ n, (∑ k < n, (1 / D : ℝ) ^ l k) < 1 := by
    intro n
    have h_le_tsum :
        (∑ k ∈ Finset.range (n+1), (1 / D : ℝ) ^ l k)
          ≤ ∑' k, (1 / D : ℝ) ^ l k :=
      Summable.sum_le_tsum _ (fun _ _ => by positivity) h_summable
    have h_le_one :
        (∑ k ∈ Finset.range (n+1), (1 / D : ℝ) ^ l k) ≤ 1 :=
      le_trans h_le_tsum h_sum
    -- convert the goal `∑ k < n` to a `range` prefix and use your helper
    -- (your existing bridge lemmas can go here)
    have : (∑ t ∈ Finset.range n, (1 / D : ℝ) ^ l t) < 1 := by
      exact sum_range_lt_one_of_sum_range_le_one
        (r := (1 / D : ℝ)) hrpos
        (k := n+1) (n := n) (hnk := Nat.lt_succ_self n)
        (lNat := l) h_le_one
    -- `∑ k < n` is `∑ t ∈ range n`
    simpa [range_eq_Iio] using this

  exact kraft_converse_nat_mono_prefix_lt_one_fin (D := D) (hD := hD)
    (l := l) (h_mono := h_mono) (h_prefix := h_prefix)

/-- Finite-index converse with `≤ 1`. -/
lemma kraft_converse_fin_mono_tight
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
    Digits.natToDigitsBE D (A i.val) (l i) (by omega)

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
    -- first get `A i.val = A j.val` via `natToDigitsBE_inj`,
    -- then strictMono injectivity for `A = kraft_numerator ...`.
    have hDpos : 0 < D := Nat.zero_lt_of_lt hD
    have hA_eq : A i.val = A j.val := by
      -- (exactly the pattern you used in the ℕ theorem’s injectivity proof)
      apply Digits.natToDigitsBE_inj hD
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
          have hwi : (w i).length = l i := by simp [w, Digits.natToDigitsBE_length]
          have hwj : (w j).length = l j := by simp [w, Digits.natToDigitsBE_length]
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
          Digits.natToDigitsBE D (A i.val) (l i) (by omega))) by
      -- convert raw goal back to PrefixFree (Set.range w)`
      simpa [w] using hraw

    refine Digits.prefixFree_range_natToDigitsBE_of_div_separated hD hA_lt ?_

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
theorem kraft_converse_nat_tight_alpha {α : Type _} [DecidableEq α] [Fintype α] [Nontrivial α]
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
    kraft_converse_nat_mono_tight (Fintype.card α) hcard l h_mono h_summable h_sum
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
lemma kraft_converse_fin_tight_alpha
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
    kraft_converse_fin_mono_tight
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

variable {α : Type _} [DecidableEq α] [Fintype α] [Nontrivial α]

/-- **Converse of Kraft's Inequality** (general alphabet, any index set).

For any index set `I` (finite or infinite), any finite alphabet `α` with `|α| ≥ 2`,
and length function `l : I → ℕ`, if `∑' i, |α|^{-l(i)} ≤ 1`, then there exists an
injective prefix-free code `w : I → List α` with the prescribed lengths.

Requires `Nontrivial α` (i.e., `|α| ≥ 2`) since prefix-free codes need at least 2 symbols. -/
theorem kraft_converse_summable_tight_alpha
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
    obtain ⟨w', hw'_inj, hw'_pf, hw'_len⟩ := kraft_converse_fin_tight_alpha
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
      kraft_converse_nat_tight_alpha (fun i ↦ l (e i)) he h_summable' h_sum'
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
theorem kraft_converse_of_arity
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
      obtain ⟨w_fin, h1, h2, h3⟩ := kraft_converse_fin_mono_tight D hD (l ∘ e) he_mono h_sum_fin
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
      obtain ⟨w_fin, h1, h2, h3⟩ := kraft_converse_nat_mono_tight D hD (l ∘ e) he_mono (h_summable.comp_injective e.injective) h_sum_nat
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
theorem kraft_inequality_tight_infinite_binary {I : Type _} (l : I → ℕ)
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
    (kraft_converse_of_arity (D := 2) (hD := by decide) ι (h_summable := h_summable) (h_sum := h_sum))

end Kraft
