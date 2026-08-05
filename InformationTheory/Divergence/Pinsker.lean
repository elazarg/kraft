/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import InformationTheory.Divergence.Basic
public import InformationTheory.Divergence.Binary

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Finite Pinsker and Bretagnolle-Huber inequalities

This file proves the classical **Pinsker** and **Bretagnolle-Huber** inequalities relating the
finite Kullback-Leibler divergence `klFin p q` of two distributions on a `Fintype` to their
total variation distance `tvDist p q`, plus the standard testing corollary. Neither inequality
is in mathlib (verified against the pinned `v4.32.2` snapshot: `Mathlib.InformationTheory` has
only `Coding/`, `Hamming`, and `KullbackLeibler`, and neither contains a total-variation bound).

Ported from the GameTheory experiments layer (probe E60, verified 2026-08-05), consolidating
previously duplicated local definitions. The source file inlined local copies of `klBin`,
`one_sub_div_le_log_div`, and `two_mul_sq_le_klBin` (marked "pending kraft consolidation"); those
copies are deleted here in favor of `InformationTheory.Divergence.Binary`'s declarations, and the
source's local `klFin` and its use of `InformationTheory.gibbs_sum_log_ratio_nonneg_of_ac` are
replaced by `InformationTheory.Divergence.Basic`'s `klFin` and `klFin_nonneg`.

## Main definitions

* `tvDist (p q : I → ℝ) : ℝ := (1 / 2) * ∑ i, |p i - q i|`, total variation distance.

## Main results

* `tvDist_eq_max_set` : the optimal-set identity `tvDist p q = ∑_{q ≤ p} (p - q)`.
* `logSum_ineq` : the classical log-sum inequality, `A * log (A / B) ≤ ∑ i ∈ S, a i * log
  (a i / b i)` for `A := ∑ i ∈ S, a i`, `B := ∑ i ∈ S, b i` — the engine behind
  `klBin_le_klFin_partition`, and reusable on its own.
* `klBin_le_klFin_partition` : the two-block log-sum reduction, `klBin P Q ≤ klFin p q` for the
  block masses `P, Q` of the optimal set.
* `pinsker` : `2 * tvDist p q ^ 2 ≤ klFin p q`, the **sharp constant `2`**, via the partition
  reduction plus the binary Pinsker inequality, with an extra boundary lemma
  (`log_pinsker_boundary`) covering the case where the optimal set carries all or none of `p`'s
  mass.
* `hellinger_ge` : `Real.exp (-(klFin p q) / 2) ≤ ∑ i, Real.sqrt (p i * q i)`, via weighted AM-GM.
* `bretagnolle_huber` : `(1 / 2) * Real.exp (-(klFin p q)) ≤ 1 - tvDist p q`, via `hellinger_ge`,
  the identity `∑ min (p, q) = 1 - tvDist p q`, and Cauchy-Schwarz.
* `miss_add_falseAlarm_ge` : the testing corollary, for every rejection region `A : Finset I`,
  `(∑ i ∈ A, q i) + ∑ i ∈ Aᶜ, p i ≥ (1 / 2) * Real.exp (-(klFin p q))` — any detector's
  false-alarm probability plus its miss probability is bounded below by the information budget.

## Nonclaims

* **Single pair of distributions.** Every statement is about one fixed pair `p, q` on one
  `Fintype`; there is no sequential, filtration, or anytime-detection statement.
* **No optimality beyond what is proved.** `pinsker` achieves the sharp constant `2`; no claim is
  made that `bretagnolle_huber`'s constant `1 / 2` is sharp (it is the standard textbook constant,
  not optimized further here).

## References

`experiments/FinitePinskerBH.lean` (probe E60); `experiments/BinaryKLQuadratic.lean` (probe E51);
`InformationTheory.gibbs_sum_log_ratio_nonneg_of_ac` in
`InformationTheory/Coding/SourceCodingLowerBound.lean`; Tsybakov, *Introduction to Nonparametric
Estimation*, §2.4 (Pinsker and Bretagnolle-Huber inequalities).
-/

@[expose] public section

namespace InformationTheory

variable {I : Type*} [Fintype I]

/-! ### Definition -/

/-- Total variation distance `(1/2) * ∑ i, |p i - q i|`. -/
noncomputable def tvDist (p q : I → ℝ) : ℝ := (1 / 2) * ∑ i, |p i - q i|

/-! ### The optimal-set identity for total variation -/

/-- The standard optimal-set identity: `tvDist p q` equals the mass `p` has in excess of `q` on
the set where `p` dominates. Needs only the normalization `hp1, hq1` (not nonnegativity): on
`A := {q ≤ p}`, `|p - q| = p - q`; on `Aᶜ`, `|p - q| = q - p`; and `∑_A (p - q) = ∑_{Aᶜ} (q - p)`
because the two differ by `∑ (p - q) = ∑ p - ∑ q = 0`. -/
theorem tvDist_eq_max_set {p q : I → ℝ} (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1) :
    tvDist p q = ∑ i ∈ Finset.univ.filter (fun i => q i ≤ p i), (p i - q i) := by
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => q i ≤ p i)
      (fun i => |p i - q i|)
  have hA : ∀ i ∈ Finset.univ.filter (fun i => q i ≤ p i), |p i - q i| = p i - q i := by
    intro i hi
    exact abs_of_nonneg (by linarith [(Finset.mem_filter.mp hi).2])
  have hAc : ∀ i ∈ Finset.univ.filter (fun i => ¬ q i ≤ p i), |p i - q i| = q i - p i := by
    intro i hi
    have hlt : p i < q i := lt_of_not_ge (Finset.mem_filter.mp hi).2
    rw [abs_sub_comm]
    exact abs_of_nonneg (by linarith)
  rw [Finset.sum_congr rfl hA] at hsplit
  rw [Finset.sum_congr rfl hAc] at hsplit
  have hzero : ∑ i, (p i - q i) = 0 := by
    rw [Finset.sum_sub_distrib, hp1, hq1]; ring
  have hAcsum : ∑ i ∈ Finset.univ.filter (fun i => ¬ q i ≤ p i), (q i - p i)
      = ∑ i ∈ Finset.univ.filter (fun i => q i ≤ p i), (p i - q i) := by
    have hsplit2 := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => q i ≤ p i)
        (fun i => p i - q i)
    rw [hzero] at hsplit2
    have : ∑ i ∈ Finset.univ.filter (fun i => ¬ q i ≤ p i), (q i - p i)
        = -∑ i ∈ Finset.univ.filter (fun i => ¬ q i ≤ p i), (p i - q i) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [this]
    linarith [hsplit2]
  unfold tvDist
  rw [← hsplit, hAcsum]
  ring

/-! ### The finite log-sum inequality (the engine behind the partition reduction) -/

/-- The finite log-sum inequality: grouping the terms of a Gibbs-type sum over a subset `S` can
only decrease it. For nonnegative `a, b` on `S` with the absolute-continuity condition
`b i = 0 → a i = 0`, writing `A := ∑ i ∈ S, a i` and `B := ∑ i ∈ S, b i`,
`A * log (A / B) ≤ ∑ i ∈ S, a i * log (a i / b i)`. Proved by the same `log x ≥ 1 - 1/x` termwise
trick as `klFin_nonneg`, with an extra `A / B` renormalization factor, reusing
`InformationTheory.Divergence.Binary.one_sub_div_le_log_div`; the degenerate case `B = 0`
(forcing `A = 0` by the a.c. hypothesis, via `b`'s nonnegativity) is handled separately since
junk values make both sides `0` there. -/
theorem logSum_ineq {I : Type*} {S : Finset I} {a b : I → ℝ}
    (ha : ∀ i ∈ S, 0 ≤ a i) (hb : ∀ i ∈ S, 0 ≤ b i)
    (hac : ∀ i ∈ S, b i = 0 → a i = 0) :
    (∑ i ∈ S, a i) * Real.log ((∑ i ∈ S, a i) / (∑ i ∈ S, b i))
      ≤ ∑ i ∈ S, a i * Real.log (a i / b i) := by
  set A := ∑ i ∈ S, a i with hAdef
  set B := ∑ i ∈ S, b i with hBdef
  have hA0 : 0 ≤ A := Finset.sum_nonneg ha
  have hB0 : 0 ≤ B := Finset.sum_nonneg hb
  rcases hB0.eq_or_lt with hB0' | hBpos
  · have hb0 : ∀ i ∈ S, b i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hb).1 (hBdef ▸ hB0'.symm)
    have ha0 : ∀ i ∈ S, a i = 0 := fun i hi => hac i hi (hb0 i hi)
    have hA0' : A = 0 := hAdef ▸ Finset.sum_eq_zero ha0
    rw [hA0']
    simp only [zero_mul]
    apply le_of_eq
    refine Eq.symm (Finset.sum_eq_zero (fun i hi => ?_))
    rw [ha0 i hi]
    simp only [zero_div, Real.log_zero, mul_zero]
  · have key : ∀ i ∈ S,
        a i - (A / B) * b i ≤ a i * Real.log (a i / b i) - a i * Real.log (A / B) := by
      intro i hi
      rcases (ha i hi).eq_or_lt with hai0 | haipos
      · rw [← hai0]
        simp only [zero_mul, sub_zero]
        have hnn : 0 ≤ (A / B) * b i := mul_nonneg (div_nonneg hA0 hB0) (hb i hi)
        linarith
      · have hbi_pos : 0 < b i := by
          rcases (hb i hi).eq_or_lt with hbi0 | hbipos
          · exact absurd (hac i hi hbi0.symm) haipos.ne'
          · exact hbipos
        have hAipos : a i ≤ A := hAdef ▸ Finset.single_le_sum ha hi
        have hABpos : 0 < A / B := div_pos (lt_of_lt_of_le haipos hAipos) hBpos
        have hratio_pos : 0 < a i / b i := div_pos haipos hbi_pos
        have hbound : 1 - (A / B) / (a i / b i) ≤ Real.log ((a i / b i) / (A / B)) :=
          one_sub_div_le_log_div hratio_pos hABpos
        have hlogeq : Real.log ((a i / b i) / (A / B))
            = Real.log (a i / b i) - Real.log (A / B) :=
          Real.log_div hratio_pos.ne' hABpos.ne'
        rw [hlogeq] at hbound
        have halg : (A / B) / (a i / b i) = A / B * b i / a i := by
          field_simp
        rw [halg] at hbound
        have hmul := mul_le_mul_of_nonneg_left hbound haipos.le
        have heq1 : a i * (1 - A / B * b i / a i) = a i - A / B * b i := by
          field_simp
        have heq2 : a i * (Real.log (a i / b i) - Real.log (A / B))
            = a i * Real.log (a i / b i) - a i * Real.log (A / B) := by ring
        rw [heq1, heq2] at hmul
        exact hmul
    have hsum := Finset.sum_le_sum key
    have hlhs : ∑ i ∈ S, (a i - (A / B) * b i) = A - (A / B) * B := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← hAdef, ← hBdef]
    have hrhs : ∑ i ∈ S, (a i * Real.log (a i / b i) - a i * Real.log (A / B))
        = (∑ i ∈ S, a i * Real.log (a i / b i)) - A * Real.log (A / B) := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← hAdef]
    rw [hlhs, hrhs] at hsum
    have hcancel : A - A / B * B = 0 := by
      rw [div_mul_cancel₀ A hBpos.ne']
      ring
    linarith

/-! ### The two-block reduction -/

/-- The two-block log-sum reduction: partitioning `Finset.univ` into `A := {q ≤ p}` and its
complement and applying `logSum_ineq` on each block. `klBin P Q` unfolds to exactly
`P * log (P/Q) + (1-P) * log ((1-P)/(1-Q))`. -/
theorem klBin_le_klFin_partition {p q : I → ℝ}
    (hp0 : ∀ i, 0 ≤ p i) (hq0 : ∀ i, 0 ≤ q i)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1)
    (hac : ∀ i, q i = 0 → p i = 0)
    (A : Finset I) (hAdef : A = Finset.univ.filter (fun i => q i ≤ p i))
    (P Q : ℝ) (hPdef : P = ∑ i ∈ A, p i) (hQdef : Q = ∑ i ∈ A, q i) :
    klBin P Q ≤ klFin p q := by
  set B := Finset.univ.filter (fun i => ¬ q i ≤ p i) with hBdef
  have hA1 := logSum_ineq (S := A) (a := p) (b := q)
      (fun i _ => hp0 i) (fun i _ => hq0 i) (fun i _ hqi => hac i hqi)
  have hB1 := logSum_ineq (S := B) (a := p) (b := q)
      (fun i _ => hp0 i) (fun i _ => hq0 i) (fun i _ hqi => hac i hqi)
  rw [← hPdef, ← hQdef] at hA1
  have hBP : ∑ i ∈ B, p i = 1 - P := by
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => q i ≤ p i) p
    rw [← hAdef, hp1] at hsplit
    rw [hBdef, hPdef]
    linarith [hsplit]
  have hBQ : ∑ i ∈ B, q i = 1 - Q := by
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => q i ≤ p i) q
    rw [← hAdef, hq1] at hsplit
    rw [hBdef, hQdef]
    linarith [hsplit]
  rw [hBP, hBQ] at hB1
  have hklFin_split : klFin p q
      = ∑ i ∈ A, p i * Real.log (p i / q i) + ∑ i ∈ B, p i * Real.log (p i / q i) := by
    rw [hAdef, hBdef]
    exact (Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => q i ≤ p i)
      (fun i => p i * Real.log (p i / q i))).symm
  unfold klBin
  rw [hklFin_split]
  linarith [hA1, hB1]

/-! ### A single-variable boundary lemma for `pinsker` -/

/-- The boundary case of binary Pinsker at `P = 1` (and, by `klBin`'s complement symmetry, at
`P = 0`): for `t ∈ (0, 1]`, `2 * (1 - t) ^ 2 ≤ -Real.log t`. Proved by showing
`h x := -Real.log x - 2 * (1 - x) ^ 2` is antitone on `(0, ∞)` — its derivative
`h' x = -x⁻¹ + 4 * (1 - x)` satisfies `x * h' x = -(2*x - 1)^2 ≤ 0`, hence `h' x ≤ 0` for `x > 0`
— together with `h 1 = 0`. -/
private theorem log_pinsker_boundary {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    2 * (1 - t) ^ 2 ≤ -Real.log t := by
  set h : ℝ → ℝ := fun x => -Real.log x - 2 * (1 - x) ^ 2 with hdef
  set h' : ℝ → ℝ := fun x => -x⁻¹ + 4 * (1 - x) with hdef'
  have hderiv : ∀ x ∈ Set.Ioi (0:ℝ), HasDerivAt h (h' x) x := by
    intro x hx
    have hx0 : x ≠ 0 := (Set.mem_Ioi.mp hx).ne'
    have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx0
    have h1 : HasDerivAt (fun y : ℝ => -Real.log y) (-x⁻¹) x := hlog.neg
    have hid : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id' (𝕜 := ℝ) x
    have hsub : HasDerivAt (fun y : ℝ => (1:ℝ) - y) (-1) x := hid.const_sub 1
    have hsq : HasDerivAt (fun y : ℝ => (1 - y) ^ 2)
        ((2 : ℕ) * (1 - x) ^ (2 - 1) * (-1)) x := hsub.pow 2
    have h2 : HasDerivAt (fun y : ℝ => 2 * (1 - y) ^ 2)
        (2 * ((2 : ℕ) * (1 - x) ^ (2 - 1) * (-1))) x := hsq.const_mul 2
    have hraw := h1.sub h2
    have hval : -x⁻¹ - 2 * ((2 : ℕ) * (1 - x) ^ (2 - 1) * (-1)) = h' x := by
      simp only [hdef']
      push_cast
      ring
    rw [hval] at hraw
    exact hraw
  have hantiOn : AntitoneOn h (Set.Ioi (0 : ℝ)) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi (0:ℝ))
    · exact fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ioi] at hx
      exact (hderiv x hx).hasDerivWithinAt
    · intro x hx
      rw [interior_Ioi] at hx
      have hxpos : 0 < x := hx
      have hxh' : x * h' x = -(2 * x - 1) ^ 2 := by
        simp only [hdef']
        field_simp
        ring
      nlinarith [sq_nonneg (2 * x - 1), hxh']
  have h1mem : (1:ℝ) ∈ Set.Ioi (0:ℝ) := by norm_num
  have htmem : t ∈ Set.Ioi (0:ℝ) := ht0
  have hle : h 1 ≤ h t := hantiOn htmem h1mem ht1
  have hh1 : h 1 = 0 := by simp [hdef]
  rw [hh1] at hle
  have hle' : 0 ≤ -Real.log t - 2 * (1 - t) ^ 2 := by simpa only [hdef] using hle
  linarith

/-! ### Pinsker's inequality -/

/-- **Pinsker's inequality**, with the **sharp constant `2`**: `2 * tvDist p q ^ 2 ≤ klFin p q`.
Proved via `tvDist_eq_max_set` (`tvDist = P - Q` for the optimal-set masses `P, Q`),
`klBin_le_klFin_partition` (`klBin P Q ≤ klFin p q`), and a case split on whether `P` is `0`, `1`,
or interior: at `P = 0`, `Q = 0` too (nonnegativity plus `hac`), so `tvDist = 0` and the bound
reduces to Gibbs' inequality `0 ≤ klFin p q` (`klFin_nonneg`); at `P = 1`, `klBin 1 Q` computes to
`-Real.log Q` and `log_pinsker_boundary` closes it; on the interior, `two_mul_sq_le_klBin`
applies directly. -/
theorem pinsker {p q : I → ℝ}
    (hp0 : ∀ i, 0 ≤ p i) (hq0 : ∀ i, 0 ≤ q i)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1)
    (hac : ∀ i, q i = 0 → p i = 0) :
    2 * tvDist p q ^ 2 ≤ klFin p q := by
  set A := Finset.univ.filter (fun i => q i ≤ p i) with hAdef
  set P := ∑ i ∈ A, p i with hPdef
  set Q := ∑ i ∈ A, q i with hQdef
  have hQP : Q ≤ P := by
    rw [hPdef, hQdef]
    exact Finset.sum_le_sum (fun i hi => (Finset.mem_filter.mp hi).2)
  have hP0 : 0 ≤ P := hPdef ▸ Finset.sum_nonneg (fun i _ => hp0 i)
  have hQ0 : 0 ≤ Q := hQdef ▸ Finset.sum_nonneg (fun i _ => hq0 i)
  have hP1 : P ≤ 1 := by
    rw [hPdef, ← hp1]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun i _ _ => hp0 i)
  have htv : tvDist p q = P - Q := by
    rw [tvDist_eq_max_set hp1 hq1, ← hAdef, hPdef, hQdef, Finset.sum_sub_distrib]
  have hpart : klBin P Q ≤ klFin p q :=
    klBin_le_klFin_partition hp0 hq0 hp1 hq1 hac A hAdef P Q hPdef hQdef
  have hQ0iff : Q = 0 → P = 0 := by
    intro hQeq
    have hqA : ∀ i ∈ A, q i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hq0 i)).1 (hQdef ▸ hQeq)
    have hpA : ∀ i ∈ A, p i = 0 := fun i hi => hac i (hqA i hi)
    rw [hPdef]
    exact Finset.sum_eq_zero hpA
  rcases hP0.eq_or_lt with hP0' | hPpos
  · have hQeq0 : Q = 0 := le_antisymm (by linarith [hQP, hP0']) hQ0
    have htv0 : tvDist p q = 0 := by rw [htv]; linarith [hP0', hQeq0]
    have hgibbs : 0 ≤ klFin p q := klFin_nonneg hp0 hq0 hac (by rw [hp1, hq1])
    rw [htv0]
    nlinarith [hgibbs]
  · have hQpos : 0 < Q := by
      rcases hQ0.eq_or_lt with hQ0' | hQpos
      · exact absurd (hQ0iff hQ0'.symm) hPpos.ne'
      · exact hQpos
    rcases hP1.eq_or_lt with hP1' | hPlt1
    · have hQmem : Q ∈ Set.Ioc (0:ℝ) 1 := ⟨hQpos, hP1' ▸ hQP⟩
      have hbound := log_pinsker_boundary hQmem.1 hQmem.2
      have hklBin1 : klBin P Q = -Real.log Q := by
        rw [hP1']
        unfold klBin
        simp [one_div, Real.log_inv]
      rw [htv, hP1']
      rw [hklBin1] at hpart
      nlinarith [hpart, hbound]
    · have hQlt1 : Q < 1 := lt_of_le_of_lt hQP hPlt1
      have hPmem : P ∈ Set.Ioo (0:ℝ) 1 := ⟨hPpos, hPlt1⟩
      have hQmem : Q ∈ Set.Ioo (0:ℝ) 1 := ⟨hQpos, hQlt1⟩
      have hpinsker2 : 2 * (P - Q) ^ 2 ≤ klBin P Q := two_mul_sq_le_klBin hQmem hPmem
      rw [htv]
      linarith [hpart, hpinsker2]

/-! ### The Hellinger affinity bound -/

/-- **Hellinger affinity lower bound**: `exp (-(klFin p q) / 2) ≤ ∑ i, sqrt (p i * q i)`.
Proved by weighted AM-GM (`Real.geom_mean_le_arith_mean_weighted`) on the support
`S := {0 < p}` of `p`, with weights `p` and values `z i := sqrt (q i / p i)`: the geometric mean
`∏ i ∈ S, z i ^ p i` computes to `exp (-(klFin p q) / 2)` (using `hac` to keep `q i > 0` wherever
`p i > 0`, so every `log (z i)` is finite), while the arithmetic mean `∑ i ∈ S, p i * z i` equals
`∑ i, sqrt (p i * q i)` (zero-mass rows contribute `0` on both sides). Only `hp1` (not `hq1`) is
needed: the Hellinger affinity makes sense for sub-probability `q`. -/
theorem hellinger_ge {p q : I → ℝ}
    (hp0 : ∀ i, 0 ≤ p i) (hq0 : ∀ i, 0 ≤ q i)
    (hp1 : ∑ i, p i = 1)
    (hac : ∀ i, q i = 0 → p i = 0) :
    Real.exp (-(klFin p q) / 2) ≤ ∑ i, Real.sqrt (p i * q i) := by
  set S := Finset.univ.filter (fun i => 0 < p i) with hSdef
  set z : I → ℝ := fun i => Real.sqrt (q i / p i) with hzdef
  have hw_nonneg : ∀ i ∈ S, 0 ≤ p i := fun i hi => (Finset.mem_filter.mp hi).2.le
  have hw_sum : ∑ i ∈ S, p i = 1 := by
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => 0 < p i) p
    have hzero : ∑ i ∈ Finset.univ.filter (fun i => ¬ 0 < p i), p i = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hle : p i ≤ 0 := not_lt.mp (Finset.mem_filter.mp hi).2
      linarith [hp0 i]
    rw [hSdef]
    linarith [hsplit, hzero, hp1]
  have hz_nonneg : ∀ i ∈ S, 0 ≤ z i := fun i _ => Real.sqrt_nonneg _
  have hQpos : ∀ i ∈ S, 0 < q i := by
    intro i hi
    have hpi : 0 < p i := (Finset.mem_filter.mp hi).2
    by_contra hcon
    exact absurd (hac i (le_antisymm (not_lt.mp hcon) (hq0 i))) hpi.ne'
  have hz_pos : ∀ i ∈ S, 0 < z i := by
    intro i hi
    exact Real.sqrt_pos.mpr (div_pos (hQpos i hi) (Finset.mem_filter.mp hi).2)
  have hAMGM : ∏ i ∈ S, z i ^ (p i) ≤ ∑ i ∈ S, p i * z i :=
    Real.geom_mean_le_arith_mean_weighted S p z hw_nonneg hw_sum hz_nonneg
  -- LHS: the geometric mean equals `exp (-(klFin p q) / 2)`.
  have hprod_eq : ∏ i ∈ S, z i ^ (p i)
      = Real.exp (∑ i ∈ S, p i * Real.log (p i / q i) / (-2)) := by
    have hstep : ∏ i ∈ S, z i ^ (p i)
        = ∏ i ∈ S, Real.exp (p i * Real.log (p i / q i) / (-2)) := by
      apply Finset.prod_congr rfl
      intro i hi
      have hpi : 0 < p i := (Finset.mem_filter.mp hi).2
      have hqi : 0 < q i := hQpos i hi
      rw [Real.rpow_def_of_pos (hz_pos i hi)]
      congr 1
      have hlogz : Real.log (z i) = Real.log (q i / p i) / 2 := by
        rw [hzdef]
        exact Real.log_sqrt (div_nonneg hqi.le hpi.le)
      have hlogqp : Real.log (q i / p i) = -Real.log (p i / q i) := by
        rw [← Real.log_inv, inv_div]
      rw [hlogz, hlogqp]
      ring
    rw [hstep, ← Real.exp_sum]
  have hsum_eq : ∑ i ∈ S, p i * Real.log (p i / q i) / (-2) = -(klFin p q) / 2 := by
    have hextend : ∑ i ∈ S, p i * Real.log (p i / q i) = klFin p q := by
      unfold klFin
      rw [hSdef]
      have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => 0 < p i)
          (fun i => p i * Real.log (p i / q i))
      have hzero : ∑ i ∈ Finset.univ.filter (fun i => ¬ 0 < p i),
          p i * Real.log (p i / q i) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have hle : p i ≤ 0 := not_lt.mp (Finset.mem_filter.mp hi).2
        have : p i = 0 := le_antisymm hle (hp0 i)
        rw [this]; ring
      linarith [hsplit, hzero]
    rw [← Finset.sum_div, hextend]
    ring
  rw [hprod_eq, hsum_eq] at hAMGM
  -- RHS: the arithmetic mean equals `∑ i, sqrt (p i * q i)`.
  have hrhs_eq : ∑ i ∈ S, p i * z i = ∑ i, Real.sqrt (p i * q i) := by
    have hterm : ∀ i ∈ S, p i * z i = Real.sqrt (p i * q i) := by
      intro i hi
      have hpi : 0 < p i := (Finset.mem_filter.mp hi).2
      rw [hzdef]
      rw [show p i * Real.sqrt (q i / p i)
          = Real.sqrt (p i ^ 2) * Real.sqrt (q i / p i) by rw [Real.sqrt_sq hpi.le]]
      rw [← Real.sqrt_mul (sq_nonneg (p i))]
      congr 1
      field_simp
    rw [Finset.sum_congr rfl hterm]
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => 0 < p i)
        (fun i => Real.sqrt (p i * q i))
    have hzero : ∑ i ∈ Finset.univ.filter (fun i => ¬ 0 < p i), Real.sqrt (p i * q i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hle : p i ≤ 0 := not_lt.mp (Finset.mem_filter.mp hi).2
      have : p i = 0 := le_antisymm hle (hp0 i)
      rw [this]; simp
    rw [hSdef]
    linarith [hsplit, hzero]
  rw [hrhs_eq] at hAMGM
  exact hAMGM

/-! ### Shared identities for the Bretagnolle-Huber inequality -/

/-- `∑ i, min (p i) (q i) = 1 - tvDist p q`: the pointwise minimum sums to the total mass minus
the total variation distance. -/
private theorem min_sum_eq_one_sub_tvDist {p q : I → ℝ}
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1) :
    ∑ i, min (p i) (q i) = 1 - tvDist p q := by
  have htv := tvDist_eq_max_set hp1 hq1
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => q i ≤ p i)
      (fun i => min (p i) (q i))
  have hA : ∀ i ∈ Finset.univ.filter (fun i => q i ≤ p i), min (p i) (q i) = q i := by
    intro i hi
    exact min_eq_right (Finset.mem_filter.mp hi).2
  have hAc : ∀ i ∈ Finset.univ.filter (fun i => ¬ q i ≤ p i), min (p i) (q i) = p i := by
    intro i hi
    exact min_eq_left (lt_of_not_ge (Finset.mem_filter.mp hi).2).le
  rw [Finset.sum_congr rfl hA, Finset.sum_congr rfl hAc] at hsplit
  have hAcP : ∑ i ∈ Finset.univ.filter (fun i => ¬ q i ≤ p i), p i
      = 1 - ∑ i ∈ Finset.univ.filter (fun i => q i ≤ p i), p i := by
    have hs2 := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => q i ≤ p i) p
    rw [hp1] at hs2
    linarith [hs2]
  rw [hAcP] at hsplit
  rw [htv, Finset.sum_sub_distrib]
  linarith [hsplit]

/-- `∑ i, max (p i) (q i) ≤ 2`, from nonnegativity and `max a b ≤ a + b`. -/
private theorem max_sum_le_two {p q : I → ℝ}
    (hp0 : ∀ i, 0 ≤ p i) (hq0 : ∀ i, 0 ≤ q i)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1) :
    ∑ i, max (p i) (q i) ≤ 2 := by
  have hle : ∀ i, max (p i) (q i) ≤ p i + q i :=
    fun i => max_le (by linarith [hq0 i]) (by linarith [hp0 i])
  calc ∑ i, max (p i) (q i) ≤ ∑ i, (p i + q i) := Finset.sum_le_sum (fun i _ => hle i)
    _ = 2 := by rw [Finset.sum_add_distrib, hp1, hq1]; norm_num

/-! ### The Bretagnolle-Huber inequality -/

/-- **The Bretagnolle-Huber inequality**: `(1/2) * exp (-(klFin p q)) ≤ 1 - tvDist p q`. Proved by
Cauchy-Schwarz (`Finset.sum_mul_sq_le_sq_mul_sq`) applied to `sqrt (min p q)` and `sqrt (max p q)`
— whose termwise product is `sqrt (p * q)` since `min * max = p * q` always — giving
`(∑ sqrt (p q)) ^ 2 ≤ (∑ min p q) * (∑ max p q) ≤ (1 - tvDist p q) * 2`; combined with
`hellinger_ge` squared, `exp (-(klFin p q)) ≤ (∑ sqrt (p q)) ^ 2 ≤ 2 * (1 - tvDist p q)`. -/
theorem bretagnolle_huber {p q : I → ℝ}
    (hp0 : ∀ i, 0 ≤ p i) (hq0 : ∀ i, 0 ≤ q i)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1)
    (hac : ∀ i, q i = 0 → p i = 0) :
    (1 / 2) * Real.exp (-(klFin p q)) ≤ 1 - tvDist p q := by
  have hhell := hellinger_ge hp0 hq0 hp1 hac
  have hmin_eq : ∑ i, min (p i) (q i) = 1 - tvDist p q := min_sum_eq_one_sub_tvDist hp1 hq1
  have hmax_le : ∑ i, max (p i) (q i) ≤ 2 := max_sum_le_two hp0 hq0 hp1 hq1
  have hCS : (∑ i, Real.sqrt (min (p i) (q i)) * Real.sqrt (max (p i) (q i))) ^ 2
      ≤ (∑ i, Real.sqrt (min (p i) (q i)) ^ 2) * ∑ i, Real.sqrt (max (p i) (q i)) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
  have hsqmin : ∀ i, Real.sqrt (min (p i) (q i)) ^ 2 = min (p i) (q i) :=
    fun i => Real.sq_sqrt (le_min (hp0 i) (hq0 i))
  have hsqmax : ∀ i, Real.sqrt (max (p i) (q i)) ^ 2 = max (p i) (q i) :=
    fun i => Real.sq_sqrt (le_trans (hp0 i) (le_max_left _ _))
  have hprod : ∀ i, Real.sqrt (min (p i) (q i)) * Real.sqrt (max (p i) (q i))
      = Real.sqrt (p i * q i) := by
    intro i
    rw [← Real.sqrt_mul (le_min (hp0 i) (hq0 i))]
    congr 1
    rcases le_total (p i) (q i) with h | h
    · rw [min_eq_left h, max_eq_right h]
    · rw [min_eq_right h, max_eq_left h]; ring
  rw [Finset.sum_congr rfl (fun i _ => hprod i)] at hCS
  rw [Finset.sum_congr rfl (fun i _ => hsqmin i)] at hCS
  rw [Finset.sum_congr rfl (fun i _ => hsqmax i)] at hCS
  rw [hmin_eq] at hCS
  have hrho_nonneg : 0 ≤ ∑ i, Real.sqrt (p i * q i) :=
    Finset.sum_nonneg (fun i _ => Real.sqrt_nonneg _)
  have hexp_nonneg : 0 ≤ Real.exp (-(klFin p q) / 2) := (Real.exp_pos _).le
  have hsq_le : Real.exp (-(klFin p q) / 2) ^ 2 ≤ (∑ i, Real.sqrt (p i * q i)) ^ 2 :=
    pow_le_pow_left₀ hexp_nonneg hhell 2
  have hexp_sq : Real.exp (-(klFin p q) / 2) ^ 2 = Real.exp (-(klFin p q)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hexp_sq] at hsq_le
  have h1mtv : 0 ≤ 1 - tvDist p q :=
    hmin_eq ▸ Finset.sum_nonneg (fun i _ => le_min (hp0 i) (hq0 i))
  have hstep : (1 - tvDist p q) * ∑ i, max (p i) (q i) ≤ (1 - tvDist p q) * 2 :=
    mul_le_mul_of_nonneg_left hmax_le h1mtv
  linarith [hsq_le, hCS, hstep]

/-! ### The testing corollary -/

/-- **The testing corollary**: for every rejection region `A : Finset I`, the detector's
false-alarm probability `∑_{i ∈ A} q i` plus its miss probability `∑_{i ∈ Aᶜ} p i` is bounded
below by the information budget `(1/2) * exp (-(klFin p q))`. From `bretagnolle_huber` and the
pointwise bounds `min p q ≤ q` (on `A`) and `min p q ≤ p` (on `Aᶜ`). -/
theorem miss_add_falseAlarm_ge {p q : I → ℝ}
    (hp0 : ∀ i, 0 ≤ p i) (hq0 : ∀ i, 0 ≤ q i)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1)
    (hac : ∀ i, q i = 0 → p i = 0) [DecidableEq I] (A : Finset I) :
    (1 / 2) * Real.exp (-(klFin p q)) ≤ (∑ i ∈ A, q i) + ∑ i ∈ Aᶜ, p i := by
  have hBH := bretagnolle_huber hp0 hq0 hp1 hq1 hac
  have hmineq : ∑ i, min (p i) (q i) = 1 - tvDist p q := min_sum_eq_one_sub_tvDist hp1 hq1
  have hsplit : ∑ i ∈ A, min (p i) (q i) + ∑ i ∈ Aᶜ, min (p i) (q i) = ∑ i, min (p i) (q i) :=
    Finset.sum_add_sum_compl A _
  have h1 : ∑ i ∈ A, min (p i) (q i) ≤ ∑ i ∈ A, q i :=
    Finset.sum_le_sum (fun i _ => min_le_right _ _)
  have h2 : ∑ i ∈ Aᶜ, min (p i) (q i) ≤ ∑ i ∈ Aᶜ, p i :=
    Finset.sum_le_sum (fun i _ => min_le_left _ _)
  linarith [hBH, hmineq, hsplit, h1, h2]

end InformationTheory
