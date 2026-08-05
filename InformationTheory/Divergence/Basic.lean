/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Finite Kullback-Leibler divergence

This file defines the finite Kullback-Leibler divergence `klFin p q` between two functions
`p q : I → ℝ` on a `Fintype` `I`, directly as a `Finset.sum` (the same style as
`InformationTheory.entropy` and `InformationTheory.condEntropy`), rather than through Mathlib's
measure-theoretic `klDiv`. It proves the mass-free Gibbs inequality and relabeling invariance,
the shared foundation for the rest of the `InformationTheory.Divergence` hierarchy.

Ported from the GameTheory experiments layer (probes E58 and E59, verified 2026-08-05),
consolidating previously duplicated local definitions.

## Main definitions

* `klFin (p q : I → ℝ) : ℝ := ∑ i, p i * Real.log (p i / q i)`, the finite Kullback-Leibler
  divergence `KL(p ‖ q)`, in nats.

## Main results

* `sum_sub_sum_le_klFin` : the mass-free termwise Gibbs bound,
  `(∑ i, p i) - (∑ i, q i) ≤ klFin p q`, under nonnegativity and absolute continuity alone (no
  normalization hypothesis at all).
* `klFin_nonneg` : Gibbs' inequality, `0 ≤ klFin p q`, whenever `q` carries no more total mass
  than `p`. This *generalizes* `InformationTheory.gibbs_sum_log_ratio_nonneg_of_ac` (the
  normalized special case, `∑ p = 1`, `∑ q ≤ 1`), which becomes derivable from it; the existing
  lemma is deliberately left untouched in this pass.
* `klFin_relabel` : `klFin` is invariant under relabeling by an equivalence, mirroring
  `InformationTheory.entropy_relabel`.

## The sign trap (junk-value boundary)

`klFin` uses Lean/Mathlib's junk conventions `a / 0 = 0` and `Real.log 0 = 0`. **This is the one
place a naive reading of "KL divergence" goes wrong.** A term where `p i > 0 = q i` should
contribute `+∞` (an event `q` declares impossible but `p` gives positive mass is *infinitely*
informative), but under the stated junk conventions it silently evaluates to
`p i * Real.log (p i / 0) = p i * Real.log 0 = p i * 0 = 0` instead — the *wrong* value, not
merely an undefined one. Every statement below therefore carries the honest boundary condition
explicitly, absolute continuity `hac : ∀ i, q i = 0 → p i = 0`, so that "no term hits the trap"
is a hypothesis, not an accident of the junk conventions.

## References

`experiments/FiniteKLChainRule.lean` (probe E59); `experiments/EntropyProduction.lean` (probe
E58); `InformationTheory.gibbs_sum_log_ratio_nonneg_of_ac` in
`InformationTheory/Coding/SourceCodingLowerBound.lean`.
-/

namespace InformationTheory

variable {I : Type*} [Fintype I]

/-! ### Definition -/

/-- Finite Kullback-Leibler divergence `KL(p ‖ q) = ∑ i, p i * log (p i / q i)`, in nats. Zero
rows of `p` vanish by `mul_zero`-style junk regardless of `q i`; rows with `p i > 0 = q i` hit
the sign trap documented in the module docstring, so every theorem about `klFin` carries the
absolute-continuity hypothesis `hac`. -/
noncomputable def klFin (p q : I → ℝ) : ℝ := ∑ i, p i * Real.log (p i / q i)

/-! ### The mass-free Gibbs inequality -/

/-- The termwise bound behind Gibbs' inequality, tolerant of `b = 0` under the absolute-continuity
hypothesis `hab`: for `a, b ≥ 0` with `b = 0 → a = 0`, `a - b ≤ a * Real.log (a / b)`. When `b = 0`
(hence `a = 0` by `hab`) both sides are `0`. When `a = 0 < b` the right side is `0` and the left
side is `-b ≤ 0`. When `a, b > 0` this is `Real.one_sub_inv_le_log_of_pos` applied to `t = a / b`,
rearranged. -/
private theorem sub_le_mul_log_div {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : b = 0 → a = 0) : a - b ≤ a * Real.log (a / b) := by
  rcases hb.eq_or_lt with hb0 | hbpos
  · have ha0 : a = 0 := hab hb0.symm
    simp [ha0, ← hb0]
  · rcases ha.eq_or_lt with ha0 | hapos
    · simpa [← ha0] using hb
    · have ht : 0 < a / b := div_pos hapos hbpos
      have hlog : 1 - (a / b)⁻¹ ≤ Real.log (a / b) := Real.one_sub_inv_le_log_of_pos ht
      rw [inv_div] at hlog
      have hmul := mul_le_mul_of_nonneg_left hlog hapos.le
      have heq : a * (1 - b / a) = a - b := by
        field_simp
      rw [heq] at hmul
      exact hmul

/-- **The mass-free Gibbs bound.** `(∑ i, p i) - (∑ i, q i) ≤ klFin p q`, under nonnegativity and
absolute continuity alone — no normalization hypothesis at all. Summing the termwise bound
`sub_le_mul_log_div` over `Finset.univ`. -/
theorem sum_sub_sum_le_klFin {p q : I → ℝ} (hp0 : ∀ i, 0 ≤ p i) (hq0 : ∀ i, 0 ≤ q i)
    (hac : ∀ i, q i = 0 → p i = 0) :
    (∑ i, p i) - (∑ i, q i) ≤ klFin p q := by
  have key : ∀ i, p i - q i ≤ p i * Real.log (p i / q i) :=
    fun i => sub_le_mul_log_div (hp0 i) (hq0 i) (hac i)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => key i)
  rwa [Finset.sum_sub_distrib] at hsum

/-- **Gibbs' inequality for `klFin`.** `0 ≤ klFin p q` whenever `q` carries no more total mass
than `p` (`hmass`). This generalizes `InformationTheory.gibbs_sum_log_ratio_nonneg_of_ac`, which
is exactly the normalized special case `∑ p = 1`, `∑ q ≤ 1`; the existing lemma is deliberately
left untouched in this pass. -/
theorem klFin_nonneg {p q : I → ℝ} (hp0 : ∀ i, 0 ≤ p i) (hq0 : ∀ i, 0 ≤ q i)
    (hac : ∀ i, q i = 0 → p i = 0) (hmass : ∑ i, q i ≤ ∑ i, p i) :
    0 ≤ klFin p q := by
  have h := sum_sub_sum_le_klFin hp0 hq0 hac
  linarith

/-! ### Relabeling invariance -/

/-- **Relabeling invariance**: `klFin` is invariant under relabeling by an equivalence, mirroring
`InformationTheory.entropy_relabel`. -/
theorem klFin_relabel {K L : Type*} [Fintype K] [Fintype L] (e : K ≃ L) (p q : K → ℝ) :
    klFin (p ∘ e.symm) (q ∘ e.symm) = klFin p q := by
  show ∑ l : L, (p ∘ e.symm) l * Real.log ((p ∘ e.symm) l / (q ∘ e.symm) l)
      = ∑ k : K, p k * Real.log (p k / q k)
  exact Equiv.sum_comp e.symm (fun k => p k * Real.log (p k / q k))

end InformationTheory
