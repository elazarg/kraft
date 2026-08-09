/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
public import Mathlib.MeasureTheory.Measure.WithDensity
public import InformationTheory.Divergence.Basic

/-!
# Finite and Measure-Theoretic Kullback–Leibler Divergence

This file connects the elementary finite divergence `InformationTheory.klFin` to mathlib's
measure-theoretic `InformationTheory.klDiv`. A nonnegative function on a finite discrete type is
represented as a measure by taking the counting measure with that function as density.

## Main definitions

* `pmfMeasure`: The discrete measure whose mass at `i` is `p i`.

## Main results

* `pmfMeasure_eq_withDensity`: Under absolute continuity, `pmfMeasure p` has density `p / q`
  with respect to `pmfMeasure q`.
* `toReal_klDiv_pmfMeasure_eq_klFin`: For equal-mass nonnegative functions satisfying absolute
  continuity, `klDiv` of the associated discrete measures is `klFin`.
-/

@[expose] public section

namespace InformationTheory

open scoped ENNReal
open MeasureTheory Real Set

variable {I : Type*} [Fintype I]
local instance : MeasurableSpace I := ⊤

omit [Fintype I] in
/-- The measure with mass `p i` at each point `i`, implemented as `count.withDensity`. -/
noncomputable def pmfMeasure (p : I → ℝ) : Measure I :=
  Measure.count.withDensity (fun i => ENNReal.ofReal (p i))

/-- Absolute continuity of mass functions passes to their associated discrete measures. -/
lemma pmfMeasure_ac {I : Type*} {p q : I → ℝ} (hq : ∀ i, 0 ≤ q i)
    (hac : ∀ i, q i = 0 → p i = 0) :
    pmfMeasure p ≪ pmfMeasure q := by
  intro s hs0
  rw [pmfMeasure, withDensity_apply_eq_zero (Measurable.of_discrete)] at hs0 ⊢
  refine measure_mono_null ?_ hs0
  rintro i ⟨hpi, his⟩
  refine ⟨?_, his⟩
  intro hqi
  have hq0 : q i = 0 := le_antisymm (ENNReal.ofReal_eq_zero.mp hqi) (hq i)
  exact hpi (by simp [hac i hq0])

/-- Under absolute continuity, the measure associated to `p` is obtained from the one associated
to `q` by taking density `p / q`. -/
lemma pmfMeasure_eq_withDensity {p q : I → ℝ} (hq : ∀ i, 0 ≤ q i)
    (hac : ∀ i, q i = 0 → p i = 0) :
    pmfMeasure p = (pmfMeasure q).withDensity (fun i => ENNReal.ofReal (p i / q i)) := by
  apply Measure.ext_of_singleton
  intro i
  by_cases hqi : q i = 0
  · simp [pmfMeasure, hqi, hac i hqi]
  · have hq_pos : 0 < q i := lt_of_le_of_ne (hq i) (Ne.symm hqi)
    change Measure.count.withDensity (fun i => ENNReal.ofReal (p i)) {i} =
      (Measure.count.withDensity (fun i => ENNReal.ofReal (q i))).withDensity
        (fun i => ENNReal.ofReal (p i / q i)) {i}
    rw [withDensity_apply _ (MeasurableSet.singleton i),
      withDensity_apply _ (MeasurableSet.singleton i),
      setLIntegral_withDensity_eq_setLIntegral_mul Measure.count (by fun_prop) (by fun_prop)
        (MeasurableSet.singleton i)]
    simp
    rw [← ENNReal.ofReal_mul hq_pos.le]
    congr 1
    field_simp

instance (p : I → ℝ) : IsFiniteMeasure (pmfMeasure p) :=
  ⟨by simp [pmfMeasure, lintegral_count]⟩

/-- The integral of the log-likelihood ratio of discrete measures is the corresponding finite
sum for nonnegative mass functions satisfying absolute continuity. -/
lemma integral_llr_pmfMeasure {p q : I → ℝ}
    (hp_nonneg : ∀ i, 0 ≤ p i) (hq_nonneg : ∀ i, 0 ≤ q i)
    (hac : ∀ i, q i = 0 → p i = 0) :
    (∫ x, llr (pmfMeasure p) (pmfMeasure q) x ∂(pmfMeasure p)) =
      ∑ i, p i * log (p i / q i) := by
  let μ : Measure I := pmfMeasure p
  let ν : Measure I := pmfMeasure q
  have hμν : μ ≪ ν := pmfMeasure_ac hq_nonneg hac
  have hμ_eq : μ = ν.withDensity (fun i => ENNReal.ofReal (p i / q i)) := by
    simpa [μ, ν] using pmfMeasure_eq_withDensity hq_nonneg hac
  have h_rn_μν : μ.rnDeriv ν =ᵐ[μ] fun i => ENNReal.ofReal (p i / q i) := by
    apply hμν
    rw [hμ_eq]
    exact Measure.rnDeriv_withDensity ν Measurable.of_discrete
  have h_llr : llr μ ν =ᵐ[μ] fun i => log (p i / q i) := by
    filter_upwards [h_rn_μν] with i hi
    simp [MeasureTheory.llr_def, hi, div_nonneg (hp_nonneg i) (hq_nonneg i)]
  calc
    (∫ x, llr μ ν x ∂μ) = ∫ x, log (p x / q x) ∂μ := integral_congr_ae h_llr
    _ = ∑ i, p i * log (p i / q i) := by
      simpa [μ, pmfMeasure, hp_nonneg] using
        integral_withDensity_eq_integral_toReal_smul
          (μ := Measure.count) (f := fun i : I => ENNReal.ofReal (p i))
          (g := fun i => log (p i / q i)) (by simp [Measurable]) (by simp)

/-- The total mass of the discrete measure associated to a nonnegative function is its sum. -/
lemma pmfMeasure_univ {p : I → ℝ} (hp_nonneg : ∀ i, 0 ≤ p i) :
    pmfMeasure p univ = ENNReal.ofReal (∑ i, p i) := by
  calc
    pmfMeasure p univ = ∑ i, ENNReal.ofReal (p i) := by
      simp [pmfMeasure, lintegral_count]
    _ = ENNReal.ofReal (∑ i, p i) := by
      simpa using (ENNReal.ofReal_sum_of_nonneg (fun i _ => hp_nonneg i)).symm

/-- The bridge between `klFin` and mathlib's measure-theoretic `klDiv`: for equal-mass
nonnegative functions satisfying absolute continuity, the two definitions agree on the associated
measures. -/
theorem toReal_klDiv_pmfMeasure_eq_klFin {p q : I → ℝ}
    (hp_nonneg : ∀ i, 0 ≤ p i) (hq_nonneg : ∀ i, 0 ≤ q i)
    (hac : ∀ i, q i = 0 → p i = 0) (hmass : ∑ i, p i = ∑ i, q i) :
    (klDiv (pmfMeasure p) (pmfMeasure q)).toReal = klFin p q := by
  rw [toReal_klDiv_of_measure_eq (pmfMeasure_ac hq_nonneg hac)]
  · exact integral_llr_pmfMeasure hp_nonneg hq_nonneg hac
  · rw [pmfMeasure_univ hp_nonneg, pmfMeasure_univ hq_nonneg, hmass]

end InformationTheory
