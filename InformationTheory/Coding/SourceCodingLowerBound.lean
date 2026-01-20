import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

import InformationTheory.Coding.Kraft

namespace InformationTheory

open scoped BigOperators ENNReal
open MeasureTheory Real Set

section DiscreteKL

variable {I : Type*} [Fintype I]
local instance : MeasurableSpace I := ⊤

/-- The finite measure with mass `p i` at each point `i`, implemented as `count.withDensity`. -/
noncomputable def pmfMeasure (p : I → ℝ) : Measure I :=
  Measure.count.withDensity (fun i => ENNReal.ofReal (p i))

lemma pmfMeasure_singleton {I : Type*} {p : I → ℝ} {i : I} :
    pmfMeasure p {i} = ENNReal.ofReal (p i) := by
  simp [pmfMeasure]

lemma pmfMeasure_univ {p : I → ℝ} :
    pmfMeasure p univ = ∑ i, ENNReal.ofReal (p i) := by
  simp [pmfMeasure, lintegral_count]

/-- If `q i > 0` for all i, then `pmfMeasure p ≪ pmfMeasure q`. -/
lemma pmfMeasure_ac {I : Type*} {p q : I → ℝ} (hq : ∀ i, 0 < q i) :
    pmfMeasure p ≪ pmfMeasure q := by
  intro s hs0
  have hs_empty : s = ∅ := by
    by_contra hne
    have hsne : s.Nonempty := Set.nonempty_iff_ne_empty.2 hne
    rcases hsne with ⟨i, his⟩
    have hle : pmfMeasure q {i} ≤ pmfMeasure  q s :=
      measure_mono (by
        intro x hx
        have : x = i := by simpa [Set.mem_singleton_iff] using hx
        simpa [this] using his)
    have hpos_singleton : 0 < pmfMeasure q {i} := by
      have : 0 < ENNReal.ofReal (q i) := ENNReal.ofReal_pos.mpr (hq i)
      simpa [pmfMeasure_singleton] using this
    exact ne_of_gt (lt_of_lt_of_le hpos_singleton hle) hs0
  simp [hs_empty]

lemma lintegral_count_ofReal_toReal_eq_sum
    (p : I → ℝ) (hp0 : ∀ i, 0 ≤ p i) :
    (∫⁻ i : I, ENNReal.ofReal (p i) ∂Measure.count).toReal = ∑ i, p i := by
  calc
    (∫⁻ i : I, ENNReal.ofReal (p i) ∂Measure.count).toReal
        = (∑ i, ENNReal.ofReal (p i)).toReal := by simp [lintegral_count]
    _ = ∑ i, (ENNReal.ofReal (p i)).toReal := by
          simpa using (ENNReal.toReal_sum (f := fun i => ENNReal.ofReal (p i)))
    _ = ∑ i, p i := by
          apply Finset.sum_congr rfl
          intro i _
          exact (ENNReal.toReal_ofReal (hp0 i))

lemma pmfMeasure_real_univ (p : I → ℝ) (hp0 : ∀ i, 0 ≤ p i) :
    (pmfMeasure (I := I) p).real univ = ∑ i, p i := by
  -- `μ.real s = (μ s).toReal`
  simp [measureReal_def, pmfMeasure_univ]  -- reduces to toReal of the ENNReal sum
  have h_ofReal :
      (∑ i, ENNReal.ofReal (p i)) = ENNReal.ofReal (∑ i, p i) :=
    (ENNReal.ofReal_sum_of_nonneg (fun i _ => hp0 i)).symm
  calc
    (∑ i, ENNReal.ofReal (p i)).toReal
        = (ENNReal.ofReal (∑ i, p i)).toReal := by simp [h_ofReal]
    _ = ∑ i, p i := by
          refine ENNReal.toReal_ofReal ?_
          exact Finset.sum_nonneg (fun i _ => hp0 i)

instance (p : I → ℝ) : IsFiniteMeasure (pmfMeasure p) := by
  exact ⟨by simp [pmfMeasure_univ]⟩

lemma integral_pmfMeasure (p : I → ℝ) (hp0 : ∀ i, 0 ≤ p i) (f : I → ℝ) :
    (∫ i, f i ∂pmfMeasure (I := I) p) = ∑ i, p i * f i := by
  -- Step 1: push `withDensity` through the integral (ENNReal density -> toReal smul)
  have h_wd :
      (∫ i, f i ∂(Measure.count.withDensity (fun i : I => ENNReal.ofReal (p i))))
        =
      (∫ i, ((ENNReal.ofReal (p i)).toReal) • f i ∂Measure.count) := by
    simpa using
      (integral_withDensity_eq_integral_toReal_smul
        (μ := Measure.count)
        (f := fun i : I => ENNReal.ofReal (p i))
        (g := f)
        (by simp [Measurable])
        (by simp))

  -- Step 2: rewrite the scalar action to multiplication and cancel `toReal (ofReal _)`
  have h_smul :
      (fun i : I => ((ENNReal.ofReal (p i)).toReal) • f i)
        = fun i : I => p i * f i := by
    funext i
    -- over ℝ, `•` is multiplication
    simp [smul_eq_mul, ENNReal.toReal_ofReal (hp0 i)]
  calc
    (∫ i, f i ∂pmfMeasure (I := I) p)
        = (∫ i, f i ∂(Measure.count.withDensity (fun i : I => ENNReal.ofReal (p i)))) := by rfl
    _ = (∫ i, ((ENNReal.ofReal (p i)).toReal) • f i ∂Measure.count) := h_wd
    _ = (∫ i, (p i * f i) ∂Measure.count) := by simp_all only
    _ = ∑ i, p i * f i := by simp


/-- Finite Gibbs inequality for strictly positive pmfs.
This is the bridge from the measure-theoretic `llr` lemma to a `Finset.sum` statement. -/
lemma gibbs_sum_log_ratio_nonneg
    {p q : I → ℝ}
    (hp_pos : ∀ i, 0 < p i) (hp_sum : ∑ i, p i = 1)
    (hq_pos : ∀ i, 0 < q i) (hq_sum : ∑ i, q i = 1) :
    0 ≤ ∑ i, p i * Real.log (p i / q i) := by
  let μ : Measure I := pmfMeasure (I := I) p
  let ν : Measure I := pmfMeasure (I := I) q
  have hμν : μ ≪ ν := pmfMeasure_ac hq_pos
  have hmass : μ univ = ν univ := by
    have hμ : μ univ = (1 : ℝ≥0∞) := by
      calc
        μ univ = ∑ i, ENNReal.ofReal (p i) := by simp [μ, pmfMeasure_univ]
        _ = ENNReal.ofReal (∑ i, p i) := by
              simpa using (ENNReal.ofReal_sum_of_nonneg (by grind)).symm
        _ = 1 := by simp [hp_sum]

    have hν : ν univ = (1 : ℝ≥0∞) := by
      calc
        ν univ = ∑ i, ENNReal.ofReal (q i) := by simp [ν, pmfMeasure_univ]
        _ = ENNReal.ofReal (∑ i, q i) := by
              simpa using (ENNReal.ofReal_sum_of_nonneg (by grind)).symm
        _ = 1 := by simp [hq_sum]
    simp [hμ, hν]
  have h_toReal :
      (klDiv μ ν).toReal = ∫ x, llr μ ν x ∂μ := toReal_klDiv_of_measure_eq hμν hmass
  have h_nonneg : 0 ≤ (klDiv μ ν).toReal := by simp
  have h_integral :
      (∫ x, llr μ ν x ∂μ) = ∑ i, p i * Real.log (p i / q i) := by
    let ρ : Measure I := Measure.count
    have hμ_def : μ = ρ.withDensity (fun i => ENNReal.ofReal (p i)) := by rfl
    have hν_def : ν = ρ.withDensity (fun i => ENNReal.ofReal (q i)) := by rfl
    have h_rn_μρ :
        μ.rnDeriv ρ =ᶠ[ae ρ] (fun i : I => ENNReal.ofReal (p i)) := by
      simpa [hμ_def] using
        (Measure.rnDeriv_withDensity (ν := ρ)
          (f := fun i : I => ENNReal.ofReal (p i))
          (by exact fun _ _ ↦ trivial))
    have h_rn_μν_ρ :
        μ.rnDeriv ν =ᵐ[ρ] fun i =>
          (ENNReal.ofReal (q i))⁻¹ * (ENNReal.ofReal (p i)) := by
      have hμρ : μ ≪ ρ := by
        simpa [hμ_def] using
          (withDensity_absolutelyContinuous (μ := ρ) (f := fun i : I => ENNReal.ofReal (p i)))
      have hf_ne0 : ∀ᵐ i ∂ρ, (fun i : I => ENNReal.ofReal (q i)) i ≠ 0 := by
        simp_all only [ne_eq, ENNReal.ofReal_eq_zero, not_le, Measure.ae_count_iff, implies_true, μ, ν, ρ]
      have hf_neTop : ∀ᵐ i ∂ρ, (fun i : I => ENNReal.ofReal (q i)) i ≠ ∞ := by
        simp
      have hmeas : Measurable (fun i : I ↦ ENNReal.ofReal (q i)) :=
        (Measurable.of_discrete : Measurable (fun i : I ↦ ENNReal.ofReal (q i)))
      -- This lemma is in `Measure/RadonNikodym` (imported by `LogLikelihoodRatio` stuff).
      have h := Measure.rnDeriv_withDensity_right_of_absolutelyContinuous
        hμρ hmeas.aemeasurable hf_ne0 hf_neTop
      filter_upwards [h, h_rn_μρ] with i hi hμρi
      simpa [hν_def, hμρi, mul_assoc] using hi
    have h_rn_μν_μ :
        μ.rnDeriv ν =ᵐ[μ] fun i =>
          (ENNReal.ofReal (q i))⁻¹ * (ENNReal.ofReal (p i)) := by
      have hμρ : μ ≪ ρ := by
        simpa [hμ_def] using (withDensity_absolutelyContinuous (μ := ρ)
          (f := fun i : I => ENNReal.ofReal (p i)))
      exact hμρ h_rn_μν_ρ
    have h_llr_ae :
        (fun i => llr μ ν i) =ᵐ[μ] fun i =>
          Real.log (p i / q i) := by
      filter_upwards [h_rn_μν_μ] with i hi
      have hp0 : 0 ≤ p i := le_of_lt (hp_pos i)
      have hq0 : 0 ≤ q i := le_of_lt (hq_pos i)
      have h_toReal :
          (((ENNReal.ofReal (q i))⁻¹ * (ENNReal.ofReal (p i)))).toReal = p i / q i := by
        simp [div_eq_mul_inv, hp0, hq0]
        exact CommMonoid.mul_comm (q i)⁻¹ (p i)
      simp [MeasureTheory.llr_def, hi, h_toReal]
    calc
      (∫ x, llr μ ν x ∂μ)
          = ∫ x, Real.log (p x / q x) ∂μ := by
              refine integral_congr_ae ?_
              simpa using h_llr_ae
      _ = ∑ i, p i * Real.log (p i / q i) := by
            simpa [μ, pmfMeasure] using
              (integral_pmfMeasure p (fun i => le_of_lt (hp_pos i))
                (fun i => Real.log (p i / q i)))
  simpa [h_toReal, h_integral] using (le_trans h_nonneg (le_of_eq h_toReal))

end DiscreteKL

section SourceCodingLower

variable {I : Type*} [Fintype I] [Nonempty I]
variable {D : ℕ}

noncomputable def entropy (D : ℕ) (p : I → ℝ) : ℝ :=
  (∑ i, Real.negMulLog (p i)) / Real.log D

noncomputable def expLength (p : I → ℝ) (w : I → List (Fin D)) : ℝ :=
  ∑ i, p i * ((w i).length : ℝ)

theorem source_coding_lower_bound
    (hD : 1 < D)
    (p : I → ℝ)
    (hp_pos : ∀ i, 0 < p i)
    (hp_sum : ∑ i, p i = 1)
    (w : I → List (Fin D))
    (hw : Function.Injective w)
    (hud : UniquelyDecodable (Set.range w)) :
    entropy D p ≤ expLength p w := by
  classical
  -- Setup lengths and Kraft sum
  let L : I → ℕ := fun i => (w i).length
  let K : ℝ := ∑ i, (1 / (D : ℝ)) ^ (L i)

  have hK_pos : 0 < K := by positivity
  have hD_pos : 0 < D := by positivity

  have hK_le_one : K ≤ 1 := by
    let S : Finset (List (Fin D)) := (Finset.univ : Finset I).image w
    have hS_coe : (S : Set (List (Fin D))) = Set.range w := by
      ext x
      constructor
      · intro hx
        rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    have hudS : UniquelyDecodable (S : Set (List (Fin D))) := by
      simpa [hS_coe] using hud
    have hS_kraft :
        (∑ c ∈ S, (1 / (D : ℝ)) ^ c.length) ≤ 1 := by
      haveI : Nonempty (Fin D) := ⟨⟨0, by positivity⟩⟩
      simpa using (kraft_mcmillan_inequality hudS)
    have hK_eq : K = ∑ c ∈ S, (1 / (D : ℝ)) ^ c.length := by
      simp_all only [Finset.coe_univ, injOn_univ, Finset.sum_image, K, L, S]
    simpa [hK_eq] using hS_kraft

  -- Define q = normalized Kraft weights
  let q : I → ℝ := fun i => (1 / K) * (1 / (D : ℝ)) ^ (L i)

  have hq_pos : ∀ i, 0 < q i := by
    intro i
    have : 0 < (1 / (D : ℝ)) ^ (L i) := by positivity
    have : 0 < (1 / K) := by positivity
    nlinarith

  have hq_sum : ∑ i, q i = 1 := by
    calc
      (∑ i, q i)
          = (1 / K) * (∑ i, (1 / (D : ℝ)) ^ (L i)) := by simp [q, Finset.mul_sum]
      _ = (1 / K) * K := by simp [K]
      _ = 1 := by simp [ne_of_gt hK_pos]

  -- Apply discrete Gibbs inequality to p,q
  have hgibbs :
      0 ≤ ∑ i, p i * Real.log (p i / q i) := by
    simpa using (gibbs_sum_log_ratio_nonneg hp_pos hp_sum hq_pos hq_sum)

  -- Convert hgibbs into entropy ≤ expected length via algebra
  -- Main rewrite: q i = (1/K) * (1/D)^(L i)
  -- So: -logb D (q i) = (L i : ℝ) + logb D K.
  -- Then use logb monotonicity and K ≤ 1 to drop the `logb D K` term.

  -- STUB: the rest is algebra; do it in three helper lemmas:
  --   (1) rewrite hgibbs into: ∑ -p*logb p ≤ ∑ -p*logb q
  --   (2) rewrite RHS using q-definition into expLength + logb D K
  --   (3) show logb D K ≤ 0 from hK_le_one, then conclude
  sorry

end SourceCodingLower

end InformationTheory
