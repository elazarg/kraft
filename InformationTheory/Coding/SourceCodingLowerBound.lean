/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.InformationTheory.KullbackLeibler.Basic

import InformationTheory.Coding.Kraft

/-!
# Source Coding Lower Bound

This file proves that Shannon entropy is a lower bound on the expected codeword length
for any uniquely decodable code. This is the converse direction of Shannon's source
coding theorem.

## Main definitions

* `pmfMeasure`: Converts a probability mass function `p : I → ℝ` to a finite measure.
* `entropy`: Shannon entropy `H(p) = -∑ p(i) log p(i)` in base `D`.
* `expLength`: Expected codeword length `E[L] = ∑ p(i) * |w(i)|`.

## Main results

* `gibbs_sum_log_ratio_nonneg`: The discrete Gibbs inequality: for probability distributions
  `p` and `q`, we have `∑ p(i) log(p(i)/q(i)) ≥ 0` (non-negativity of KL divergence).
* `source_coding_lower_bound`: For any uniquely decodable code over an alphabet of size `D`,
  the expected codeword length is at least the entropy: `H_D(p) ≤ E[L]`.

## Implementation notes

The proof uses the Gibbs inequality applied to the probability distribution `p` and the
normalized Kraft weights `q(i) = D^{-|w(i)|} / K` where `K = ∑ D^{-|w(i)|}` is the Kraft sum.
The Kraft-McMillan inequality ensures `K ≤ 1`, which makes `log K ≤ 0` and allows us to
drop this term in the final inequality.

## References

* Cover & Thomas, *Elements of Information Theory*, Chapter 5
-/

namespace InformationTheory

open scoped BigOperators ENNReal
open MeasureTheory Real Set

section DiscreteKL

variable {I : Type*} [Fintype I]
local instance : MeasurableSpace I := ⊤

/-- The finite measure with mass `p i` at each point `i`, implemented as `count.withDensity`. -/
noncomputable def pmfMeasure (p : I → ℝ) : Measure I :=
  Measure.count.withDensity (fun i => ENNReal.ofReal (p i))

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
      simpa [pmfMeasure] using this
    exact ne_of_gt (lt_of_lt_of_le hpos_singleton hle) hs0
  simp [hs_empty]

instance (p : I → ℝ) : IsFiniteMeasure (pmfMeasure p) := by
  exact ⟨by simp [pmfMeasure, lintegral_count]⟩

lemma integral_llr_pmfMeasure {p q : I → ℝ}
  (hp_pos : ∀ i, 0 < p i)
  (hq_pos : ∀ i, 0 < q i) :
  (∫ x, llr (pmfMeasure p) (pmfMeasure q) x ∂(pmfMeasure p)) = ∑ i, p i * log (p i / q i) := by
  let ρ : Measure I := Measure.count
  let μ : Measure I := pmfMeasure p
  let ν : Measure I := pmfMeasure q

  have hμρ : μ ≪ ρ := by
    simpa [μ, pmfMeasure] using
      (withDensity_absolutelyContinuous (μ := ρ) (f := fun i => ENNReal.ofReal (p i)))

  have h_rn_μρ : μ.rnDeriv ρ =ᵐ[ρ] fun i => ENNReal.ofReal (p i) := by
    simpa [μ, pmfMeasure] using (Measure.rnDeriv_withDensity (ν := ρ) (fun i => by simp))

  have h_rn_μν_ρ :
      μ.rnDeriv ν =ᵐ[ρ] fun i =>
        (ENNReal.ofReal (q i))⁻¹ * (ENNReal.ofReal (p i)) := by
    have hf : AEMeasurable (fun i => ENNReal.ofReal (q i)) ρ :=
      (Measurable.of_discrete : Measurable (fun i : I => ENNReal.ofReal (q i))).aemeasurable
    have h := Measure.rnDeriv_withDensity_right (μ := μ) (ν := ρ) hf (by simp [ρ]; grind) (by simp [ρ])
    filter_upwards [h, h_rn_μρ] with i hi hip
    simpa [hip] using hi

  have h_llr :
      llr μ ν  =ᵐ[μ] fun i => log (p i / q i) := by
    filter_upwards [hμρ h_rn_μν_ρ] with i hi
    simp [MeasureTheory.llr_def, hi, div_eq_mul_inv, le_of_lt (hp_pos i), le_of_lt (hq_pos i), CommMonoid.mul_comm]

  calc
    (∫ x, llr μ ν x ∂μ)
        = ∫ x, log (p x / q x) ∂μ := by
            refine integral_congr_ae ?_
            simpa using h_llr
    _ = ∑ i, p i * log (p i / q i) := by
          simpa [μ, fun i => le_of_lt (hp_pos i)]
            using integral_withDensity_eq_integral_toReal_smul
              (μ := Measure.count)
              (f := fun i : I => ENNReal.ofReal (p i))
              (g := fun i => log (p i / q i))
              (by simp [Measurable])
              (by simp)

lemma pmfMeasure_univ_eq_of_sum_eq_one {p : I → ℝ}
    (hp_nonneg : ∀ i, 0 ≤ p i)
    (hp_sum : ∑ i, p i = 1) :
    pmfMeasure p univ = 1 := by
  calc
    pmfMeasure p univ
      = ∑ i, ENNReal.ofReal (p i) := by simp [pmfMeasure, lintegral_count]
    _ = ENNReal.ofReal (∑ i, p i) := by
          simpa using (ENNReal.ofReal_sum_of_nonneg (fun i _ => hp_nonneg i)).symm
    _ = 1 := by simp [hp_sum]

/-- Finite Gibbs inequality for strictly positive pmfs.
This is the bridge from the measure-theoretic `llr` lemma to a `Finset.sum` statement. -/
lemma gibbs_sum_log_ratio_nonneg
    {p q : I → ℝ}
    (hp_pos : ∀ i, 0 < p i) (hp_sum : ∑ i, p i = 1)
    (hq_pos : ∀ i, 0 < q i) (hq_sum : ∑ i, q i = 1) :
    0 ≤ ∑ i, p i * log (p i / q i) := by
  let μ : Measure I := pmfMeasure p
  let ν : Measure I := pmfMeasure q
  have hμν : μ ≪ ν := pmfMeasure_ac hq_pos

  have h_integral :
      (∫ x, llr μ ν x ∂μ) = ∑ i, p i * log (p i / q i) :=
    integral_llr_pmfMeasure hp_pos hq_pos

  have hmass : μ univ = ν univ := by
    have hμ : μ univ = 1 := pmfMeasure_univ_eq_of_sum_eq_one (fun i => le_of_lt (hp_pos i)) hp_sum
    have hν : ν univ = 1 := pmfMeasure_univ_eq_of_sum_eq_one (fun i => le_of_lt (hq_pos i)) hq_sum
    simp [hμ, hν]

  have hk : 0 ≤ (klDiv μ ν).toReal := by simp
  simpa [h_integral, toReal_klDiv_of_measure_eq hμν hmass] using hk

end DiscreteKL

section SourceCodingLower

lemma sum_normalized {I : Type*} [Fintype I] (K : ℝ) (a : I → ℝ) :
    (∑ i, (1 / K) * a i) = (1 / K) * (∑ i, a i) := by
  simp [Finset.mul_sum]

open Real

variable {I : Type*} [Fintype I] [Nonempty I]
variable {D : ℕ}

noncomputable def entropy (D : ℕ) (p : I → ℝ) : ℝ :=
  (∑ i, Real.negMulLog (p i)) / log D

noncomputable def expLength (p : I → ℝ) (w : I → List (Fin D)) : ℝ :=
  ∑ i, p i * ((w i).length : ℝ)

/-
We assume hp_pos : ∀ i, 0 < p i. That's stronger than what source coding typically needs
(usually 0 ≤ p i, sum=1, plus convention 0*log 0 = 0).
The route via pmfMeasure_ac and the llr algebra is what forces the strict positivity.

TODO:
Relax strict positivity by
(1) keeping p i ≥ 0, ∑ p = 1, and using the convention Real.negMulLog 0 = 0 (already true), and
(2) handling the KL/Gibbs step with an a.e. statement:
prove llr μ ν = log(p/q) only on the set {i | p i > 0 ∧ q i > 0},
and show the complement is μ-null (because μ {i | p i = 0} = 0).

Practically, we either truncate to the support s := {i | p i > 0} (work on s as a finite type)
or regularize with q_ε := (1-ε) q + ε r for a strictly positive r,
prove the bound for q_ε, then take ε → 0 using continuity/monotone convergence
to recover the non-strict case.
-/
theorem source_coding_lower_bound
    (hD : 1 < D)
    (p : I → ℝ)
    (hp_pos : ∀ i, 0 < p i)
    (hp_sum : ∑ i, p i = 1)
    (w : I → List (Fin D))
    (hw : Function.Injective w)
    (hud : UniquelyDecodable (Set.range w)) :
    entropy D p ≤ expLength p w := by
  let L : I → ℕ := fun i => (w i).length
  let K : ℝ := ∑ i, (1 / (D : ℝ)) ^ (L i)
  have hK_pos : 0 < K := by positivity
  have hD0 : 0 < (D : ℝ) := by
    exact_mod_cast (lt_trans Nat.zero_lt_one hD)
  -- Define q = normalized Kraft weights
  let q (i : I) : ℝ := (1 / K) * (1 / (D : ℝ)) ^ (L i)
  -- Key pointwise rewrite: p/q = p * K * D^(L i)
  have hgibbs' :
      0 ≤ ∑ i, p i * log (p i) + log K * ∑ i, p i + log D * ∑ i, p i * L i := by
    have hq_sum := calc
            ∑ i, q i
          = 1 / K * K := by simp [q, K, Finset.mul_sum]
        _ = 1 := by simp [ne_of_gt hK_pos]
    have hq_pos : ∀ i, 0 < q i := by
      intro i
      have : 0 < (1 / (D : ℝ)) ^ (L i) := by positivity
      have : 0 < (1 / K) := by positivity
      nlinarith
    have hgibbs :
        0 ≤ ∑ i, p i * log (p i / q i) := by
      simpa using gibbs_sum_log_ratio_nonneg hp_pos hp_sum hq_pos hq_sum
    have h_log_p_div_q (i : I) := by
      calc  log (p i / q i)
        _ = log (p i * (K * D ^ L i)) := by simp [q, div_eq_mul_inv, mul_comm]
        _ = log (p i) + log (K * D ^ L i) := by
              have hp0 : 0 < p i := hp_pos i
              exact log_mul (by positivity) (by positivity)
        _ = log (p i) + (log K + log (D ^ L i)) := by
              simpa using Real.log_mul (ne_of_gt hK_pos) (ne_of_gt (pow_pos hD0 _))
        _ = log (p i) + log K + L i * log D := by
              simp [log_pow, add_left_comm, add_comm]
    simp_rw [h_log_p_div_q] at hgibbs
    calc
      0 ≤ (∑ i, p i * log (p i))
          + (∑ i, p i * log K)
          + (∑ i, p i * (L i * log D)) := by
              simpa [Finset.sum_add_distrib, mul_add] using hgibbs
      _ = (∑ i, p i * log (p i))
          + (log K * ∑ i, p i)
          + (log D * ∑ i, p i * L i) := by
              have h2 := calc
                        ∑ i, p i * log K
                      = ∑ i, log K * p i := by simp [mul_comm]
                  _   = log K * ∑ i, p i := by simpa using
                            ((Finset.mul_sum (s := (Finset.univ : Finset I))
                              (a := log K) (f := fun i : I => p i))).symm
              have h3 := calc
                        ∑ i, p i * (L i * log D)
                      = ∑ i, log D * (p i * L i) := by
                          simp [mul_assoc, mul_comm]
                  _   = log D * (∑ i, p i * L i) := by
                          simpa using
                            (Finset.mul_sum (s := (Finset.univ : Finset I))
                              (a := log D) (f := fun i : I => p i * L i)).symm
              simp [h2, h3, add_assoc]
  -- Convert to the usual `∑ -p log p ≤ logD * E[L] + logK`
  have h_negMulLog_le := calc
            ∑ i, negMulLog (p i)
          = - (∑ i, p i * log (p i)) := by simp [negMulLog]
      _ ≤ log K + log D * (∑ i, p i * L i) := by
            have : 0 ≤ ∑ i, p i * log (p i) + log K + log D * ∑ i, p i * (L i : ℝ) := by
              simpa [hp_sum] using hgibbs'
            linarith
      _ = log D * expLength p w + log K := by simp [expLength, L, add_comm]
  have hlogD_pos : 0 < log D := by
    have : 1 < (D : ℝ) := by exact_mod_cast hD
    simpa using log_pos this
  -- log K ≤ 0 from K ≤ 1 and K > 0
  have hlogK_le0 : log K ≤ 0 := by
    have hK_le_one : K ≤ 1 := by
      calc K
        = ∑ c ∈ Finset.univ.image w, (1 / (D : ℝ)) ^ c.length := by
              simp [K, L]
              simp_all only [Finset.coe_univ, injOn_univ, Finset.sum_image]
        _ ≤ 1 := by
              have hudS : UniquelyDecodable (Finset.univ.image w : Set (List (Fin D))) := by
                simp [hud]
              haveI : Nonempty (Fin D) := ⟨⟨0, by positivity⟩⟩
              simpa using kraft_mcmillan_inequality hudS
    simpa using log_le_log hK_pos hK_le_one
  -- Now show `log K / log D ≤ 0` and conclude
  have hlogK_div_le0 : log K / log D ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hlogK_le0 (by positivity)
  calc entropy D p
       ≤ (log D * expLength p w + log K) / log D :=
            div_le_div_of_nonneg_right h_negMulLog_le (le_of_lt hlogD_pos)
    _  = expLength p w + log K / log D := by
            simp [add_div, ne_of_gt hlogD_pos]
    _ ≤ expLength p w := by linarith

end SourceCodingLower

end InformationTheory
