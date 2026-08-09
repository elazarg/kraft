/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.InformationTheory.Coding.UniquelyDecodable
public import InformationTheory.Entropy.Basic
import Mathlib.InformationTheory.Coding.KraftMcMillan

/-!
# Source Coding Lower Bound

This file proves that Shannon entropy is a lower bound on the expected codeword length
for any uniquely decodable code. This is the converse direction of Shannon's source
coding theorem. `entropy` itself, and the zero-mass-tolerant Gibbs inequality, live in
`InformationTheory.Entropy.Basic` — neither has anything to do with codes, so they don't belong
here; this file is genuinely just the source-coding-specific content built on top of them.

## Main definitions

* `expectedLength`: Expected codeword length `E[L] = ∑ p(i) * |w(i)|`.

## Main results

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

@[expose] public section

namespace InformationTheory

open Real Set

section SourceCodingLower

open Real

variable {I : Type*} [Fintype I]

/-- Expected codeword length under the weights `p`. -/
noncomputable def expectedLength {α : Type*} (p : I → ℝ) (w : I → List α) : ℝ :=
  ∑ i, p i * ((w i).length : ℝ)

/-- The source-coding lower bound: the entropy of a source is at most the expected length of
any injective uniquely decodable code over a finite nontrivial alphabet. -/
theorem source_coding_lower_bound
    {α : Type*} [Fintype α] [Nontrivial α]
    (p : I → ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i)
    (hp_sum : ∑ i, p i = 1)
    (w : I → List α)
    (hw : Function.Injective w)
    (hud : UniquelyDecodable (Set.range w)) :
    entropy (Fintype.card α) p ≤ expectedLength p w := by
  classical
  let D := Fintype.card α
  change entropy D p ≤ expectedLength p w
  have hD : 1 < D := Fintype.one_lt_card
  letI : Nonempty I := not_isEmpty_iff.mp fun hI => by
    letI := hI
    simp at hp_sum
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
      exact gibbs_sum_log_ratio_nonneg_of_ac hp_nonneg hp_sum (fun i => (hq_pos i).le)
        hq_sum.le fun i hi => ((hq_pos i).ne' hi).elim
    have h_gibbs_term (i : I) :
        p i * log (p i / q i) =
          p i * log (p i) + p i * log K + p i * (L i * log D) := by
      have hlogq : log (q i) = -log K - L i * log D := by
        rw [show q i = (1 / K) * (1 / (D : ℝ)) ^ L i by rfl,
          Real.log_mul (by positivity) (by positivity), log_pow]
        simp [one_div]
        ring
      rw [mul_log_div_of_ac (hp_nonneg i) (hq_pos i).le
        (fun hi => ((hq_pos i).ne' hi).elim), hlogq]
      ring
    simp_rw [h_gibbs_term] at hgibbs
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
      _ = log D * expectedLength p w + log K := by simp [expectedLength, L, add_comm]
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
              have hudS : UniquelyDecodable (Finset.univ.image w : Set (List α)) := by
                simp [hud]
              simpa [D] using kraft_mcmillan_inequality hudS
    simpa using log_le_log hK_pos hK_le_one
  -- Now show `log K / log D ≤ 0` and conclude
  have hlogK_div_le0 : log K / log D ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hlogK_le0 (by positivity)
  calc entropy D p
       ≤ (log D * expectedLength p w + log K) / log D :=
            div_le_div_of_nonneg_right h_negMulLog_le (le_of_lt hlogD_pos)
    _  = expectedLength p w + log K / log D := by
            simp [add_div, ne_of_gt hlogD_pos]
    _ ≤ expectedLength p w := by linarith

end SourceCodingLower

end InformationTheory
