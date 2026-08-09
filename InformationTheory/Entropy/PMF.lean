/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import InformationTheory.Entropy.Basic

/-!
# Entropy of a Probability Mass Function

This file adapts the elementary real-valued finite entropy API to mathlib's `PMF`. It is kept
separate from `InformationTheory.Entropy.Basic` so users of finite sums do not need to import the
probability-measure hierarchy.

## Main definitions

* `entropyPMF`: Shannon entropy of a finite `PMF`.

## Main results

* `PMF.sum_toReal`: The real masses of a finite `PMF` sum to one.
* `entropyPMF_nonneg`: Entropy of a finite `PMF` is nonnegative.
* `entropyPMF_eq_zero_iff`: Entropy is zero exactly for a point mass.
-/

@[expose] public section

variable {I : Type*} [Fintype I]

namespace PMF

/-- The real masses of a finite probability mass function sum to one. -/
@[simp] theorem sum_toReal (p : PMF I) : ∑ i, (p i).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun i _ => p.apply_ne_top i)]
  have hsum : ∑ i, p i = 1 := by simpa using p.tsum_coe
  simp [hsum]

end PMF

namespace InformationTheory

/-- Entropy of a finite probability mass function, measured in base-`D` digits. -/
noncomputable def entropyPMF (D : ℕ) (p : PMF I) : ℝ :=
  entropy D fun i => (p i).toReal

/-- Entropy of a finite probability mass function is nonnegative. -/
theorem entropyPMF_nonneg (D : ℕ) (hD : 1 < D) (p : PMF I) :
    0 ≤ entropyPMF D p :=
  entropy_nonneg D hD (fun _ => ENNReal.toReal_nonneg) p.sum_toReal.le

/-- A finite probability mass function has zero entropy exactly when one point has mass one. -/
theorem entropyPMF_eq_zero_iff (D : ℕ) (hD : 1 < D) (p : PMF I) :
    entropyPMF D p = 0 ↔ ∃ i, p i = 1 := by
  rw [entropyPMF, entropy_eq_zero_iff D hD (fun _ => ENNReal.toReal_nonneg) p.sum_toReal]
  simp only [ENNReal.toReal_eq_one_iff]

/-- A finite probability mass function has zero entropy exactly when its support is a singleton. -/
theorem entropyPMF_eq_zero_iff_support_singleton (D : ℕ) (hD : 1 < D) (p : PMF I) :
    entropyPMF D p = 0 ↔ ∃ i, p.support = {i} := by
  rw [entropyPMF_eq_zero_iff D hD p]
  simp only [p.apply_eq_one_iff]

end InformationTheory
