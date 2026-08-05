/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
import InformationTheory.Coding.SourceCodingLowerBound

/-!
# Maximum-entropy attainment on the uniform law

This file records the max-entropy attainment fact underlying
`InformationTheory.entropy_le_logb_card` (which only bounds entropy above by
`logb D (Fintype.card I)`, without exhibiting a law that attains it): the uniform law on a
nonempty finite type attains exactly that bound, and `T` fresh independent uniform draws carry
entropy growing exactly linearly in `T`, without any horizon-free cap.

Ported from the GameTheory experiments layer (probe E57, verified 2026-08-05), consolidating
previously duplicated local definitions. This file deliberately does **not** port the
`seedBudget` theorems from the source (`seedBudget`, `seedBudget_le_logb_card`, and the
`tupleLaw` definition they use): those stay as a downstream worked example built on top of
`entropy_uniform` and `InformationTheory.entropy_push_le`, rather than as library-level results.

## Main results

* `entropy_uniform` : the entropy of the uniform law on a finite type `B` is exactly
  `logb D (Fintype.card B)`.
* `freshStream_entropy_linear` : instantiating `entropy_uniform` at `T` fresh independent uniform
  draws from a finite type `G` gives entropy exactly `T * logb D (Fintype.card G)` — linear in
  the horizon.

## Nonclaims

* **No seed-budget statement.** The source's contrasting fence — that a deterministic stream
  driven by a hidden finite seed carries at most `entropy D σ` bits at *every* horizon, uniformly
  in `T` — is not ported here; only the linearly-growing regime that the contrast was drawn
  against is.
* **Exact uniformity only.** `freshStream_entropy_linear` assumes *exact* uniformity of each
  fresh draw, not merely high min-entropy or approximate uniformity.

## References

`experiments/SeedEntropyBudget.lean` (probe E57); `InformationTheory.entropy_le_logb_card` in
`InformationTheory/Entropy/ConditionalEntropy.lean`.
-/

namespace InformationTheory

/-! ## Maximum-entropy attainment -/

variable {B : Type*} [Fintype B] [Nonempty B]

/-- The entropy of the uniform law on a nonempty finite type is exactly `logb D` of its
cardinality. -/
theorem entropy_uniform (D : ℕ) :
    entropy D (fun _ : B => (Fintype.card B : ℝ)⁻¹)
      = Real.logb D (Fintype.card B) := by
  have hn_ne : (Fintype.card B : ℝ) ≠ 0 := by
    have := Fintype.card_pos (α := B)
    positivity
  have hterm : Real.negMulLog ((Fintype.card B : ℝ)⁻¹)
      = (Fintype.card B : ℝ)⁻¹ * Real.log (Fintype.card B) := by
    unfold Real.negMulLog
    rw [Real.log_inv]
    ring
  have hsum : (∑ _i : B, Real.negMulLog ((Fintype.card B : ℝ)⁻¹))
      = Real.log (Fintype.card B) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hterm, ← mul_assoc,
      mul_inv_cancel₀ hn_ne, one_mul]
  unfold entropy Real.logb
  rw [hsum]

/-! ## The contrast: fresh contributions grow linearly -/

variable {G : Type*} [Fintype G] [Nonempty G]

/-- **Fresh contributions grow linearly.** The uniform law on `T` fresh independent draws from
a finite type `G` has entropy exactly `T * logb D (Fintype.card G)`: linear in the horizon,
without any horizon-free cap. -/
theorem freshStream_entropy_linear (D : ℕ) (T : ℕ) :
    entropy D (fun _ : Fin T → G => ((Fintype.card G : ℝ) ^ T)⁻¹)
      = (T : ℝ) * Real.logb D (Fintype.card G) := by
  have hcard : Fintype.card (Fin T → G) = Fintype.card G ^ T := Fintype.card_pi_const G T
  have huniform := entropy_uniform (B := Fin T → G) D
  rw [hcard] at huniform
  push_cast at huniform
  rw [huniform, Real.logb_pow]

end InformationTheory
