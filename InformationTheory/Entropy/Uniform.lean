/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import InformationTheory.Entropy.Basic

/-!
# Maximum-entropy attainment on the uniform law

This file records the max-entropy attainment fact underlying
`entropy_le_logb_card` (which only bounds entropy above by
`logb D (Fintype.card I)`, without exhibiting a law that attains it): the uniform law on a
nonempty finite type attains exactly that bound. Instantiating this at the tuple type `Fin T → G`
gives the entropy of the uniform law on `T`-tuples, which grows exactly linearly in `T` — this
coincides with what `T` independent fresh uniform draws would give, but note the formalization:
it is the entropy of the single uniform law on `Fin T → G`, not a statement about a product of
`T` independent per-step laws (contrast `klFin_productLaw` in
`Divergence.Tensorization`, which does formalize independence explicitly via `productLaw`).

## Main results

* `entropy_uniform` : the entropy of the uniform law on a finite type `B` is exactly
  `logb D (Fintype.card B)`.
* `freshStream_entropy_linear` : `entropy_uniform` instantiated at `B := Fin T → G`, giving
  entropy exactly `T * logb D (Fintype.card G)` for the uniform law on `T`-tuples — linear in
  the horizon, without any horizon-free cap.

## Nonclaims

* **No independence structure.** `freshStream_entropy_linear` is a cardinality computation on
  the uniform law of a single tuple type, not a product-of-laws statement; it does not formalize
  "independent draws" the way `Divergence.Tensorization.klFin_productLaw` does.
* **No seed-budget statement.** The contrasting fence — that a deterministic stream driven by a
  hidden finite seed carries at most `entropy D σ` bits at *every* horizon, uniformly in `T` — is
  not in this file; only the linearly-growing regime that such a contrast would be drawn against
  is.
* **Exact uniformity only.** `freshStream_entropy_linear` assumes *exact* uniformity, not merely
  high min-entropy or approximate uniformity.

## References

`entropy_le_logb_card` in `InformationTheory/Entropy/ConditionalEntropy.lean`.
-/

public section

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
