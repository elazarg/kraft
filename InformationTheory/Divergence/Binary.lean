/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The quadratic information fence for binary KL divergence

This file defines the binary Kullback-Leibler divergence directly,

`klBin q p = q * log (q / p) + (1 - q) * log ((1 - q) / (1 - p))`,

without going through Mathlib's measure-theoretic `klDiv`, and proves that it is `Θ(δ²)` in the
deviation `δ = q - p`, sandwiched between two quadratics on the open unit square: Gibbs'
inequality (`klBin_nonneg`), the sharp-constant binary Pinsker inequality
(`two_mul_sq_le_klBin`), and the chi-squared upper bound (`klBin_le_sq_div`). The symmetric-point
corollaries `le_klBin_half` and `klBin_half_le` record the clean numerical instance
`2 δ² ≤ klBin (1/2 + δ) (1/2) ≤ 4 δ²`.

Ported from the GameTheory experiments layer (probe E51, verified 2026-08-05), consolidating
previously duplicated local definitions. The helper lemma `one_sub_div_le_log_div` is exposed
(non-private, unlike its source) so that `InformationTheory.Divergence.Pinsker`'s log-sum
argument can reuse it instead of carrying its own inlined copy.

## Main definitions

* `klBin (q p : ℝ) : ℝ`, binary Kullback-Leibler divergence `KL(Bernoulli q ‖ Bernoulli p)`,
  meaningful on `p, q ∈ (0, 1)`.

## Main results

* `klBin_nonneg` : Gibbs' inequality, `0 ≤ klBin q p`.
* `two_mul_sq_le_klBin` : the binary Pinsker inequality with the sharp constant,
  `2 * (q - p) ^ 2 ≤ klBin q p`.
* `klBin_le_sq_div` : the chi-squared upper bound, `klBin q p ≤ (q - p) ^ 2 / (p * (1 - p))`.
* `le_klBin_half`, `klBin_half_le` : the symmetric-point corollaries at `p = 1/2`.

## What this file does NOT claim

* **No process-level statement.** This is a single-observation (one-shot, static) bound on two
  Bernoulli laws; no sequential detection, stopping time, or accumulated evidence appears here.
* **No detector.** No test, estimator, or decision rule is constructed or analyzed.
* **No incentive or payoff structure.** This file supplies only the information-side quadratic
  fence, not an incentive-side linear term, and does not combine the two into a finance
  inequality.

## References

`experiments/BinaryKLQuadratic.lean` (probe E51).
-/

@[expose] public section

namespace InformationTheory

/-- Binary Kullback-Leibler divergence `KL(Bernoulli q ‖ Bernoulli p)`, defined directly by its
closed form rather than through Mathlib's measure-theoretic `klDiv`. Meaningful for
`p, q ∈ (0, 1)`, but total (junk values elsewhere) so it can be applied at boundary points
`P ∈ {0, 1}` too, as `InformationTheory.Divergence.Pinsker.pinsker` does. -/
noncomputable def klBin (q p : ℝ) : ℝ :=
  q * Real.log (q / p) + (1 - q) * Real.log ((1 - q) / (1 - p))

/-- For `a, b > 0`, `Real.log (a / b) ≥ 1 - b / a`. This is `Real.log x ≤ x - 1` applied to the
reciprocal ratio `b / a`, after converting `log (a / b)` to `-log (b / a)`. It is the one-line
engine behind Gibbs' inequality below, and is reused by
`InformationTheory.Divergence.Pinsker`'s log-sum argument. -/
theorem one_sub_div_le_log_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    1 - b / a ≤ Real.log (a / b) := by
  have hba : Real.log (a / b) = -Real.log (b / a) := by
    rw [← Real.log_inv, inv_div]
  rw [hba]
  linarith [Real.log_le_sub_one_of_pos (div_pos hb ha)]

/-- Gibbs' inequality: binary KL divergence is nonnegative on the open square. -/
theorem klBin_nonneg {p q : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    0 ≤ klBin q p := by
  obtain ⟨hp0, hp1⟩ := hp
  obtain ⟨hq0, hq1⟩ := hq
  have h1p : (0:ℝ) < 1 - p := by linarith
  have h1q : (0:ℝ) < 1 - q := by linarith
  have h1 : 1 - p / q ≤ Real.log (q / p) := one_sub_div_le_log_div hq0 hp0
  have h2 : 1 - (1 - p) / (1 - q) ≤ Real.log ((1 - q) / (1 - p)) :=
    one_sub_div_le_log_div h1q h1p
  have e1 : q * (1 - p / q) = q - p := by field_simp
  have e2 : (1 - q) * (1 - (1 - p) / (1 - q)) = p - q := by field_simp; ring
  have h1' : q - p ≤ q * Real.log (q / p) := e1 ▸ mul_le_mul_of_nonneg_left h1 hq0.le
  have h2' : p - q ≤ (1 - q) * Real.log ((1 - q) / (1 - p)) :=
    e2 ▸ mul_le_mul_of_nonneg_left h2 h1q.le
  unfold klBin
  linarith

/-- The chi-squared identity behind the upper bound: `q²/p + (1-q)²/(1-p) - 1` equals
`(q - p)² / (p * (1 - p))`. -/
private theorem sq_div_add_sq_div_sub_one {p q : ℝ} (hp0 : p ≠ 0) (hp1 : (1:ℝ) - p ≠ 0) :
    q ^ 2 / p + (1 - q) ^ 2 / (1 - p) - 1 = (q - p) ^ 2 / (p * (1 - p)) := by
  field_simp
  ring

/-- Chi-squared upper bound: `klBin q p ≤ (q - p)² / (p (1 - p))`, from the termwise bound
`log x ≤ x - 1` applied to `q / p` and `(1 - q) / (1 - p)`. -/
theorem klBin_le_sq_div {p q : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    klBin q p ≤ (q - p) ^ 2 / (p * (1 - p)) := by
  obtain ⟨hp0, hp1⟩ := hp
  obtain ⟨hq0, hq1⟩ := hq
  have h1p : (0:ℝ) < 1 - p := by linarith
  have h1q : (0:ℝ) < 1 - q := by linarith
  have h1 : Real.log (q / p) ≤ q / p - 1 := Real.log_le_sub_one_of_pos (div_pos hq0 hp0)
  have h2 : Real.log ((1 - q) / (1 - p)) ≤ (1 - q) / (1 - p) - 1 :=
    Real.log_le_sub_one_of_pos (div_pos h1q h1p)
  have h1' : q * Real.log (q / p) ≤ q * (q / p - 1) := mul_le_mul_of_nonneg_left h1 hq0.le
  have h2' : (1 - q) * Real.log ((1 - q) / (1 - p)) ≤ (1 - q) * ((1 - q) / (1 - p) - 1) :=
    mul_le_mul_of_nonneg_left h2 h1q.le
  have e1 : q * (q / p - 1) = q ^ 2 / p - q := by field_simp
  have e2 : (1 - q) * ((1 - q) / (1 - p) - 1) = (1 - q) ^ 2 / (1 - p) - (1 - q) := by
    field_simp
  rw [e1] at h1'
  rw [e2] at h2'
  have hsum : klBin q p ≤ q ^ 2 / p - q + ((1 - q) ^ 2 / (1 - p) - (1 - q)) := by
    unfold klBin
    linarith
  have hid := sq_div_add_sq_div_sub_one (q := q) hp0.ne' h1p.ne'
  linarith [hsum, hid]

/-- The binary Pinsker inequality with the sharp constant `2`: `2 * (q - p)² ≤ klBin q p`. Proved
by fixing `p`, setting `F x = klBin x p - 2 * (x - p)²`, and showing `F` attains its minimum `0`
at `x = p` via a second-derivative sign argument: `F'' x = 1/x + 1/(1-x) - 4 ≥ 0` on `(0,1)`
because `x * (1 - x) ≤ 1/4` (AM-GM), so `F'` is monotone with `F' p = 0`, so `F' ≤ 0` before `p`
and `F' ≥ 0` after `p`, so `F` decreases then increases around `p`. -/
theorem two_mul_sq_le_klBin {p q : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    2 * (q - p) ^ 2 ≤ klBin q p := by
  obtain ⟨hp0, hp1⟩ := hp
  obtain ⟨hq0, hq1⟩ := hq
  have h1p : (0:ℝ) < 1 - p := by linarith
  -- The shifted function, its derivative, and its second derivative.
  set F : ℝ → ℝ := fun x =>
    x * (Real.log x - Real.log p) + (1 - x) * (Real.log (1 - x) - Real.log (1 - p))
      - 2 * (x - p) ^ 2 with hFdef
  set F' : ℝ → ℝ := fun x =>
    Real.log x - Real.log (1 - x) - (Real.log p - Real.log (1 - p)) - 4 * (x - p) with hF'def
  set F'' : ℝ → ℝ := fun x => 1 / x + 1 / (1 - x) - 4 with hF''def
  -- `F` at the deviated point recovers the goal; `F` at `p` is `0`.
  have hFq : F q = klBin q p - 2 * (q - p) ^ 2 := by
    have h1q : (0:ℝ) < 1 - q := by linarith
    simp only [hFdef, klBin]
    rw [Real.log_div hq0.ne' hp0.ne', Real.log_div h1q.ne' h1p.ne']
  have hFp : F p = 0 := by simp [hFdef]
  -- First derivative of `F`.
  have hderivF : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt F (F' x) x := by
    intro x hx
    obtain ⟨hx0, hx1⟩ := hx
    have h1x : (0:ℝ) < 1 - x := by linarith
    have hidx : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id' (𝕜 := ℝ) x
    have hlogx : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx0.ne'
    have hA := hlogx.sub_const (Real.log p)
    have hg1 := hidx.mul hA
    have hsub : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := hidx.const_sub 1
    have hB0 : HasDerivAt (fun y => Real.log (1 - y)) ((-1) / (1 - x)) x := hsub.log h1x.ne'
    have hB := hB0.sub_const (Real.log (1 - p))
    have hg2 := hsub.mul hB
    have hg3 := ((hidx.sub_const p).pow 2).const_mul (2 : ℝ)
    have hraw := (hg1.add hg2).sub hg3
    have hxinv : x * x⁻¹ = 1 := mul_inv_cancel₀ hx0.ne'
    have h1xinv : (1 - x) * (1 - x)⁻¹ = 1 := mul_inv_cancel₀ h1x.ne'
    have hval : 1 * (Real.log x - Real.log p) + x * x⁻¹ +
        (-1 * (Real.log (1 - x) - Real.log (1 - p)) + (1 - x) * (-1 / (1 - x))) -
        2 * ((2 : ℕ) * (x - p) ^ (2 - 1) * 1) = F' x := by
      have e1 : (1 - x) * (-1 / (1 - x)) = -((1 - x) * (1 - x)⁻¹) := by ring
      rw [e1, h1xinv, hxinv, hF'def]
      push_cast
      ring
    rw [hval] at hraw
    exact hraw
  -- Second derivative of `F'`.
  have hderivF' : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt F' (F'' x) x := by
    intro x hx
    obtain ⟨hx0, hx1⟩ := hx
    have h1x : (0:ℝ) < 1 - x := by linarith
    have hidx : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id' (𝕜 := ℝ) x
    have hlogx : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx0.ne'
    have hsub : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := hidx.const_sub 1
    have hB0 : HasDerivAt (fun y => Real.log (1 - y)) ((-1) / (1 - x)) x := hsub.log h1x.ne'
    have hlin : HasDerivAt (fun _ : ℝ => Real.log p - Real.log (1 - p)) 0 x :=
      hasDerivAt_const x _
    have hquad := (hidx.sub_const p).const_mul (4 : ℝ)
    have hraw := ((hlogx.sub hB0).sub hlin).sub hquad
    have hval : x⁻¹ - -1 / (1 - x) - 0 - 4 * 1 = F'' x := by
      simp only [hF''def]
      rw [one_div, one_div]
      ring
    rw [hval] at hraw
    exact hraw
  -- Nonnegativity of the second derivative, via `x (1-x) ≤ 1/4`.
  have hF''nonneg : ∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ F'' x := by
    intro x hx
    obtain ⟨hx0, hx1⟩ := hx
    have h1x : (0:ℝ) < 1 - x := by linarith
    have hprod : x * (1 - x) ≤ 1 / 4 := by nlinarith [sq_nonneg (x - 1 / 2)]
    have hprodpos : 0 < x * (1 - x) := mul_pos hx0 h1x
    have hkey : 4 ≤ 1 / x + 1 / (1 - x) := by
      rw [div_add_div _ _ hx0.ne' h1x.ne', le_div_iff₀ hprodpos]
      nlinarith [hprod]
    simp only [hF''def]
    linarith
  -- `F'` is monotone on `(0,1)`.
  have hF'mono : MonotoneOn F' (Set.Ioo (0 : ℝ) 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioo (0:ℝ) 1)
    · exact fun x hx => (hderivF' x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ioo] at hx
      exact (hderivF' x hx).hasDerivWithinAt
    · intro x hx
      rw [interior_Ioo] at hx
      exact hF''nonneg x hx
  have hF'p : F' p = 0 := by simp [hF'def]
  -- Split on which side of `p` the deviated point `q` lies.
  rcases le_total p q with hpq | hqp
  · have hDhi : Convex ℝ (Set.Ioo (0 : ℝ) 1 ∩ Set.Ici p) := (convex_Ioo 0 1).inter (convex_Ici p)
    have hmono : MonotoneOn F (Set.Ioo (0 : ℝ) 1 ∩ Set.Ici p) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg hDhi
      · exact fun x hx => (hderivF x hx.1).continuousAt.continuousWithinAt
      · intro x hx
        exact (hderivF x (interior_subset hx).1).hasDerivWithinAt
      · intro x hx
        obtain ⟨hxIoo, hxp⟩ := interior_subset hx
        have := hF'mono ⟨hp0, hp1⟩ hxIoo hxp
        rwa [hF'p] at this
    have hpmem : p ∈ Set.Ioo (0 : ℝ) 1 ∩ Set.Ici p := ⟨⟨hp0, hp1⟩, le_refl p⟩
    have hqmem : q ∈ Set.Ioo (0 : ℝ) 1 ∩ Set.Ici p := ⟨⟨hq0, hq1⟩, hpq⟩
    have hle := hmono hpmem hqmem hpq
    rw [hFp] at hle
    linarith [hFq]
  · have hDlo : Convex ℝ (Set.Ioo (0 : ℝ) 1 ∩ Set.Iic p) := (convex_Ioo 0 1).inter (convex_Iic p)
    have hanti : AntitoneOn F (Set.Ioo (0 : ℝ) 1 ∩ Set.Iic p) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos hDlo
      · exact fun x hx => (hderivF x hx.1).continuousAt.continuousWithinAt
      · intro x hx
        exact (hderivF x (interior_subset hx).1).hasDerivWithinAt
      · intro x hx
        obtain ⟨hxIoo, hxp⟩ := interior_subset hx
        have := hF'mono hxIoo ⟨hp0, hp1⟩ hxp
        rwa [hF'p] at this
    have hpmem : p ∈ Set.Ioo (0 : ℝ) 1 ∩ Set.Iic p := ⟨⟨hp0, hp1⟩, le_refl p⟩
    have hqmem : q ∈ Set.Ioo (0 : ℝ) 1 ∩ Set.Iic p := ⟨⟨hq0, hq1⟩, hqp⟩
    have hle := hanti hqmem hpmem hqp
    rw [hFp] at hle
    linarith [hFq]

/-- Upper half of the symmetric-point corollary: at `p = 1/2`, `klBin` is at most `4 δ²` for a
deviation `δ`. -/
theorem klBin_half_le {δ : ℝ} (hδ : (1 / 2 + δ) ∈ Set.Ioo (0 : ℝ) 1) :
    klBin (1 / 2 + δ) (1 / 2) ≤ 4 * δ ^ 2 := by
  have hp : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by constructor <;> norm_num
  have h := klBin_le_sq_div hp hδ
  have heq : ((1 / 2 + δ) - (1 / 2 : ℝ)) ^ 2 / ((1 / 2 : ℝ) * (1 - 1 / 2)) = 4 * δ ^ 2 := by
    ring
  linarith [heq ▸ h]

/-- Lower half of the symmetric-point corollary: at `p = 1/2`, `klBin` is at least `2 δ²` for a
deviation `δ`. -/
theorem le_klBin_half {δ : ℝ} (hδ : (1 / 2 + δ) ∈ Set.Ioo (0 : ℝ) 1) :
    2 * δ ^ 2 ≤ klBin (1 / 2 + δ) (1 / 2) := by
  have hp : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by constructor <;> norm_num
  have h := two_mul_sq_le_klBin hp hδ
  have heq : 2 * ((1 / 2 + δ) - (1 / 2 : ℝ)) ^ 2 = 2 * δ ^ 2 := by ring
  linarith [heq ▸ h]

end InformationTheory
