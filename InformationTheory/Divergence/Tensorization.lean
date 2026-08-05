/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
import InformationTheory.Divergence.Basic
import InformationTheory.Divergence.Pinsker

/-!
# Tensorization of finite KL divergence and the quadratic deviation budget

This file proves that Kullback-Leibler divergence between finite product laws is the sum of the
per-step divergences (tensorization), and composes that with a per-step chi-squared bound to get
a finite-horizon quadratic information budget for a predictable-mixture deviation. It studies a
per-step deviation rate `δ t ∈ [0,1]` that mixes a baseline per-step law `r t` with a comparison
law `s t`, `mixed t := (1 - δ t) · r t + δ t · s t`, and bounds `D_KL(∏ mixed_t ‖ ∏ r_t)`.

**Scope.** Only *independent* per-step deviations are treated: the mixing weight `δ t` at step
`t` may depend on `t` but not on the realized history `ω`. Tensorizing KL divergence for an
adapted (history-dependent) mixture would need the sequential chain rule for KL, not the
two-factor product identity proved here; that adapted/predictable-rate version is a further
extension, not attempted in this file.

**Units.** `klFin` is built on `Real.log`, i.e. it is measured in **nats**, not bits.

Ported from the GameTheory experiments layer (probe E61, verified 2026-08-05), consolidating
previously duplicated local definitions: the source's local `klFin` and `klFin_relabel` are
deleted in favor of `InformationTheory.Divergence.Basic`'s declarations.

## Main definitions

* `productLaw (r : Fin T → I → ℝ) : (Fin T → I) → ℝ`, the finite-horizon product law
  `∏ t, r t (ω t)`.

## Main results

* `klFin_prod_two` : the two-factor tensorization identity on a product index type `I × J`.
* `productLaw_nonneg`, `productLaw_sum_one` : basic plumbing for `productLaw`.
* `klFin_productLaw` : the full tensorization theorem, `KL(∏ r_t ‖ ∏ r'_t) = ∑_t KL(r_t ‖ r'_t)`,
  by induction on the horizon `T`, peeling off the last step via the equivalence
  `(Fin (T+1) → I) ≃ (Fin T → I) × I`.
* `klFin_mix_le_chiSq` : the per-step chi-squared bound `D_KL(P_δ ‖ P) ≤ δ² · χ²(Q, P)` for the
  mixture `P_δ = (1-δ)P + δQ`, `δ ∈ [0,1]`, under strict positivity of the base `P`.
* `pathBudget` : composing the two: if every per-step chi-squared statistic is capped by `C`, the
  accumulated information of the whole path is at most `C · ∑_t δ_t²`.
* `detector_miss_of_pathBudget` : **new in this port** (the composition the source experiments
  could not state, since `experiments/*.lean` files cannot import each other). The finite-horizon
  linear-debt/quadratic-information detection fence: composing `pathBudget` with
  `InformationTheory.Divergence.Pinsker.miss_add_falseAlarm_ge` via `Real.exp` monotonicity,
  false alarm under the prescribed law plus miss under the deviation law is bounded below by
  `½ · exp(−C · ∑ δ²)`, while the deviator's incentive debt scales as `∑ δ` (linear).

## References

`experiments/ProductKLBudget.lean` (probe E61); `experiments/BinaryKLQuadratic.lean` (probe E51,
the single-step binary analogue whose termwise `log t ≤ t - 1` route `klFin_mix_le_chiSq`
reuses); `InformationTheory.Divergence.Pinsker.miss_add_falseAlarm_ge`, the testing corollary
`detector_miss_of_pathBudget` composes with.
-/

namespace InformationTheory

/-! ## The two-factor tensorization identity -/

/-- Termwise engine of `klFin_prod_two`: for termwise absolute continuity
`a' = 0 → a = 0` and `b' = 0 → b = 0`,
`(a * b) * log (a * b / (a' * b')) = a * log (a / a') * b + a * (b * log (b / b'))`,
with **no sign hypotheses at all** on `a, a', b, b'`. When `a = 0` or `b = 0` both sides vanish
(the common factor `a * b` is `0` regardless of the log value); otherwise `a' ≠ 0` and `b' ≠ 0`
follow from absolute continuity, and the identity is `Real.log_mul` applied to `a / a'` and
`b / b'` — which needs only nonvanishing denominators, not positivity, since Lean's `Real.log` is
already the even extension `log x = log |x|` under the junk convention `log 0 = 0`. -/
private theorem klFin_prod_two_term {a a' b b' : ℝ} (hac : a' = 0 → a = 0)
    (hbc : b' = 0 → b = 0) :
    (a * b) * Real.log (a * b / (a' * b'))
      = a * Real.log (a / a') * b + a * (b * Real.log (b / b')) := by
  rcases eq_or_ne a 0 with ha0 | hane
  · simp [ha0]
  · rcases eq_or_ne b 0 with hb0 | hbne
    · simp [hb0]
    · have ha'ne : a' ≠ 0 := fun h => hane (hac h)
      have hb'ne : b' ≠ 0 := fun h => hbne (hbc h)
      have hlog : Real.log (a * b / (a' * b')) = Real.log (a / a') + Real.log (b / b') := by
        rw [← div_mul_div_comm]
        exact Real.log_mul (div_ne_zero hane ha'ne) (div_ne_zero hbne hb'ne)
      rw [hlog]
      ring

/-- Tensorization of `klFin` over a two-factor product index `I × J`. Proved under strictly fewer
hypotheses than a naive statement would need: **no nonnegativity hypothesis is needed at all**
(the termwise engine `klFin_prod_two_term` is an unconditional algebraic identity, because
`Real.log_mul` only needs nonvanishing arguments, not positive ones), and normalization `∑ = 1`
is needed only of the two **numerator** laws `p` and `s`, not of `p'` and `s'`. Nonnegativity and
full normalization of all four laws remain the intended *reading* of `p, p', s, s'` as genuine
probability laws (that is the setting `productLaw`, `klFin_productLaw`, and `pathBudget` below
actually use); they are simply not needed by *this* proof. -/
theorem klFin_prod_two {I J : Type*} [Fintype I] [Fintype J] (p p' : I → ℝ) (s s' : J → ℝ)
    (hpsum : ∑ i, p i = 1) (hssum : ∑ j, s j = 1)
    (hpac : ∀ i, p' i = 0 → p i = 0) (hsac : ∀ j, s' j = 0 → s j = 0) :
    klFin (fun x : I × J => p x.1 * s x.2) (fun x : I × J => p' x.1 * s' x.2)
      = klFin p p' + klFin s s' := by
  have hterm : ∀ i j, (p i * s j) * Real.log (p i * s j / (p' i * s' j))
      = p i * Real.log (p i / p' i) * s j + p i * (s j * Real.log (s j / s' j)) :=
    fun i j => klFin_prod_two_term (hpac i) (hsac j)
  have hsplit : ∀ i, ∑ j, (p i * Real.log (p i / p' i) * s j + p i * (s j * Real.log (s j / s' j)))
      = p i * Real.log (p i / p' i) * (∑ j, s j) + p i * (∑ j, s j * Real.log (s j / s' j)) := by
    intro i
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  show ∑ x : I × J, (p x.1 * s x.2) * Real.log (p x.1 * s x.2 / (p' x.1 * s' x.2))
      = klFin p p' + klFin s s'
  rw [Fintype.sum_prod_type]
  calc ∑ i, ∑ j, (p i * s j) * Real.log (p i * s j / (p' i * s' j))
      = ∑ i, ∑ j, (p i * Real.log (p i / p' i) * s j + p i * (s j * Real.log (s j / s' j))) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hterm i j
    _ = ∑ i, (p i * Real.log (p i / p' i) * (∑ j, s j)
          + p i * (∑ j, s j * Real.log (s j / s' j))) :=
        Finset.sum_congr rfl fun i _ => hsplit i
    _ = ∑ i, p i * Real.log (p i / p' i) + ∑ i, p i * ∑ j, s j * Real.log (s j / s' j) := by
        simp_rw [hssum, mul_one]
        exact Finset.sum_add_distrib
    _ = (∑ i, p i * Real.log (p i / p' i)) + ∑ j, s j * Real.log (s j / s' j) := by
        rw [← Finset.sum_mul, hpsum, one_mul]

/-! ## Finite-horizon product laws -/

/-- The product law of a finite sequence of per-step laws `r t : I → ℝ`, `t < T`, evaluated at a
realized path `ω : Fin T → I`. -/
noncomputable def productLaw {I : Type*} {T : ℕ} (r : Fin T → I → ℝ) : (Fin T → I) → ℝ :=
  fun ω => ∏ t, r t (ω t)

/-- A product law of nonnegative per-step laws is nonnegative. -/
theorem productLaw_nonneg {I : Type*} [Fintype I] {T : ℕ} (r : Fin T → I → ℝ)
    (hr : ∀ t i, 0 ≤ r t i) : ∀ ω, 0 ≤ productLaw r ω :=
  fun ω => Finset.prod_nonneg fun t _ => hr t (ω t)

/-- A product law of per-step laws that each sum to `1` itself sums to `1` over all paths, via
`Fintype.prod_sum` (a product of sums is a sum of products). -/
theorem productLaw_sum_one {I : Type*} [Fintype I] {T : ℕ} (r : Fin T → I → ℝ)
    (hrsum : ∀ t, ∑ i, r t i = 1) : ∑ ω, productLaw r ω = 1 := by
  have h : ∏ t, ∑ i, r t i = ∑ ω : Fin T → I, ∏ t, r t (ω t) := Fintype.prod_sum r
  simp only [hrsum, Finset.prod_const_one] at h
  simpa [productLaw] using h.symm

/-- Absolute continuity of per-step laws propagates to their product laws: if `r'` is termwise
absolutely continuous with respect to `r` (`r' t i = 0 → r t i = 0`), then `productLaw r'` is
absolutely continuous with respect to `productLaw r`. In a finite product of reals, the product
vanishes iff some factor vanishes (`Finset.prod_eq_zero_iff`), so the failing factor of
`productLaw r'` is witnessed and transported termwise. -/
private theorem productLaw_ac {I : Type*} [Fintype I] {T : ℕ} {r r' : Fin T → I → ℝ}
    (hac : ∀ t i, r' t i = 0 → r t i = 0) :
    ∀ ω, productLaw r' ω = 0 → productLaw r ω = 0 := by
  intro ω hω
  simp only [productLaw] at hω ⊢
  obtain ⟨t, -, ht⟩ := Finset.prod_eq_zero_iff.mp hω
  exact Finset.prod_eq_zero (Finset.mem_univ t) (hac t (ω t) ht)

/-! ## Peeling off the last step -/

/-- The equivalence separating a length-`(T+1)` path into its first `T` steps and its last step,
`ω ↦ (Fin.init ω, ω (Fin.last T))`, with inverse `Fin.snoc`. This is the equivalence
`(Fin (T + 1) → I) ≃ (Fin T → I) × I` that `klFin_productLaw`'s inductive step transports along. -/
def stepEquiv (T : ℕ) (I : Type*) : (Fin (T + 1) → I) ≃ (Fin T → I) × I where
  toFun ω := (Fin.init ω, ω (Fin.last T))
  invFun p := Fin.snoc p.1 p.2
  left_inv ω := by simp
  right_inv p := by simp

/-! ## Tensorization over the horizon -/

/-- Tensorization of `klFin` over a finite horizon: KL divergence between product laws is the sum
of the per-step KL divergences, under per-step normalization (`∑ i, r t i = 1`,
`∑ i, r' t i = 1`) and per-step absolute continuity. Proved by induction on `T`, peeling off the
last step via `stepEquiv` and `klFin_prod_two`. **No nonnegativity hypothesis is needed**, since
`klFin_prod_two` itself needs none, and `productLaw_sum_one` / `productLaw_ac` likewise need only
normalization / absolute continuity. The relabeling step reuses
`InformationTheory.Divergence.Basic.klFin_relabel`, applied along `(stepEquiv T I).symm` so that
its `e.symm` matches `stepEquiv T I` in the direction the induction needs. -/
theorem klFin_productLaw {I : Type*} [Fintype I] :
    ∀ (T : ℕ) (r r' : Fin T → I → ℝ),
      (∀ t, ∑ i, r t i = 1) → (∀ t, ∑ i, r' t i = 1) →
      (∀ t i, r' t i = 0 → r t i = 0) →
      klFin (productLaw r) (productLaw r') = ∑ t, klFin (r t) (r' t) := by
  intro T
  induction T with
  | zero =>
    intro r r' _ _ _
    simp [klFin, productLaw, Finset.prod_of_isEmpty]
  | succ T ih =>
    intro r r' hrsum hr'sum hac
    set rp : Fin T → I → ℝ := fun t => r t.castSucc with hrp_def
    set rp' : Fin T → I → ℝ := fun t => r' t.castSucc with hrp'_def
    have hrpsum : ∀ t, ∑ i, rp t i = 1 := fun t => hrsum t.castSucc
    have hrp'sum : ∀ t, ∑ i, rp' t i = 1 := fun t => hr'sum t.castSucc
    have hracc : ∀ t i, rp' t i = 0 → rp t i = 0 := fun t i => hac t.castSucc i
    have hihstep : klFin (productLaw rp) (productLaw rp') = ∑ t, klFin (rp t) (rp' t) :=
      ih rp rp' hrpsum hrp'sum hracc
    have hPsum : ∑ ω, productLaw rp ω = 1 := productLaw_sum_one rp hrpsum
    have hPac : ∀ ω, productLaw rp' ω = 0 → productLaw rp ω = 0 := productLaw_ac hracc
    have key := klFin_prod_two (productLaw rp) (productLaw rp') (r (Fin.last T)) (r' (Fin.last T))
      hPsum (hrsum (Fin.last T)) hPac (hac (Fin.last T))
    have hmatch : productLaw r
        = fun ω => productLaw rp (stepEquiv T I ω).1 * r (Fin.last T) (stepEquiv T I ω).2 := by
      funext ω
      show productLaw r ω = productLaw rp (Fin.init ω) * r (Fin.last T) (ω (Fin.last T))
      have hkey : (∏ t : Fin (T + 1), r t (ω t))
          = (∏ t : Fin T, r t.castSucc (ω t.castSucc)) * r (Fin.last T) (ω (Fin.last T)) :=
        Fin.prod_univ_castSucc (fun t => r t (ω t))
      simpa [productLaw, hrp_def, Fin.init] using hkey
    have hmatch' : productLaw r'
        = fun ω => productLaw rp' (stepEquiv T I ω).1 * r' (Fin.last T) (stepEquiv T I ω).2 := by
      funext ω
      show productLaw r' ω = productLaw rp' (Fin.init ω) * r' (Fin.last T) (ω (Fin.last T))
      have hkey : (∏ t : Fin (T + 1), r' t (ω t))
          = (∏ t : Fin T, r' t.castSucc (ω t.castSucc)) * r' (Fin.last T) (ω (Fin.last T)) :=
        Fin.prod_univ_castSucc (fun t => r' t (ω t))
      simpa [productLaw, hrp'_def, Fin.init] using hkey
    have hrelabel :
        klFin (fun ω => productLaw rp (stepEquiv T I ω).1 * r (Fin.last T) (stepEquiv T I ω).2)
            (fun ω => productLaw rp' (stepEquiv T I ω).1 * r' (Fin.last T) (stepEquiv T I ω).2)
          = klFin (fun x : (Fin T → I) × I => productLaw rp x.1 * r (Fin.last T) x.2)
              (fun x : (Fin T → I) × I => productLaw rp' x.1 * r' (Fin.last T) x.2) := by
      have h := klFin_relabel (stepEquiv T I).symm
        (fun x : (Fin T → I) × I => productLaw rp x.1 * r (Fin.last T) x.2)
        (fun x : (Fin T → I) × I => productLaw rp' x.1 * r' (Fin.last T) x.2)
      rw [Equiv.symm_symm] at h
      exact h
    rw [hmatch, hmatch', hrelabel, key, hihstep, hrp_def, hrp'_def]
    exact (Fin.sum_univ_castSucc (fun t => klFin (r t) (r' t))).symm

/-! ## The per-step chi-squared bound -/

/-- Termwise engine of `klFin_mix_le_chiSq`: for `a ≥ 0` and `b > 0`,
`a * log (a / b) ≤ (a - b)^2 / b + (a - b)`. At `a = 0` both sides are `0`; for `a > 0` it is
`Real.log_le_sub_one_of_pos` (`log t ≤ t - 1`) applied to `t = a / b`, after the algebraic
identity `(a - b)^2 / b + (a - b) = a^2 / b - a` (clearing the denominator `b ≠ 0`). -/
private theorem klFin_mix_le_chiSq_term {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    a * Real.log (a / b) ≤ (a - b) ^ 2 / b + (a - b) := by
  have hident : (a - b) ^ 2 / b + (a - b) = a ^ 2 / b - a := by field_simp; ring
  rw [hident]
  rcases ha.eq_or_lt with ha0 | hapos
  · simp [← ha0]
  · have hlog : Real.log (a / b) ≤ a / b - 1 := Real.log_le_sub_one_of_pos (div_pos hapos hb)
    have hmul : a * Real.log (a / b) ≤ a * (a / b - 1) := mul_le_mul_of_nonneg_left hlog ha
    have heq : a * (a / b - 1) = a ^ 2 / b - a := by field_simp
    linarith [heq ▸ hmul]

/-- The finite, discrete-KL analogue of the chi-squared upper bound: for a strictly positive
base law `r` and an alternative `s` with `∑ s = 1`, the mixture `P_δ = (1 - δ) r + δ s` satisfies
`D_KL(P_δ ‖ r) ≤ δ² · χ²(s, r)` for `δ ∈ [0, 1]`. This is the finite-support companion of
`InformationTheory.Divergence.Binary.klBin_le_sq_div`; the same termwise `log t ≤ t - 1` route is
used, then re-summed with the "both sum to `1`" cancellation of the linear term. Requires
`∑ r = 1` in addition to `∑ s = 1` — necessary (not merely a proof artifact): the linear term
`∑ (P_δ)_i - ∑ r_i` cancels only because both sums equal `1`. -/
theorem klFin_mix_le_chiSq {I : Type*} [Fintype I] (r s : I → ℝ) (hr_pos : ∀ i, 0 < r i)
    (hrsum : ∑ i, r i = 1) (hs : ∀ i, 0 ≤ s i) (hssum : ∑ i, s i = 1) {δ : ℝ}
    (hδ : δ ∈ Set.Icc (0 : ℝ) 1) :
    klFin (fun i => (1 - δ) * r i + δ * s i) r ≤ δ ^ 2 * ∑ i, (s i - r i) ^ 2 / r i := by
  obtain ⟨hδ0, hδ1⟩ := hδ
  set mix : I → ℝ := fun i => (1 - δ) * r i + δ * s i with hmix_def
  have hmixnn : ∀ i, 0 ≤ mix i := by
    intro i
    have h1 : 0 ≤ (1 - δ) * r i := mul_nonneg (by linarith) (hr_pos i).le
    have h2 : 0 ≤ δ * s i := mul_nonneg hδ0 (hs i)
    simpa [hmix_def] using add_nonneg h1 h2
  have hterm : ∀ i, mix i * Real.log (mix i / r i) ≤ (mix i - r i) ^ 2 / r i + (mix i - r i) :=
    fun i => klFin_mix_le_chiSq_term (hmixnn i) (hr_pos i)
  have hsum_le : klFin mix r ≤ ∑ i, ((mix i - r i) ^ 2 / r i + (mix i - r i)) :=
    Finset.sum_le_sum (fun i _ => hterm i)
  have hmixsum : ∑ i, mix i = 1 := by
    simp only [hmix_def]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hrsum, hssum]
    ring
  have hdiffsum : ∑ i, (mix i - r i) = 0 := by
    rw [Finset.sum_sub_distrib, hmixsum, hrsum]
    ring
  have hdiff_eq : ∀ i, mix i - r i = δ * (s i - r i) := by
    intro i
    simp only [hmix_def]
    ring
  have hsq_eq : ∑ i, (mix i - r i) ^ 2 / r i = δ ^ 2 * ∑ i, (s i - r i) ^ 2 / r i := by
    have hterm_eq : ∀ i, (mix i - r i) ^ 2 / r i = δ ^ 2 * ((s i - r i) ^ 2 / r i) := by
      intro i
      rw [hdiff_eq i]
      ring
    simp_rw [hterm_eq, ← Finset.mul_sum]
  calc klFin mix r ≤ ∑ i, ((mix i - r i) ^ 2 / r i + (mix i - r i)) := hsum_le
    _ = (∑ i, (mix i - r i) ^ 2 / r i) + ∑ i, (mix i - r i) := Finset.sum_add_distrib
    _ = δ ^ 2 * ∑ i, (s i - r i) ^ 2 / r i + 0 := by rw [hsq_eq, hdiffsum]
    _ = δ ^ 2 * ∑ i, (s i - r i) ^ 2 / r i := by ring

/-! ## The finite-horizon path budget -/

/-- The finite-horizon quadratic information budget: composing `klFin_productLaw` with
`klFin_mix_le_chiSq` at each step, the KL divergence between the mixed path law and the base path
law is at most `C` times the accumulated quadratic deviation `∑ t, (δ t)²`, whenever every
per-step chi-squared statistic `χ²(s t, r t)` is capped by `C`. The absolute-continuity side
condition needed by `klFin_productLaw` (mixture-vs-base) is automatic here, since the base `r t i`
is always strictly positive. -/
theorem pathBudget {I : Type*} [Fintype I] (T : ℕ) (r s : Fin T → I → ℝ) (δ : Fin T → ℝ)
    (hr_pos : ∀ t i, 0 < r t i) (hrsum : ∀ t, ∑ i, r t i = 1) (hs : ∀ t i, 0 ≤ s t i)
    (hssum : ∀ t, ∑ i, s t i = 1) (hδ : ∀ t, δ t ∈ Set.Icc (0 : ℝ) 1) {C : ℝ}
    (hC : ∀ t, ∑ i, (s t i - r t i) ^ 2 / r t i ≤ C) :
    klFin (productLaw (fun t i => (1 - δ t) * r t i + δ t * s t i)) (productLaw r)
      ≤ C * ∑ t, (δ t) ^ 2 := by
  set mixed : Fin T → I → ℝ := fun t i => (1 - δ t) * r t i + δ t * s t i with hmixed_def
  have hmixed_sum : ∀ t, ∑ i, mixed t i = 1 := by
    intro t
    simp only [hmixed_def]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hrsum t, hssum t]
    ring
  have hac : ∀ t i, r t i = 0 → mixed t i = 0 := fun t i h => absurd h (hr_pos t i).ne'
  have htensor : klFin (productLaw mixed) (productLaw r) = ∑ t, klFin (mixed t) (r t) :=
    klFin_productLaw T mixed r hmixed_sum hrsum hac
  have hstep : ∀ t, klFin (mixed t) (r t) ≤ (δ t) ^ 2 * ∑ i, (s t i - r t i) ^ 2 / r t i :=
    fun t => klFin_mix_le_chiSq (r t) (s t) (hr_pos t) (hrsum t) (hs t) (hssum t) (hδ t)
  have hstep2 : ∀ t, klFin (mixed t) (r t) ≤ (δ t) ^ 2 * C := by
    intro t
    calc klFin (mixed t) (r t) ≤ (δ t) ^ 2 * ∑ i, (s t i - r t i) ^ 2 / r t i := hstep t
      _ ≤ (δ t) ^ 2 * C := mul_le_mul_of_nonneg_left (hC t) (sq_nonneg _)
  calc klFin (productLaw mixed) (productLaw r)
      = ∑ t, klFin (mixed t) (r t) := htensor
    _ ≤ ∑ t, (δ t) ^ 2 * C := Finset.sum_le_sum (fun t _ => hstep2 t)
    _ = C * ∑ t, (δ t) ^ 2 := by rw [← Finset.sum_mul, mul_comm]

/-! ## The detection-fence corollary -/

open scoped Classical in
/-- **The finite-horizon linear-debt/quadratic-information detection fence.** Composing
`pathBudget` with `InformationTheory.Divergence.Pinsker.miss_add_falseAlarm_ge` via `Real.exp`
antitonicity: for every rejection region `A`, false alarm under the prescribed (base) product law
plus miss under the deviation (mixed) product law is bounded below by `½ · exp(−C · ∑ δ²)`. This
is the composition the source experiments could not state, since `experiments/*.lean` files
cannot import each other; it is the payoff of consolidating `pathBudget`
(`experiments/ProductKLBudget.lean`, probe E61) and `miss_add_falseAlarm_ge`
(`experiments/FinitePinskerBH.lean`, probe E60) into the same library.

The orientation matches `miss_add_falseAlarm_ge` applied with `p := productLaw mixed` (the
deviation law) and `q := productLaw r` (the prescribed/null law): `∑_A q` is the false-alarm
probability under the null, `∑_{Aᶜ} p` is the miss probability under the deviation. The
absolute-continuity side condition is automatic since the base `r t i` is strictly positive
(`productLaw r ω` is a product of positive numbers, hence itself positive, so it is never zero).

While the detector's statistical information budget scales as `∑ δ_t²` (quadratic), a deviator's
accumulated incentive debt scales as `∑ δ_t` (linear) — the finite-horizon core of the
linear-debt-versus-quadratic-information fence. -/
theorem detector_miss_of_pathBudget {I : Type*} [Fintype I] (T : ℕ) (r s : Fin T → I → ℝ)
    (δ : Fin T → ℝ)
    (hr_pos : ∀ t i, 0 < r t i) (hrsum : ∀ t, ∑ i, r t i = 1) (hs : ∀ t i, 0 ≤ s t i)
    (hssum : ∀ t, ∑ i, s t i = 1) (hδ : ∀ t, δ t ∈ Set.Icc (0 : ℝ) 1) {C : ℝ}
    (hC : ∀ t, ∑ i, (s t i - r t i) ^ 2 / r t i ≤ C)
    (A : Finset (Fin T → I)) :
    (1 / 2) * Real.exp (-(C * ∑ t, (δ t) ^ 2))
      ≤ (∑ ω ∈ A, productLaw r ω)
        + ∑ ω ∈ Aᶜ, productLaw (fun t i => (1 - δ t) * r t i + δ t * s t i) ω := by
  have hmixed_nonneg : ∀ t i, 0 ≤ (1 - δ t) * r t i + δ t * s t i := by
    intro t i
    have h1 : 0 ≤ (1 - δ t) * r t i := mul_nonneg (by linarith [(hδ t).2]) (hr_pos t i).le
    have h2 : 0 ≤ δ t * s t i := mul_nonneg (hδ t).1 (hs t i)
    linarith
  have hmixed_sum : ∀ t, ∑ i, ((1 - δ t) * r t i + δ t * s t i) = 1 := by
    intro t
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hrsum t, hssum t]
    ring
  have hac : ∀ ω, productLaw r ω = 0 →
      productLaw (fun t i => (1 - δ t) * r t i + δ t * s t i) ω = 0 := by
    intro ω hω
    exact absurd hω (Finset.prod_pos (fun t _ => hr_pos t (ω t))).ne'
  have hp0 := productLaw_nonneg (fun t i => (1 - δ t) * r t i + δ t * s t i) hmixed_nonneg
  have hq0 := productLaw_nonneg r (fun t i => (hr_pos t i).le)
  have hp1 := productLaw_sum_one (fun t i => (1 - δ t) * r t i + δ t * s t i) hmixed_sum
  have hq1 := productLaw_sum_one r hrsum
  have hbudget := pathBudget T r s δ hr_pos hrsum hs hssum hδ hC
  have htest := miss_add_falseAlarm_ge hp0 hq0 hp1 hq1 hac A
  have hexp_mono : Real.exp (-(C * ∑ t, (δ t) ^ 2))
      ≤ Real.exp
          (-(klFin (productLaw (fun t i => (1 - δ t) * r t i + δ t * s t i)) (productLaw r))) :=
    Real.exp_le_exp.mpr (by linarith [hbudget])
  have hscaled := mul_le_mul_of_nonneg_left hexp_mono (by norm_num : (0:ℝ) ≤ 1 / 2)
  linarith [hscaled, htest]

end InformationTheory
