/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import InformationTheory.Divergence.Basic
public import InformationTheory.Entropy.ConditionalEntropy

/-!
# The chain rule for finite Kullback-Leibler divergence

This file is the Kullback-Leibler mirror of `InformationTheory.entropy_chain_rule`, namely
`klFin p q = klFin (fst p) (fst q) + condKL p q` for two joint distributions `p, q` on the
*same* product type, rather than the entropy chain rule's single distribution `p`. It reuses
`InformationTheory.fst`/`InformationTheory.snd` (the marginals already built in
`InformationTheory.Entropy.ConditionalEntropy`) and `InformationTheory.Divergence.Basic.klFin`.

Ported from the GameTheory experiments layer (probe E59, verified 2026-08-05), consolidating
previously duplicated local definitions.

## Main definitions

* `condKL (p q : I × J → ℝ) : ℝ`, the conditional KL divergence between two joint laws on the
  same product type, written directly as a single joint sum (mirroring `condEntropy`'s "joint
  sum, not nested sum" design):
  `condKL p q := ∑ x, p x * Real.log ((p x / fst p x.1) / (q x / fst q x.1))`.

## Main results

* `fst_ac` : joint-level absolute continuity descends to the marginals,
  `∀ i, fst q i = 0 → fst p i = 0`.
* `klFin_chain_rule` : **the chain rule**,
  `klFin p q = klFin (fst p) (fst q) + condKL p q`, under only nonnegativity and `hac` — no
  normalization hypothesis, exactly as `entropy_chain_rule` needs none.
* `condKL_nonneg` : `0 ≤ condKL p q` under nonnegativity and `hac` alone — no global
  normalization hypothesis is needed, since a row's own conditional slices are automatically
  normalized regardless of the joint's total mass.
* `klFin_fst_le` : the marginal data-processing corollary, `klFin (fst p) (fst q) ≤ klFin p q`
  (dropping to the marginal projection `I × J → I` only decreases KL divergence). This is new
  relative to the source: `experiments/FiniteKLChainRule.lean`'s docstring only *noted* that
  `klFin_chain_rule` and `condKL_nonneg` together give this "free", without stating it as a
  declaration; this port makes it one.

## Nonclaims

* **No data processing beyond the marginal projection.** `klFin_fst_le` is the marginal
  projection only; no data-processing inequality for a general (possibly stochastic) channel or
  Markov kernel is proved or stated here.
* **No process/sequential statement.** Every definition is a single joint distribution on a
  `Fintype`; there is no time index, no kernel, no filtration, and no anytime/online argument.

## References

`experiments/FiniteKLChainRule.lean` (probe E59); `InformationTheory.condEntropy` and
`InformationTheory.entropy_chain_rule` in `InformationTheory/Entropy/ConditionalEntropy.lean`.
-/

@[expose] public section

namespace InformationTheory

variable {I J : Type*} [Fintype I] [Fintype J]

/-! ### Definition -/

/-- Conditional Kullback-Leibler divergence between two joint laws `p, q` on the same product
type `I × J`, written as a single joint sum (mirroring `condEntropy`'s design) rather than as a
nested sum over conditional slices. -/
noncomputable def condKL (p q : I × J → ℝ) : ℝ :=
  ∑ x, p x * Real.log ((p x / fst p x.1) / (q x / fst q x.1))

/-! ### Absolute continuity descends to the marginal -/

omit [Fintype I] in
/-- Joint-level absolute continuity descends to the first marginal: if `fst q` vanishes at `i`,
every `q (i, j)` vanishes (sum of nonnegatives is zero iff every term is zero), hence by `hac`
every `p (i, j)` vanishes, hence `fst p` vanishes at `i` too. -/
theorem fst_ac {p q : I × J → ℝ} (hq0 : ∀ x, 0 ≤ q x) (hac : ∀ x, q x = 0 → p x = 0) :
    ∀ i, fst q i = 0 → fst p i = 0 := by
  intro i hi
  have hqrow : ∀ j, q (i, j) = 0 := by
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hq0 (i, j))).1 hi
    exact fun j => hzero j (Finset.mem_univ j)
  have hprow : ∀ j, p (i, j) = 0 := fun j => hac (i, j) (hqrow j)
  show ∑ j, p (i, j) = 0
  simp [hprow]

/-! ### The chain rule -/

omit [Fintype I] in
/-- Pointwise splitting of the `klFin p q` summand into a marginal term and a `condKL` term.
Holds unconditionally on `p x = 0` rows (both sides vanish); on `p x > 0` rows, `hac` and the
marginal bounds `le_fst` force all four of `p x`, `q x`, `fst p x.1`, `fst q x.1` positive, and
the log of a product splits by `Real.log_mul`. -/
private theorem pointwise_split_klFin {p q : I × J → ℝ}
    (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x) (hac : ∀ x, q x = 0 → p x = 0) (x : I × J) :
    p x * Real.log (p x / q x)
      = p x * Real.log (fst p x.1 / fst q x.1)
        + p x * Real.log ((p x / fst p x.1) / (q x / fst q x.1)) := by
  rcases (hp0 x).lt_or_eq with hpx | hpx
  · have hqx : 0 < q x := by
      rcases (hq0 x).lt_or_eq with hqx | hqx0
      · exact hqx
      · exact absurd (hac x hqx0.symm) hpx.ne'
    have hfstp : 0 < fst p x.1 := lt_of_lt_of_le hpx (le_fst hp0 x)
    have hfstq : 0 < fst q x.1 := lt_of_lt_of_le hqx (le_fst hq0 x)
    have hprod : (fst p x.1 / fst q x.1) *
        ((p x / fst p x.1) / (q x / fst q x.1)) = p x / q x := by
      field_simp
    have hfac1 : fst p x.1 / fst q x.1 ≠ 0 :=
      div_ne_zero hfstp.ne' hfstq.ne'
    have hfac2 : (p x / fst p x.1) / (q x / fst q x.1) ≠ 0 :=
      div_ne_zero (div_ne_zero hpx.ne' hfstp.ne') (div_ne_zero hqx.ne' hfstq.ne')
    have hlog : Real.log (p x / q x)
        = Real.log (fst p x.1 / fst q x.1)
          + Real.log ((p x / fst p x.1) / (q x / fst q x.1)) := by
      rw [← hprod, Real.log_mul hfac1 hfac2]
    rw [hlog, mul_add]
  · simp [← hpx]

omit [Fintype I] in
/-- Grouping the marginal term of the joint sum by its first coordinate collapses to the
marginal-level `klFin` summand. -/
private theorem sum_mul_log_fst_ratio {p q : I × J → ℝ} (i : I) :
    ∑ j, p (i, j) * Real.log (fst p i / fst q i)
      = fst p i * Real.log (fst p i / fst q i) := by
  rw [← Finset.sum_mul]; rfl

/-- **Chain rule for `klFin`**: `klFin p q = klFin (fst p) (fst q) + condKL p q`. No
normalization hypothesis is needed (the identity is purely algebraic, like
`entropy_chain_rule`); only nonnegativity and absolute continuity are used, to keep every term
on the correct side of the sign trap. -/
theorem klFin_chain_rule {p q : I × J → ℝ}
    (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x) (hac : ∀ x, q x = 0 → p x = 0) :
    klFin p q = klFin (fst p) (fst q) + condKL p q := by
  show ∑ x : I × J, p x * Real.log (p x / q x)
      = ∑ i, fst p i * Real.log (fst p i / fst q i)
        + ∑ x : I × J, p x * Real.log ((p x / fst p x.1) / (q x / fst q x.1))
  have hsplit : ∑ x : I × J, p x * Real.log (p x / q x)
      = ∑ x : I × J, p x * Real.log (fst p x.1 / fst q x.1)
        + ∑ x : I × J, p x * Real.log ((p x / fst p x.1) / (q x / fst q x.1)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun x _ => pointwise_split_klFin hp0 hq0 hac x)
  have hgroup : ∑ x : I × J, p x * Real.log (fst p x.1 / fst q x.1)
      = ∑ i, fst p i * Real.log (fst p i / fst q i) := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl (fun i _ => sum_mul_log_fst_ratio i)
  rw [hsplit, hgroup]

/-! ### Nonnegativity of `condKL` -/

/-- **Nonnegativity of `condKL`.** Row `i` of the joint sum equals `fst p i` times `klFin` of
the two conditional slices `p (i, ·) / fst p i` and `q (i, ·) / fst q i`. When `fst p i = 0`,
nonnegativity of `p` and `le_fst` force `p (i, ·) ≡ 0`, so the row vanishes. When `fst p i > 0`,
`fst_ac` (contrapositive) forces `fst q i > 0`, and both slices sum to exactly `1` regardless of
the joint's total mass, so `klFin_nonneg`'s mass hypothesis is trivial: **no global
normalization hypothesis is needed**, unlike a naive statement anticipating
`hp1 : ∑ x, p x = 1` and `hq1 : ∑ x, q x ≤ 1`. -/
theorem condKL_nonneg {p q : I × J → ℝ}
    (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x) (hac : ∀ x, q x = 0 → p x = 0) :
    0 ≤ condKL p q := by
  show 0 ≤ ∑ x : I × J, p x * Real.log ((p x / fst p x.1) / (q x / fst q x.1))
  rw [Fintype.sum_prod_type]
  apply Finset.sum_nonneg
  intro i _
  rcases (fst_nonneg hp0 i).lt_or_eq with hfstp_pos | hfstp0
  · have hfstq_pos : 0 < fst q i := by
      rcases (fst_nonneg hq0 i).lt_or_eq with hfstq_pos | hfstq0
      · exact hfstq_pos
      · exact absurd (fst_ac hq0 hac i hfstq0.symm) hfstp_pos.ne'
    have hps0 : ∀ j, 0 ≤ p (i, j) / fst p i := fun j =>
      div_nonneg (hp0 (i, j)) hfstp_pos.le
    have hqs0 : ∀ j, 0 ≤ q (i, j) / fst q i := fun j =>
      div_nonneg (hq0 (i, j)) hfstq_pos.le
    have hps1 : ∑ j, p (i, j) / fst p i = 1 := by
      rw [← Finset.sum_div]
      have hrow : ∑ j, p (i, j) = fst p i := rfl
      rw [hrow, div_self hfstp_pos.ne']
    have hqs1 : ∑ j, q (i, j) / fst q i = 1 := by
      rw [← Finset.sum_div]
      have hrow : ∑ j, q (i, j) = fst q i := rfl
      rw [hrow, div_self hfstq_pos.ne']
    have hmass : ∑ j, q (i, j) / fst q i ≤ ∑ j, p (i, j) / fst p i := by rw [hps1, hqs1]
    have hacs : ∀ j, q (i, j) / fst q i = 0 →
        p (i, j) / fst p i = 0 := by
      intro j hqsj
      rcases div_eq_zero_iff.mp hqsj with h | h
      · rw [hac (i, j) h, zero_div]
      · exact absurd h hfstq_pos.ne'
    have hklnonneg : 0 ≤ klFin (fun j => p (i, j) / fst p i)
        (fun j => q (i, j) / fst q i) :=
      klFin_nonneg hps0 hqs0 hacs hmass
    have heq : ∑ j, p (i, j) * Real.log ((p (i, j) / fst p i) /
        (q (i, j) / fst q i))
        = fst p i *
          klFin (fun j => p (i, j) / fst p i)
            (fun j => q (i, j) / fst q i) := by
      show ∑ j, p (i, j) * Real.log ((p (i, j) / fst p i) /
          (q (i, j) / fst q i))
          = fst p i *
            ∑ j, (p (i, j) / fst p i) *
              Real.log ((p (i, j) / fst p i) /
                (q (i, j) / fst q i))
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      have hcancel :
          fst p i * (p (i, j) / fst p i) = p (i, j) :=
        mul_div_cancel₀ (p (i, j)) hfstp_pos.ne'
      rw [← mul_assoc, hcancel]
    rw [heq]
    exact mul_nonneg hfstp_pos.le hklnonneg
  · have hrow0 : ∀ j, p (i, j) = 0 := by
      intro j
      have hle : p (i, j) ≤ fst p i := le_fst hp0 (i, j)
      have hle0 : p (i, j) ≤ 0 := hfstp0 ▸ hle
      linarith [hp0 (i, j)]
    simp [hrow0]

/-! ### The marginal data-processing corollary -/

/-- **Marginal data-processing corollary.** Dropping to the first marginal never increases KL
divergence: `klFin (fst p) (fst q) ≤ klFin p q`. Immediate from `klFin_chain_rule` (the difference
is exactly `condKL p q`) and `condKL_nonneg` (which is nonnegative). -/
theorem klFin_fst_le {p q : I × J → ℝ}
    (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x) (hac : ∀ x, q x = 0 → p x = 0) :
    klFin (fst p) (fst q) ≤ klFin p q := by
  have hchain := klFin_chain_rule hp0 hq0 hac
  have hcond := condKL_nonneg hp0 hq0 hac
  linarith

end InformationTheory
