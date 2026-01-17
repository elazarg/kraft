/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

import InformationTheory.Coding.KraftConverse

/-!
# Shannon-Fano Coding Example

This file demonstrates an application of Kraft's inequality to source coding.

## Main definitions

* `Examples.entropy`: Shannon entropy in base `D`.
* `Examples.shannonFanoLength`: The Shannon-Fano length assignment `⌈-log_D p(i)⌉`.

## Main results

* `Examples.exists_prefix_code_near_entropy`: For any probability distribution, there exists
  a prefix-free code with expected length less than `H_D(p) + 1`.

## References

* Cover & Thomas, *Elements of Information Theory*, Chapter 5
-/

open scoped Real BigOperators

namespace InformationTheory

variable {I : Type*} [Fintype I]
variable {D : ℕ}

section Entropy

/-- Entropy in **base D** (so measured in "D-ary digits"), defined via `negMulLog` (nats) / `log D`. -/
noncomputable def entropy (D : ℕ) (p : I → ℝ) : ℝ :=
  (∑ i, Real.negMulLog (p i)) / Real.log D

/-- Convenience: base-D entropy equals the usual `∑ -p * logb_D p`. -/
lemma entropy_eq_sum_neg_logb (hD : 1 < D) (p : I → ℝ) :
    entropy D p = ∑ i, - p i * Real.logb D (p i) := by
  classical

  unfold entropy

  have hDpos: 0 < (D: ℝ) := by exact_mod_cast lt_trans Nat.zero_lt_one hD
  have hDneq1: (D: ℝ) ≠ 1 := by exact_mod_cast Nat.ne_of_gt hD
  have hlogD_ne : Real.log D ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hDpos hDneq1

  -- turn `/ log D` into `* (log D)⁻¹` and push inside the sum
  -- then rewrite `negMulLog` and `logb`.
  calc
    (∑ i, Real.negMulLog (p i)) / Real.log D
        = (Real.log (D : ℝ))⁻¹ * ∑ i, Real.negMulLog (p i) := by simp [div_eq_mul_inv, mul_comm]
    _   = ∑ i, (Real.log (D : ℝ))⁻¹ * Real.negMulLog (p i) := by simp [Finset.mul_sum]
    _   = ∑ i, - p i * Real.logb D (p i) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            -- `negMulLog x = -x * log x` and `logb D x = log x / log D`
            -- so: (log D)⁻¹ * (-p * log p) = -p * (log p / log D).
            simp [Real.negMulLog_def, Real.logb, div_eq_mul_inv, mul_assoc, mul_comm]


end Entropy

section SourceCoding

/-- Shannon–Fano length assignment: `l(i) = ⌈ -log_D p(i) ⌉`. -/
noncomputable def shannonFanoLength (p : I → ℝ) (i : I) : ℕ :=
  Nat.ceil (- Real.logb D (p i))

variable [Nonempty I]

/--
A source-coding use case of Converse:
there exists a prefix-free code with expected length `< H_D(p) + 1`,
where `H_D` is entropy in base `D`.

This is intentionally placed under `Examples` rather than the core library.
-/
theorem exists_prefix_code_near_entropy
    {hD : 1 < D} (p : I → ℝ)
    (hp_pos : ∀ i, 0 < p i)      -- (strictly) positive probabilities so logs behave nicely
    (hp_sum : ∑ i, p i = 1) :    -- normalization
    ∃ (w : I → List (Fin D)),
      Function.Injective w ∧
      PrefixFree (Set.range w) ∧
      let L := fun i => (w i).length
      let AvgL := ∑ i, p i * (L i : ℝ)
      AvgL < entropy D p + 1 := by
  classical

  let l : I → ℕ := shannonFanoLength (D := D) p

  have hD_one_lt : 1 < (D : ℝ) := by exact_mod_cast hD
  have hDpos: 0 < (D: ℝ) := by exact_mod_cast lt_trans Nat.zero_lt_one hD
  have hDneq1: (D: ℝ) ≠ 1 := by exact_mod_cast Nat.ne_of_gt hD
  have hlogD_ne : Real.log D ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hDpos hDneq1

  --------------------------------------------------------------------
  -- Step 1: Kraft condition for Shannon–Fano lengths
  --
  -- Canonical approach: show pointwise `(1/D)^l(i) ≤ p(i)`, then sum ≤ 1.
  --------------------------------------------------------------------
  have h_pointwise : ∀ i, (1 / D : ℝ) ^ l i ≤ p i := by
    intro i
    -- 1. Rewrite the goal (1/D)^l as D^(-l)
    rw [one_div, inv_pow, ←Real.rpow_natCast, ←Real.rpow_neg (by positivity)]
    -- 2. Use the property: y ≤ log_b(x) ↔ b^y ≤ x
    rw [←Real.le_logb_iff_rpow_le hD_one_lt (hp_pos i)]
    -- 3. Rearrange the hypothesis `hceil` to match the form -l ≤ log(p)
    have hceil : (-Real.logb D (p i)) ≤ l i := Nat.le_ceil _
    rw [neg_le_iff_add_nonneg] at (hceil) ⊢
    linarith [hceil]

  have h_kraft : (∑ i, (1 / D : ℝ) ^ l i) ≤ 1 := by
    -- sum the pointwise bound and use `hp_sum`
    have : (∑ i, (1 / D : ℝ) ^ l i) ≤ ∑ i, p i := by
      exact Finset.sum_le_sum (fun i _ => h_pointwise i)
    simpa [hp_sum] using this


  --------------------------------------------------------------------
  -- Step 2: Invoke Converse library to get an actual prefix-free code
  --------------------------------------------------------------------
  haveI : Nontrivial (Fin D) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by simpa using hD)

  have hs : Summable (fun i : I => (1 / (Fintype.card (Fin D)) : ℝ) ^ l i) := by
    simpa using (Summable.of_finite (f := (fun i : I => (1 / D : ℝ) ^ l i)))

  have htsum : (∑' i : I, (1 / (Fintype.card (Fin D)) : ℝ) ^ l i) ≤ 1 := by
    simpa using (show (∑ i : I, (1 / D : ℝ) ^ l i) ≤ 1 from h_kraft)

  obtain ⟨w, h_inj, h_pf, h_len⟩ := exists_code l hs htsum
  use w

  --------------------------------------------------------------------
  -- Step 3: Expected length bound AvgL < H_D(p) + 1
  --------------------------------------------------------------------
  refine ⟨h_inj, h_pf, ?_⟩
  clear htsum h_kraft hs h_pf h_inj h_pointwise
  intros L avgL
  subst L avgL l
  unfold shannonFanoLength at h_len
  simp_all

  have hp0 : ∀ x : I, 0 ≤ p x := fun x => (hp_pos x).le

  -- Let a_x = -logb D (p x)
  let a : I → ℝ := fun x => - Real.logb (D : ℝ) (p x)

  -- Pointwise: (ceil a_x : ℝ) < a_x + 1
  have hceil_lt : ∀ x : I, (⌈a x⌉₊ : ℝ) < a x + 1 := by
    intro x
    have hp_le_sum : p x ≤ ∑ i, p i := by
      exact (Finset.single_le_sum (fun i hi => (hp_pos i).le) (by simp))

    have lpos: 0 ≤ a x := by
      subst a
      replace hp0 := hp0 x
      simp
      apply Real.logb_nonpos (by exact_mod_cast hD) hp0
      simpa [hp_sum] using (le_trans hp_le_sum (le_of_eq hp_sum))

    simpa [a] using (Nat.ceil_lt_add_one lpos)

  -- Pointwise (weak): (ceil a_x : ℝ) ≤ a x + 1
  have hceil_le : ∀ x : I, (⌈a x⌉₊ : ℝ) ≤ a x + 1 :=
    fun x => (hceil_lt x).le

  -- Multiply by p x (nonneg) and sum: AvgL ≤ ∑ p*(a+1)
  have havg_le :
      (∑ x, p x * (⌈a x⌉₊ : ℝ)) ≤ ∑ x, p x * (a x + 1) := by
    -- `Finset.sum_le_sum` + `mul_le_mul_of_nonneg_left`
    refine Finset.sum_le_sum ?_
    intro x _
    have : (⌈a x⌉₊ : ℝ) ≤ a x + 1 := hceil_le x
    exact mul_le_mul_of_nonneg_left this (hp0 x)

  -- Now rewrite RHS
  have hrhs :
      (∑ x, p x * (a x + 1)) = (∑ x, p x * a x) + (∑ x, p x) := by
    -- distribute and collect
    simp [mul_add, Finset.sum_add_distrib]

  -- Rewrite ∑ p x * a x = ∑ (-p x * logb D (p x))
  have ha :
      (∑ x, p x * a x) = ∑ x, - p x * Real.logb (D : ℝ) (p x) := by
    -- since a x = -logb...
    simp [a]

  -- Put together: AvgL ≤ (∑ -p*logb) + 1
  have havg_le_entropy_plus_one :
      (∑ x, p x * (⌈a x⌉₊ : ℝ)) ≤ entropy D p + 1 := by
    -- use entropy_eq_sum_neg_logb and hp_sum
    calc
      (∑ x, p x * (⌈a x⌉₊ : ℝ))
          ≤ ∑ x, p x * (a x + 1) := havg_le
      _ = (∑ x, p x * a x) + (∑ x, p x) := by simp [hrhs]
      _ = (∑ x, - p x * Real.logb (D : ℝ) (p x)) + (∑ x, p x) := by
            simp [ha]
      _ = (entropy D p) + 1 := by
            simp [entropy_eq_sum_neg_logb hD p, hp_sum]

  -- If you are okay with `≤` instead of `<`, you can finish right here:
  -- exact lt_of_le_of_lt ? ? is missing. But user wants `<`.

  -- To get `<` robustly, pick one index x0 and use strict inequality at x0,
  -- while using `≤` for the rest. This requires `Fintype` to be nonempty.
  let x0 : I := Classical.choice (by assumption)

  have hstrict_one :
      p x0 * (⌈a x0⌉₊ : ℝ) < p x0 * (a x0 + 1) := by
    -- strictness comes from `hceil_lt` and hp_pos x0
    exact (mul_lt_mul_of_pos_left (hceil_lt x0) (hp_pos x0))

  -- Now show the total sum is strictly less:
  have havg_lt :
      (∑ x, p x * (⌈a x⌉₊ : ℝ)) < ∑ x, p x * (a x + 1) := by
    apply Finset.sum_lt_sum _ ⟨x0, Finset.mem_univ x0, hstrict_one⟩
    intro i hiuniv
    simp_all only [mul_le_mul_iff_right₀]

  -- Finally chain to entropy+1
  calc (∑ x, p x * (⌈a x⌉₊ : ℝ))
      < ∑ x, p x * (a x + 1) := havg_lt
    _ = (∑ x, p x * a x) + (∑ x, p x) := by simp [hrhs]
    _ = (∑ x, - p x * Real.logb (D : ℝ) (p x)) + (∑ x, p x) := by simp [ha]
    _ ≤ entropy D p + 1 := by simp [entropy_eq_sum_neg_logb hD p, hp_sum]

end SourceCoding

end InformationTheory
