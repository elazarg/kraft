/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import InformationTheory.Coding.KraftConverse
public import InformationTheory.Coding.SourceCodingLowerBound

/-!
# Shannon-Fano Coding Example

This file demonstrates an application of Kraft's inequality to source coding: the Shannon-Fano
length assignment `⌈-log_D p(i)⌉` satisfies Kraft's condition, so the constructive converse
(`exists_code`) produces an actual prefix-free code from it, with expected
length within one symbol of the entropy lower bound (`entropy_le_expectedLength`
gives the other direction).

## Main definitions

* `shannonFanoLength`: the length assignment `⌈-log_D p(i)⌉`.

## Main results

* `exists_prefix_code_near_entropy`: for any probability distribution, there
  exists a prefix-free code with expected length strictly less than `H_D(p) + 1`.

## References

* Cover & Thomas, *Elements of Information Theory*, Chapter 5
-/

@[expose] public section

namespace InformationTheory

variable {I : Type*} [Fintype I] {D : ℕ}

omit [Fintype I] in
/-- Shannon–Fano length assignment: `l(i) = ⌈ -log_D p(i) ⌉`. -/
noncomputable def shannonFanoLength (p : I → ℝ) (i : I) : ℕ :=
  Nat.ceil (- Real.logb D (p i))

/-- A source-coding use case of the constructive converse: there exists a prefix-free code with
expected length `< H_D(p) + 1`. -/
theorem exists_prefix_code_near_entropy
    (hD : 1 < D) (p : I → ℝ)
    (hp_pos : ∀ i, 0 < p i)      -- (strictly) positive probabilities so logs behave nicely
    (hp_sum : ∑ i, p i = 1) :    -- normalization
    ∃ w : I → List (Fin D),
      Function.Injective w ∧
      IsPrefixFree (Set.range w) ∧
      expectedLength p w < entropy D p + 1 := by
  classical
  letI : Nonempty I := not_isEmpty_iff.mp fun hI => by
    letI := hI
    simp at hp_sum
  let l : I → ℕ := shannonFanoLength (D := D) p

  have hD_one_lt : 1 < (D : ℝ) := by exact_mod_cast hD

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
  refine ⟨w, h_inj, h_pf, ?_⟩

  --------------------------------------------------------------------
  -- Step 3: Expected length bound expectedLength p w < H_D(p) + 1
  --------------------------------------------------------------------
  have hp0 : ∀ x : I, 0 ≤ p x := fun x => (hp_pos x).le

  -- Let a_x = -logb D (p x)
  let a : I → ℝ := fun x => - Real.logb (D : ℝ) (p x)

  -- Pointwise: (ceil a_x : ℝ) < a_x + 1
  have hceil_lt : ∀ x : I, (⌈a x⌉₊ : ℝ) < a x + 1 := by
    intro x
    have hp_le_sum : p x ≤ ∑ i, p i :=
      Finset.single_le_sum (fun i _ => (hp_pos i).le) (by simp)
    have lpos : 0 ≤ a x := by
      simp only [a, Left.nonneg_neg_iff]
      apply Real.logb_nonpos (by exact_mod_cast hD) (hp0 x)
      simpa [hp_sum] using (le_trans hp_le_sum (le_of_eq hp_sum))
    simpa [a] using (Nat.ceil_lt_add_one lpos)

  -- Pointwise (weak): (ceil a_x : ℝ) ≤ a x + 1
  have hceil_le : ∀ x : I, (⌈a x⌉₊ : ℝ) ≤ a x + 1 :=
    fun x => (hceil_lt x).le

  -- Rewrite `∑ p x * a x` as `∑ (-p x * logb D (p x))`
  have ha : (∑ x, p x * a x) = ∑ x, - p x * Real.logb (D : ℝ) (p x) := by
    simp [a]

  have hrhs : (∑ x, p x * (a x + 1)) = (∑ x, p x * a x) + (∑ x, p x) := by
    simp [mul_add, Finset.sum_add_distrib]

  -- `expectedLength p w` unfolds to exactly `∑ x, p x * (l x : ℝ) = ∑ x, p x * ⌈a x⌉₊`
  have hexp_eq : expectedLength p w = ∑ x, p x * (⌈a x⌉₊ : ℝ) := by
    unfold expectedLength
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [h_len x]
    simp [l, shannonFanoLength, a]

  rw [hexp_eq]

  -- Strict inequality: pick one index `x₀` where `hceil_lt` is used, `hceil_le` elsewhere.
  let x₀ : I := Classical.arbitrary I

  have hstrict_one : p x₀ * (⌈a x₀⌉₊ : ℝ) < p x₀ * (a x₀ + 1) :=
    mul_lt_mul_of_pos_left (hceil_lt x₀) (hp_pos x₀)

  have havg_lt : (∑ x, p x * (⌈a x⌉₊ : ℝ)) < ∑ x, p x * (a x + 1) := by
    apply Finset.sum_lt_sum _ ⟨x₀, Finset.mem_univ x₀, hstrict_one⟩
    intro i _
    exact mul_le_mul_of_nonneg_left (hceil_le i) (hp0 i)

  calc (∑ x, p x * (⌈a x⌉₊ : ℝ))
      < ∑ x, p x * (a x + 1) := havg_lt
    _ = (∑ x, p x * a x) + (∑ x, p x) := hrhs
    _ = (∑ x, - p x * Real.logb (D : ℝ) (p x)) + (∑ x, p x) := by rw [ha]
    _ = entropy D p + 1 := by rw [entropy_eq_sum_neg_logb D p, hp_sum]

end InformationTheory
