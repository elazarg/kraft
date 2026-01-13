/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Kraft.Basic

namespace Kraft
open scoped BigOperators Real


variable {α : Type _} [DecidableEq α] [Fintype α] [Nonempty α]

/-- **Kraft's Inequality (Finite)**:
    If S is a finite prefix-free code, the sum of D^(-length) is ≤ 1. -/

theorem kraft_inequality (S : Finset (List α)) (h : PrefixFree (S : Set (List α))) :
    ∑ w ∈ S, (1 / (Fintype.card α) : ℝ) ^ w.length ≤ 1 := by

  let D := (Fintype.card α)

  -- Let $n$ be the maximum length of a word in $S$.
  let n := Finset.sup S List.length

  -- The set of all αean strings of length k
  let all_words (k : ℕ) : Finset (List α) :=
    (Finset.univ : Finset (Fin k → α)).image List.ofFn

  -- The "cylinder" of w (all extensions of w to length n)
  let cylinder (w : List α) : Finset (List α) :=
    (all_words (n - w.length)).image (w ++ ·)

  -- 1. A list is in 'all_words k' iff its length is k
  have mem_all_words_iff (k : ℕ) (l : List α) : l ∈ all_words k ↔ l.length = k := by
    rw [Finset.mem_image]
    constructor
    · rintro ⟨f, _, rfl⟩
      simp
    · intro hlen
      -- If length is k, it comes from the function `l.get`
      exists (fun i => l.get ⟨i, hlen.symm ▸ i.isLt⟩)
      simp only [Finset.mem_univ, true_and]
      apply List.ext_get
      · simp [hlen]
      · intro i h1 h2
        simp

  -- 2. Disjointness: Cylinders don't overlap because S is prefix-free.
  have h_disjoint : ∀ w1 ∈ S, ∀ w2 ∈ S, w1 ≠ w2 → Disjoint (cylinder w1) (cylinder w2) := by
    intros w1 hw1 w2 hw2 hne
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rcases Finset.mem_image.mp hx1 with ⟨s1, _, rfl⟩
    rcases Finset.mem_image.mp hx2 with ⟨s2, _, heq⟩
    rw [List.append_eq_append_iff] at heq
    rcases heq with ⟨m, rfl, -⟩ | ⟨m, rfl, -⟩
    · exact hne (h w2 hw2 _ hw1 ⟨m, rfl⟩).symm
    · exact hne (h w1 hw1 _ hw2 ⟨m, rfl⟩)

  -- card of all_words
  have all_words_card (k : ℕ) : (all_words k).card = D^k := by
    -- all_words k = image List.ofFn univ, and List.ofFn is injective
    have hinj : Function.Injective (List.ofFn : (Fin k → α) → List α) := by
      intro f g hfg
      -- this lemma exists in Lean4/Mathlib
      exact List.ofFn_injective hfg
    -- card(image) = card(univ) = D^k
    simp [D, all_words, Finset.card_image_of_injective, hinj]

  -- card of each cylinder
  have cylinder_card (w : List α) : (cylinder w).card = D^(n - w.length) := by
    have hinj : Function.Injective (fun z : List α => w ++ z) := by
      intro a b hab
      simp_all only [ne_eq, List.append_cancel_left_eq]
    -- cylinder w = image (w++·) (all_words (n - |w|))
    simp [cylinder, Finset.card_image_of_injective, hinj, all_words_card]

  -- cylinders land inside the length-n universe
  have cylinder_subset_all_words_n (w : List α) (hw : w ∈ S) :
      cylinder w ⊆ all_words n := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨s, hs, rfl⟩
    have hslen : s.length = n - w.length :=
      (mem_all_words_iff (n - w.length) s).1 hs
    have hwle : w.length ≤ n := by
      -- n = sup S length
      simpa [n] using (Finset.le_sup (s := S) (f := List.length) hw)
    have hlen : (w ++ s).length = n := by
      -- len(w++s) = len w + len s = w.length + (n - w.length) = n
      simp [List.length_append, hslen, Nat.add_sub_of_le hwle]
    exact (mem_all_words_iff n (w ++ s)).2 hlen

  -- now the main inequality
  have h_sum_le_total : ∑ w ∈ S, D^(n - w.length) ≤ D^n := by
    let U : Finset (List α) := S.biUnion cylinder
    have hU_card :
        U.card = ∑ w ∈ S, (cylinder w).card := by
      -- disjoint union → sum of cards
      simpa [U] using
        (Finset.card_biUnion (s := S) (t := cylinder)
          (by
            intro w1 hw1 w2 hw2 hne
            exact h_disjoint w1 hw1 w2 hw2 hne))
    have hU_sub : U ⊆ all_words n := by
      intro x hx
      rcases Finset.mem_biUnion.mp hx with ⟨w, hwS, hxw⟩
      exact cylinder_subset_all_words_n w hwS hxw
    have hU_le : U.card ≤ (all_words n).card :=
      Finset.card_le_card hU_sub
    -- rewrite sums into cards, then bound by all_words n
    calc
      ∑ w ∈ S, D^(n - w.length)
          = ∑ w ∈ S, (cylinder w).card := by
              refine Finset.sum_congr rfl (fun w hw => ?_)
              simp [cylinder_card]
      _ = U.card := by simp [hU_card]
      _ ≤ (all_words n).card := hU_le
      _ = D^n := by simp [all_words_card]

  -- Key algebra lemma: D^(n-|w|)/D^n = (1/D)^{|w|}
  have rhs_eq (w : List α) (hw : w ∈ S) :
      (D : ℝ)^(n - w.length) / (D : ℝ)^n = (1/D : ℝ)^w.length := by
    have hwle : w.length ≤ n := by simpa [n] using Finset.le_sup (s := S) (f := List.length) hw
    rw [show (D : ℝ)^n = (D : ℝ)^(n - w.length) * (D : ℝ)^w.length by
          rw [← pow_add, Nat.sub_add_cancel hwle]]
    subst D
    simp [div_mul_eq_div_div, one_div, inv_pow]

  -- Cast the Nat inequality to ℝ in the exact form we need
  have h_sum_le_totalR :
      (∑ w ∈ S, (D : ℝ)^(n - w.length)) ≤ (D : ℝ)^n := by
    have h_cast :
        ((∑ w ∈ S, D^(n - w.length)) : ℝ) ≤ (D^n : ℕ) := by
      exact_mod_cast h_sum_le_total
    simpa [Nat.cast_sum, Nat.cast_pow, Nat.cast_two] using h_cast

  -- Final
  calc
    ∑ w ∈ S, (1/D : ℝ)^w.length
        = ∑ w ∈ S, (D : ℝ)^(n - w.length) / (D : ℝ)^n := by
            refine Finset.sum_congr rfl (fun w hw => ?_)
            simpa using (rhs_eq w hw).symm
    _ = (∑ w ∈ S, (D : ℝ)^(n - w.length)) / (D : ℝ)^n := by
            simpa using
              (S.sum_div
                (f := fun w => (D : ℝ)^(n - w.length))
                (a := (D : ℝ)^n)).symm
    _ ≤ (D : ℝ)^n / (D : ℝ)^n := by
            exact div_le_div_of_nonneg_right h_sum_le_totalR (by positivity)
    _ = 1 := by simp

end Kraft
