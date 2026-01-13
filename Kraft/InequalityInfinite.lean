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
import Kraft.McMillan

namespace Kraft
open scoped BigOperators Real

variable {α : Type _} [DecidableEq α] [Fintype α] [Nonempty α]

/-- **Kraft's Inequality (Infinite)**: If `S` is a prefix-free code (possibly infinite),
then the series `∑ D^{-|w|}` converges and its sum is at most 1.

The proof shows that every finite subset satisfies the bound (by the finite Kraft inequality),
which implies summability. The tsum bound then follows from summability. -/
theorem kraft_inequality_infinite (S : Set (List α)) (h : PrefixFree S) :
    HasSum (fun w : S => (1 / (Fintype.card α) : ℝ) ^ (w : List α).length) (∑' w : S, (1 / (Fintype.card α) : ℝ) ^ (w : List α).length) ∧
    (∑' w : S, (1 / (Fintype.card α) : ℝ) ^ (w : List α).length) ≤ 1 := by
  let D := (Fintype.card α)
  -- Let $F$ be any finite subset of $S$. Then $F$ is prefix-free. By the finite Kraft inequality, $\sum_{w \in F} D^{-|w|} \le 1$.
  have h_finite_subset : ∀ (F : Finset (List α)), SetLike.coe F ⊆ S → (∑ w ∈ F, (1 / D : ℝ) ^ w.length) ≤ 1 := by
    -- Apply the finite Kraft inequality to the finite subset F.
    intro F hF
    apply kraft_inequality F (fun x hx y hy hxy => h x (hF hx) y (hF hy) hxy)
  refine' ⟨ _, _ ⟩
  · have h_summable : Summable (fun w : S => (1 / D : ℝ) ^ w.val.length) := by
      refine' summable_of_sum_le _ _
      exact 1
      · intro _
        positivity
      · intro u
        specialize h_finite_subset (u.image Subtype.val)
        simp_all only [Finset.coe_image, Set.image_subset_iff, Subtype.coe_preimage_self, Set.subset_univ, Subtype.forall, Subtype.mk.injEq, implies_true, Set.injOn_of_eq_iff_eq, Finset.sum_image]
    exact h_summable.hasSum
  · contrapose! h_finite_subset
    -- Since the series is summable, there exists a finite subset $F$ of $S$ such that $\sum_{w \in F} D^{-|w|} > 1$.
    obtain ⟨F, hF⟩ : ∃ F : Finset (↥S), (∑ w ∈ F, (1 / D : ℝ) ^ (w.val.length)) > 1 := by
      have h_summable : Summable (fun w : S => (1 / D : ℝ) ^ w.val.length) := by
        by_contra h
        rw [tsum_eq_zero_of_not_summable h] at h_finite_subset
        norm_num at h_finite_subset
      exact h_summable.hasSum.eventually (lt_mem_nhds h_finite_subset) |>.exists
    use F.image Subtype.val
    simp_all only [Finset.coe_image, Set.image_subset_iff, Subtype.coe_preimage_self, Set.subset_univ, Subtype.forall, Subtype.mk.injEq, implies_true, Set.injOn_of_eq_iff_eq, Finset.sum_image, and_self]

end Kraft
