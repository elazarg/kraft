/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Tendsto
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Analysis.SpecificLimits.Normed

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

import InformationTheory.Coding.PrefixFree
import InformationTheory.Coding.KraftMcMillan

/-!
# Kraft's Inequality

This file proves Kraft's inequality for prefix-free codes over finite alphabets.

## Main definitions

* `kraftWeight`: The Kraft weight of a word `w` is `D^{-|w|}` where `D` is the alphabet size.

## Main results

* `kraft_inequality`: For a finite prefix-free code `S` over an alphabet of size `D`,
  `∑_{w ∈ S} D^{-|w|} ≤ 1`.
* `kraft_inequality_infinite`: Extension to infinite prefix-free codes via `tsum`.

## References

* Cover & Thomas, *Elements of Information Theory*, Chapter 5
-/

namespace InformationTheory

variable {α : Type*} [DecidableEq α] [Fintype α] [Nonempty α]

/-- The Kraft weight of a word `w` is `D^{-|w|}` where `D` is the alphabet size. -/
noncomputable def kraftWeight (w : List α) : ℝ :=
  (1 / (Fintype.card α : ℝ)) ^ w.length

/-- **Kraft's Inequality**: If `S` is a finite prefix-free code over an alphabet of size `D`,
then `∑_{w ∈ S} D^{-|w|} ≤ 1`.

This follows from the Kraft-McMillan inequality since prefix-free codes are uniquely decodable. -/
theorem kraft_inequality {S : Finset (List α)} (hpf : PrefixFree (S : Set (List α))) :
    ∑ w ∈ S, kraftWeight w ≤ 1 := by
  unfold kraftWeight
  by_cases he : [] ∈ S
  · simp
    have h_eq : S = {[]} := by
      exact_mod_cast hpf.epsilon_singleton he
    subst h_eq
    simp
  · have hud : UniquelyDecodable (S : Set (List α)) :=
      hpf.uniquely_decodable he
    simpa using (kraft_mcmillan_inequality hud)

/-- **Kraft's Inequality (Infinite)**: If `S` is a prefix-free code (possibly infinite),
then the series `∑ D^{-|w|}` (a) converges and (b) its sum is at most 1.

The proof shows that every finite subset satisfies the bound (by the finite Kraft inequality),
which implies summability. The tsum bound then follows from summability. -/
theorem kraft_inequality_infinite {S : Set (List α)} (h : PrefixFree S) :
    HasSum (fun w : S => kraftWeight (w : List α))
              (∑' w : S, kraftWeight (w : List α))
            ∧ (∑' w : S, kraftWeight (w : List α)) ≤ 1 := by
  -- Bound every finite partial sum
  have h_bound :
      ∀ (F : Finset S), (∑ w ∈ F, kraftWeight (w : List α)) ≤ 1 := by
    intro F

    let F_val : Finset (List α) := F.image Subtype.val

    have h_subset : (F_val : Set (List α)) ⊆ S := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨y, _, rfl⟩
      exact y.property

    -- Rewrite the sum over subtypes as a sum over values
    have hsum : (∑ w ∈ F, kraftWeight (w : List α)) = ∑ x ∈ F_val, kraftWeight x := by
      simp [F_val]

    rw [hsum]
    exact kraft_inequality (h.mono h_subset)

  -- Prove summability using the finite bound
  have h_summable : Summable (fun w : S => kraftWeight (w : List α)) :=
    summable_of_sum_le (fun _ => by unfold kraftWeight; positivity) h_bound

  -- Return HasSum (convergence) and the bound
  exact ⟨h_summable.hasSum, h_summable.tsum_le_of_sum_le h_bound⟩

end InformationTheory
