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

## Main results

* `kraft_inequality`: For a finite prefix-free code `S` over an alphabet of size `D`,
  `∑_{w ∈ S} D^{-|w|} ≤ 1`.
* `kraft_inequality_infinite`: Extension to infinite prefix-free codes via `tsum`.

## References

* Cover & Thomas, *Elements of Information Theory*, Chapter 5
-/

namespace InformationTheory

variable {α : Type*} [DecidableEq α] [Fintype α] [Nonempty α]

/-- **Kraft's Inequality**: If `S` is a finite prefix-free code over an alphabet of size `D`,
then `∑_{w ∈ S} D^{-|w|} ≤ 1`.

This follows from the Kraft-McMillan inequality since prefix-free codes are uniquely decodable. -/
theorem kraft_inequality {S : Finset (List α)} (hpf : PrefixFree (S : Set (List α))) :
    ∑ w ∈ S, (1 / (Fintype.card α) : ℝ) ^ w.length ≤ 1 := by
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
then the series `∑ D^{-|w|}` converges and its sum is at most 1.

The proof shows that every finite subset satisfies the bound (by the finite Kraft inequality),
which implies summability. The tsum bound then follows from summability. -/
theorem kraft_inequality_infinite {S : Set (List α)} (h : PrefixFree S) :
    HasSum (fun w : S => (1 / (Fintype.card α) : ℝ) ^ (w : List α).length) (∑' w : S, (1 / (Fintype.card α) : ℝ) ^ (w : List α).length)
    ∧ (∑' w : S, (1 / (Fintype.card α) : ℝ) ^ (w : List α).length) ≤ 1 := by
  let D : ℝ := Fintype.card α

  -- 1) bound every finite partial sum
  have h_bound :
      ∀ (F : Finset S), (∑ w ∈ F, (1 / D) ^ (w : List α).length) ≤ 1 := by
    intro F
    let F_val : Finset (List α) := F.image Subtype.val
    have h_subset : (F_val : Set (List α)) ⊆ S := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨y, _, rfl⟩
      exact y.property

    -- rewrite the sum over subtypes as a sum over values
    have hsum :
        (∑ w ∈ F, (1 / D) ^ (w : List α).length)
          =
        ∑ x ∈ F_val, (1 / D) ^ x.length := by
      simp [F_val]
    -- combine
    rw [hsum]
    simpa [D] using (kraft_inequality (h.mono h_subset))

  -- 2. Prove summability using the finite bound
  have h_summable : Summable (fun w : S => (1 / D) ^ (w : List α).length) :=
    summable_of_sum_le (fun _ => by positivity) h_bound

  -- 3. Return HasSum (convergence) and the bound
  exact ⟨h_summable.hasSum, h_summable.tsum_le_of_sum_le h_bound⟩

end InformationTheory
