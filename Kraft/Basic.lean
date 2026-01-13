/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin

namespace Kraft

variable {α : Type _}

/-- A set of lists is prefix-free if no element is a strict prefix of another. -/
def PrefixFree (S : Set (List α)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x <+: y → x = y

lemma epsilon_prefix_singleton {S : Set (List α)} (hS : PrefixFree S) :
    [] ∈ S → S = {[]} := by
  intro h_nil
  ext x
  constructor
  · -- Forward: x ∈ S → x = []
    intro hx
    -- Since [] is a prefix of x, and both are in S, they must be equal
    have := hS _ h_nil _ hx List.nil_prefix
    simp [this.symm]
  · -- Backward: x = [] → x ∈ S
    rintro rfl
    exact h_nil

end Kraft
