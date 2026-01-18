/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# List and Finset Helpers

This file provides utility lemmas for lists, prefixes, and injective mappings.

## Main results

* `List.prefix_map_iff`: Mapping preserves prefix relationships.
-/

/-- Mapping an injective function over lists preserves prefix relationships in both directions. -/
lemma List.IsPrefix.map_iff {α β : Type*} {f : α → β} (hf : Function.Injective f)
    {l₁ l₂ : List α} :
    l₁.map f <+: l₂.map f ↔ l₁ <+: l₂ := by
  constructor
  · intro h
    rcases h with ⟨t, ht⟩

    have htake' : (l₂.take l₁.length).map f = l₁.map f := by
      have := congrArg (fun s => s.take l₁.length) ht.symm
      simpa [List.take_append, List.length_map] using this

    refine ⟨l₂.drop l₁.length, ?_⟩
    -- `take_append_drop` says: take n l₂ ++ drop n l₂ = l₂
    simpa [Function.Injective.list_map hf htake'] using (List.take_append_drop l₁.length l₂)

  · intro h
    exact List.IsPrefix.map f h

/-- a small helper -/
lemma range_eq_Iio (n : ℕ) : (Finset.range n : Finset ℕ) = Finset.Iio n := by
  ext k
  simp [Finset.mem_Iio]  -- gives: k ∈ Iio n ↔ k < n, same as mem_range
