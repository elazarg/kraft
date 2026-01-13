/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Basic

/-- Mapping an injective function over lists is injective. -/
lemma List.map_injective' {α β} {f : α → β} (hf : Function.Injective f) :
    Function.Injective (List.map f) := by
  intro a b hab
  revert b
  induction a with
  | nil =>
      intro b hab
      cases b with
      | nil => rfl
      | cons b bs =>
          -- [] = f b :: ... is impossible
          have : False := by simp at hab
          exact False.elim this
  | cons a as ih =>
      intro b hab
      cases b with
      | nil =>
          -- f a :: ... = [] is impossible
          have : False := by simp at hab
          exact False.elim this
      | cons b bs =>
          -- (f a :: ...) = (f b :: ...) → f a = f b and tails equal
          injection hab with h1 h2
          have hab' : a = b := hf h1
          have htail : as = bs := ih h2
          simp [hab', htail]

/-- Mapping an injective function over lists preserves prefix relationships in both directions. -/
lemma List.IsPrefix.map_iff {α β : Type _} {f : α → β} (hf : Function.Injective f)
    {l₁ l₂ : List α} :
    l₁.map f <+: l₂.map f ↔ l₁ <+: l₂ := by
  constructor
  · intro h
    rcases h with ⟨t, ht⟩

    -- Take the first `l₁.length` elements on both sides of `l₁.map f ++ t = l₂.map f`
    have htake : (l₂.map f).take l₁.length = l₁.map f := by
      have := congrArg (fun s => s.take l₁.length) ht
      simpa [List.take_append, List.length_map] using this.symm

    -- Rewrite `take` over `map` as `map` over `take`
    have htake' : (l₂.take l₁.length).map f = l₁.map f := by
      rw [<-htake]
      simp

    have hmap_inj : Function.Injective (List.map f) := List.map_injective' (f := f) hf

    have htakes : l₂.take l₁.length = l₁ := hmap_inj htake'

    refine ⟨l₂.drop l₁.length, ?_⟩
    -- `take_append_drop` says: take n l₂ ++ drop n l₂ = l₂
    simpa [htakes] using (List.take_append_drop l₁.length l₂)

  · intro h
    exact List.IsPrefix.map f h

/-- `Fin.val` is injective. -/
lemma Fin.val_injective' {n : ℕ} : Function.Injective (Fin.val : Fin n → ℕ) :=
  Fin.val_injective
