/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

import InformationTheory.Coding.UniquelyDecodable

namespace Kraft

variable {α : Type _}

/-- A set of lists is prefix-free if no element is a strict prefix of another. -/
def PrefixFree (S : Set (List α)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x <+: y → x = y

/-- If a prefix-free set contains the empty string, it must be the singleton `{[]}`.

The empty string is a prefix of every string, so prefix-freeness forces all elements to equal `[]`. -/
lemma epsilon_prefix_singleton {S : Set (List α)} (hS : PrefixFree S) :
    [] ∈ S → S = {[]} := by
  intro h_nil
  rw [Set.eq_singleton_iff_unique_mem]
  constructor
  · exact h_nil
  · intro x hx
    -- Since [] is a prefix of x, and both are in S, they must be equal
    simp [hS _ h_nil x hx, List.nil_prefix]

lemma PrefixFree.mono {α : Type _} {S T : Set (List α)} (hS : PrefixFree S) (hST : T ⊆ S) :
  PrefixFree T := by
  intro a ha b hb hpre
  exact hS a (hST ha) b (hST hb) hpre

/-- Prefix-free codes are uniquely decodable.

If `S` is prefix-free (no codeword is a prefix of another) and does not contain the empty string,
then any string formed by concatenating codewords from `S` can be parsed into those codewords
in exactly one way.

The proof proceeds by structural induction on the list of codewords `L₁`.. -/
theorem PrefixFree.uniquely_decodable
    {α : Type _}
    {S : Set (List α)}
    (h0 : [] ∉ S)
    (hS : PrefixFree S) :
    UniquelyDecodable S := by
  -- We prove that for any two lists of codewords L₁ and L₂, if they flatten to the same string, they are identical.
  intro L₁ L₂ hL₁ hL₂ hflatten

  -- Structural induction on L₁ generalizing L₂ handles the "peeling off" logic automatically.
  induction L₁ generalizing L₂ with
  | nil =>
    -- Case: L₁ is empty. Then L₂ must also be empty (since [] ∉ S).
    cases L₂
    · rfl
    · -- Contradiction: L₂ has a head w, but flatten L₂ = [] implies w = []
      exfalso
      simp at hflatten
      rcases hflatten with ⟨rfl, -⟩
      exact h0 (hL₂ _ (.head ..))
  | cons w₁ L₁' ih =>
    -- Case: L₁ = w₁ :: L₁'
    cases L₂ with
    | nil =>
      -- identical to "Case: L₁ is empty."
      exfalso
      simp at hflatten
      rcases hflatten with ⟨rfl, -⟩
      exact h0 (hL₁ _ (.head ..))
    | cons w₂ L₂' =>
      -- Case: L₂ = w₂ :: L₂'. We have w₁ ++ ... = w₂ ++ ...
      simp only [List.flatten_cons] at hflatten

      -- Key Step: Use the fact that one head must be a prefix of the other.
      -- List.append_eq_append_iff splits this into two cases: w₁ = w₂ ++ t  OR  w₂ = w₁ ++ t
      rw [List.append_eq_append_iff] at hflatten

      -- We prove w₁ = w₂ using the PrefixFree property.
      have hw : w₁ = w₂ := by
        cases hflatten with
        | inl h => -- w₂ is a prefix of w₁
          rcases h with ⟨t, hw₁, _⟩
          -- hS w₂ ... w₁ ... (w₂ is prefix of w₁) implies w₂ = w₁
          exact hS w₁ (hL₁ _ (.head ..)) w₂ (hL₂ _ (.head ..)) ⟨t, hw₁.symm⟩
        | inr h => -- w₁ is a prefix of w₂
          rcases h with ⟨t, hw₂, _⟩
          exact (hS w₂ (hL₂ _ (.head ..)) w₁ (hL₁ _ (.head ..)) ⟨t, hw₂.symm⟩).symm

      -- Now that we know heads are equal, we substitute and recurse.
      -- We proved the heads are equal, so unify them.
      subst hw
      simp
      simp at hflatten

      -- Apply the induction hypothesis to the tails
      apply ih L₂'
      · -- Solve: ∀ w ∈ L₁', w ∈ S (using hL₁)
        intros w hw; exact hL₁ w (.tail _ hw)
      · -- Solve: ∀ w ∈ L₂', w ∈ S (using hL₂)
        intros w hw; exact hL₂ w (.tail _ hw)
      · -- Solve the flattened equality
        rcases hflatten with h | h <;> simp [h]

/--
Prefix-free codes with at least two codewords are uniquely decodable.

This variant avoids explicitly assuming `[] ∉ S` by deriving it from the cardinality
constraint: if `|S| ≥ 2` and `S` is prefix-free, then `[]` cannot be in `S`
(since `[]` is a prefix of every other string). -/
theorem PrefixFree.is_uniquely_decodable_of_card_ge_two
    {α : Type _}
    (S : Finset (List α))
    (hS : PrefixFree (S: Set (List α)))
    (h_card : S.card ≥ 2) :
    UniquelyDecodable (S: Set (List α)) := by
    -- We prove [] ∉ S by contradiction.
  have h0 : [] ∉ S := by
    intro h_nil
    -- If [] ∈ S, then for any w ∈ S, [] is a prefix of w.
    -- By prefix-freeness, this means w must be [].
    have h_subset : S ⊆ {[]} := by
      intro w hw
      have := hS _ h_nil _ hw -- [] <+: w implies [] = w
      simp [this]

    -- If S ⊆ {[]}, then |S| ≤ 1, which contradicts |S| ≥ 2.
    have : S.card ≤ 1 := Finset.card_le_card h_subset
    omega

  -- Now delegate to the main theorem
  exact hS.uniquely_decodable h0

end Kraft
