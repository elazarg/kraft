
/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
import Mathlib.Data.Finset.Card

namespace Kraft

variable {α : Type _}

/-- A set of lists is uniquely decodable if distinct concatenations yield distinct strings. -/
def UniquelyDecodable (S : Set (List α)) : Prop :=
  ∀ (L1 L2 : List (List α)),
    (∀ w ∈ L1, w ∈ S) → (∀ w ∈ L2, w ∈ S) →
    L1.flatten = L2.flatten → L1 = L2

/-- If a code is uniquely decodable, it does not contain the empty string.

The empty string ε can be "decoded" as either zero or two copies of itself,
violating unique decodability. -/
lemma UniquelyDecodable.epsilon_not_mem
    {S : Set (List α)}
    (h : UniquelyDecodable S) :
    [] ∉ S := by
  intro h_in
  -- UniquelyDecodable implies [] cannot be decomposed in two ways.
  -- But if [] ∈ S, then [] = [] (1 part) and [] = [] ++ [] (2 parts).
  unfold UniquelyDecodable at h
  specialize h (L1 := [[]]) (L2 := [[], []]) (by simp [h_in]) (by simp [h_in]) (by simp)
  simp at h

variable {α : Type _}

lemma UniquelyDecodable.flatten_injective
  {S : Set (List α)} (h : UniquelyDecodable S) :
  Function.Injective (fun (L : {L : List (List α) // ∀ x ∈ L, x ∈ S}) => L.1.flatten) := by
  intro L1 L2 hflat
  apply Subtype.ext
  exact h L1.1 L2.1 L1.2 L2.2 hflat

end Kraft
