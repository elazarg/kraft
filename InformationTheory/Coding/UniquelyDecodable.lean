/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Group.Defs

/-!
# Uniquely Decodable Codes

This file defines uniquely decodable codes and proves basic properties.

## Main definitions

* `UniquelyDecodable`: A set of codewords is uniquely decodable if distinct concatenations
  of codewords yield distinct strings.

## Main results

* `UniquelyDecodable.epsilon_not_mem`: Uniquely decodable codes cannot contain the empty
  string.
* `UniquelyDecodable.flatten_injective`: The flatten function is injective on lists of
  codewords from a uniquely decodable code.
-/

namespace InformationTheory

variable {M : Type*} [Monoid M]

/-- A set of lists is uniquely decodable if distinct concatenations yield distinct strings. -/
def UniquelyDecodable (S : Set M) : Prop :=
  ∀ (L1 L2 : List M),
    (∀ w ∈ L1, w ∈ S) → (∀ w ∈ L2, w ∈ S) →
    L1.prod = L2.prod → L1 = L2

variable {S : Set M}

/-- If a code is uniquely decodable, it does not contain the empty string.

The empty string can be "decoded" as either zero or two copies of itself,
violating unique decodability. -/
lemma UniquelyDecodable.one_not_mem (h : UniquelyDecodable S) : (1 : M) ∉ S := by
  intro h1
  unfold UniquelyDecodable at h
  -- decode 1 as [1] and as [1,1]
  specialize h [1] [1,1] (by simp [h1]) (by simp [h1]) (by simp)
  simp at h

lemma UniquelyDecodable.prod_injective (h : UniquelyDecodable S) :
    Function.Injective (fun (L : {L : List M // ∀ x ∈ L, x ∈ S}) => L.1.prod) := by
  intro L1 L2 hprod
  apply Subtype.ext
  exact h L1.1 L2.1 L1.2 L2.2 hprod

def listMonoid (α : Type*) : Monoid (List α) :=
  { mul := List.append
    one := []
    mul_assoc := List.append_assoc
    one_mul := by intro a; change ([] ++ a) = a; simp
    mul_one := List.append_nil }

end InformationTheory
