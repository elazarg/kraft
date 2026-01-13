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

section Definitions

variable {α : Type _} [DecidableEq α]

/-- A set of lists is prefix-free if no element is a strict prefix of another. -/
def PrefixFree (S : Set (List α)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x <+: y → x = y

/-- A set of lists is uniquely decodable if distinct concatenations yield distinct strings. -/
def UniquelyDecodable (S : Set (List α)) : Prop :=
  ∀ (L1 L2 : List (List α)),
    (∀ w ∈ L1, w ∈ S) → (∀ w ∈ L2, w ∈ S) →
    L1.flatten = L2.flatten → L1 = L2

end Definitions

end Kraft
