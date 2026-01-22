/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Order.Filter.Tendsto
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.FreeMonoid.Basic

import InformationTheory.Coding.UniquelyDecodable
import InformationTheory.Coding.KraftGeneralized

/-!
# Kraft-McMillan Inequality

This file proves the Kraft-McMillan inequality for uniquely decodable codes.

## Main results

* `kraft_mcmillan_inequality`: For a uniquely decodable code `S` over an alphabet of size
  `D`, `∑_{w ∈ S} D^{-|w|} ≤ 1`.

The proof uses a counting argument: the `r`-th power of the Kraft sum counts concatenations of
`r` codewords, weighted by length. Since the code is uniquely decodable, these concatenations are
distinct, and the count is bounded by the number of strings of each length.

## References

* McMillan, B. (1956), "Two inequalities implied by unique decipherability"
-/

namespace InformationTheory

variable {α : Type*}

private instance : Monoid (List α) := listMonoid α

@[simp] private lemma mul_list (a b : List α) : a * b = a ++ b := rfl

/-- For uniquely decodable codes, the concatenation map is injective.

This is the key property: distinct tuples of codewords produce distinct concatenations. -/
private lemma uniquely_decodable_tupleProduct_injective {S : Finset (List α)}
    (h : UniquelyDecodable (S : Set (List α))) (r : ℕ) :
    Function.Injective (prodTuple (S := S) (r := r)) := by
  intro w₁ w₂ hflat
  have hprod :
      (List.ofFn (fun i => (w₁ i).val)).prod =
      (List.ofFn (fun i => (w₂ i).val)).prod := by
    simpa using hflat
  have : (fun i : Fin r => (w₁ i).val) = fun i => (w₂ i).val :=
    List.ofFn_injective (h _ _ (by simp) (by simp) hprod)
  funext i
  exact Subtype.ext (by simpa using congrArg (fun f => f i) this)

private lemma lengthGrowth_list [Fintype α]:
    ExpBounded (M := List α) (len := List.length) (base := Fintype.card α) := by
  classical
  intro T s
  let all_words := (Finset.univ : Finset (Fin s → α)).image List.ofFn
  have hsub : T.filter (fun x => x.length = s) ⊆ all_words := by
    intro a ha
    have halen : a.length = s := (Finset.mem_filter.mp ha).right
    apply Finset.mem_image.mpr
    refine ⟨(fun j : Fin s => a.get ⟨j.val, by simp [halen]⟩), ?_, ?_⟩
    · exact Finset.mem_univ _
    · exact List.ext_get (by simp [halen]) (by simp)
  have hcard_all : all_words.card = Fintype.card α ^ s := by
    -- `List.ofFn` is injective, so the image has the same cardinality as the domain.
    simpa using
      (Finset.card_image_of_injective
        (s := (Finset.univ : Finset (Fin s → α)))
        (f := (List.ofFn : (Fin s → α) → List α))
        List.ofFn_injective)
  calc
    (T.filter (fun x => x.length = s)).card
        ≤ all_words.card := Finset.card_le_card hsub
    _ = Fintype.card α ^ s := hcard_all

public theorem kraft_mcmillan_inequality {S : Finset (List α)} [Fintype α] [Nonempty α]
    (h : UniquelyDecodable (S : Set (List α))) :
    ∑ w ∈ S, (1 / Fintype.card α : ℝ) ^ w.length ≤ 1 := by
  refine kraft_inequality_of_injective_real
    (D_nat := Fintype.card α)
    (D_pos := Fintype.card_pos)
    (h_add := by simp)
    (h_growth := lengthGrowth_list)
    (h_inj := fun r => uniquely_decodable_tupleProduct_injective h r)

end InformationTheory
