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

## Main definitions

* `concatFn`: Concatenation of `r` codewords into a single string.

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

section concatFn

variable {S : Finset (List α)} {r : ℕ}

private def concatFn (w : Fin r → S) : List α :=
  (List.ofFn (fun i => (w i).val)).flatten

private lemma concatFn.length (w : Fin r → S) :
    (concatFn w).length = ∑ i : Fin r, ((w i).val).length := by
  simp [List.sum_ofFn, concatFn]

end concatFn

private instance : Monoid (List α) := listMonoid α

@[simp] private lemma one_list : (1 : List α) = [] := rfl
@[simp] private lemma mul_list (a b : List α) : a * b = a ++ b := rfl

private lemma flatten_eq_prod (L : List (List α)) : L.flatten = L.prod := by
  induction L with
  | nil => simp
  | cons x xs ih => simp [ih]

private lemma concatFn_eq_prod {S : Finset (List α)} {r : ℕ} (w : Fin r → S) :
    concatFn (S := S) (r := r) w = (List.ofFn (fun i => (w i).val)).prod := by
  -- concatFn is flatten of that ofFn list
  simpa using flatten_eq_prod (List.ofFn (fun i => (w i).val))

/-- For uniquely decodable codes, the concatenation map is injective.

This is the key property: distinct tuples of codewords produce distinct concatenations. -/
private lemma uniquely_decodable_concatFn_injective {S : Finset (List α)}
    (h : UniquelyDecodable (S : Set (List α))) (r : ℕ) :
    Function.Injective (concatFn (S := S) (r := r)) := by
  intro w₁ w₂ hflat
  have hprod :
      (List.ofFn (fun i => (w₁ i).val)).prod =
      (List.ofFn (fun i => (w₂ i).val)).prod := by
    -- turn prods into concatFn
    simpa [concatFn_eq_prod (S := S) (r := r) w₁,
           concatFn_eq_prod (S := S) (r := r) w₂] using hflat
  have : (fun i : Fin r => (w₁ i).val) = fun i => (w₂ i).val :=
    List.ofFn_injective (h _ _ (by simp) (by simp) hprod)
  funext i
  exact Subtype.ext (by simpa using congrArg (fun f => f i) this)

/-- The number of strings of length `s` in any set is at most `D^s`
(the total number of such strings). -/
private lemma card_filter_length_eq_le [Fintype α] (T : Finset (List α)) (s : ℕ) :
    (T.filter (fun x => x.length = s)).card ≤ (Fintype.card α) ^ s := by
  classical
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

/-- `S` has no empty word. -/
private def NoEpsilon (S : Finset (List α)) : Prop :=
  ([] : List α) ∉ (S : Set (List α))

private lemma one_le_length_of_mem {S : Finset (List α)} (hε : NoEpsilon S) :
    ∀ x ∈ S, 1 ≤ x.length := by
  intro x hx
  have : x.length ≠ 0 := by
    intro hx0
    have : x = [] := by simpa [List.length_eq_zero_iff] using hx0
    exact hε (by simpa [this] using hx)
  exact Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero this)

-- Adapter: growth axiom packaged for lists
private lemma lengthGrowth_list [Fintype α]:
    lengthGrowth (M := List α) (ℓ := List.length) (D_nat := Fintype.card α) := by
  intro T s
  simpa using card_filter_length_eq_le (T := T) (s := s)

private lemma concatFn_succ_mul {S : Finset (List α)} {r : ℕ}
    (w : Fin (r + 1) → S) :
    concatFn (S := S) (r := r + 1) w
      = (w 0).val * concatFn (S := S) (r := r) (fun i : Fin r => w i.succ) := by
  -- reduce `*` to `++` just once, inside the proof
  change (List.ofFn (fun i : Fin (r + 1) => (w i).val)).flatten
      = (w 0).val ++ (List.ofFn (fun i : Fin r => (w i.succ).val)).flatten
  simp

-- Adapter: tupleProduct = concatFn for lists (monoid product = concatenation)
private lemma tupleProduct_eq_concatFn {S : Finset (List α)} {r : ℕ} {w : Fin r → S} :
    tupleProduct w = concatFn w := by
  induction r with
  | zero => rfl
  | succ r ih => simp [tupleProduct, concatFn_succ_mul, ih]

private lemma injective_tupleProduct_of_injective_concatFn
    {S : Finset (List α)} {r : ℕ}
    (hinj : Function.Injective (concatFn (S := S) (r := r))) :
    Function.Injective (tupleProduct (S := S) (r := r)) := by
  have hfc : tupleProduct (S := S) (r := r)
        = concatFn (S := S) (r := r) := by
    funext w
    simpa using tupleProduct_eq_concatFn
  simpa [hfc]

public theorem kraft_mcmillan_inequality {S : Finset (List α)} [Fintype α] [Nonempty α]
    (h : UniquelyDecodable (S : Set (List α))) :
    ∑ w ∈ S, (1 / Fintype.card α : ℝ) ^ w.length ≤ 1 := by
  refine kraft_inequality_of_injective (M := List α) (ℓ := List.length) (S := S)
    (D_nat := Fintype.card α)
    (D_pos := Fintype.card_pos)
    (h_add := by simp [List.length_append])
    (h_pos := one_le_length_of_mem (S := S) (by simpa using h.one_not_mem))
    (h_count := lengthGrowth_list)
    (h_inj := fun r => injective_tupleProduct_of_injective_concatFn
              (hinj := uniquely_decodable_concatFn_injective (S := S) h r))

end InformationTheory
