/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

import Mathlib.Order.Filter.Tendsto
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Analysis.SpecificLimits.Normed

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace Kraft

section concatFn

variable {α : Type _}

def concatFn {S : Set (List α)} {r : ℕ} (w : Fin r → S) : List α :=
  (List.ofFn (fun i : Fin r => (w i).val)).flatten

@[simp]
lemma concatFn_def {S : Set (List α)} {r : ℕ} (w : Fin r → S):
  concatFn w = (List.ofFn (fun i : Fin r => (w i).val)).flatten :=
  rfl

def concatImage [DecidableEq α] {S : Finset (List α)} {r : ℕ} : Finset (List α) :=
  (Finset.univ : Finset (Fin r → (S : Set (List α)))).image concatFn

lemma concatFn_length {S : Set (List α)} {r : ℕ} (w : Fin r → S):
  (concatFn w).length = ∑ i : Fin r, (w i).val.length := by
  simp [concatFn, List.length_flatten, List.sum_ofFn]

lemma concatFn_length_le_mul_sup {Sf : Finset (List α)} {r : ℕ}
    (ws : Fin r → (Sf : Set (List α))) :
  (concatFn ws).length ≤ r * (Sf.sup List.length) := by
  have h_each : ∀ i : Fin r, (ws i).val.length ≤ Sf.sup List.length := by
    intro i
    -- (w i).property : (w i).val ∈ (S : Set _)
    exact Finset.le_sup (f := List.length) (by simp)

  have hsum :
      (∑ i : Fin r, (ws i).val.length) ≤ ∑ i : Fin r, Sf.sup List.length := by
    -- `Fintype.sum` is definitionaly `Finset.univ.sum`
    simpa using
      (Finset.sum_le_sum (s := (Finset.univ : Finset (Fin r)))
        (fun i _ => h_each i))

  calc
    (concatFn ws).length
        = ∑ i : Fin r, (ws i).val.length := concatFn_length (w := ws)
    _ ≤ ∑ i : Fin r, Sf.sup List.length := hsum
    _ = r * (Sf.sup List.length) := by
      -- sum of a constant over `Fin r`
      simp [Fintype.card_fin]

lemma le_concatFn_length_of_no_empty {S : Set (List α)} {r : ℕ} (w : Fin r → S) (hε : ([] : List α) ∉ S):
  r ≤ (concatFn w).length := by
  have h_each : ∀ i : Fin r, (1 : ℕ) ≤ (w i).val.length := by
    intro i
    have hne : (w i).val ≠ ([] : List α) := by
      intro h0
      apply hε
      simpa [h0] using (w i).property
    -- `0 < length` -> `1 ≤ length`
    have : 0 < (w i).val.length := List.length_pos_iff.2 hne
    simpa using (Nat.succ_le_iff.2 this)  -- succ 0 = 1

  have hsum :
      (∑ i : Fin r, (1 : ℕ)) ≤ ∑ i : Fin r, (w i).val.length := by
    simpa using
      (Finset.sum_le_sum (s := (Finset.univ : Finset (Fin r)))
        (fun i _ => h_each i))

  -- rewrite `∑ i : Fin r, 1` as `r`
  have hone : (∑ i : Fin r, (1 : ℕ)) = r := by
    simp [Fintype.card_fin]

  calc
    r = ∑ i : Fin r, (1 : ℕ) := by simp [hone]
    _ ≤ ∑ i : Fin r, (w i).val.length := hsum
    _ = (concatFn w).length := by simpa using (concatFn_length (w := w)).symm

end concatFn
