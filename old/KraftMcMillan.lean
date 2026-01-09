import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith

import Kraft.DyadicHelpers
import Kraft.UniquelyDecodable

open BigOperators Real

namespace Kraft

variable {S : Code}

/-- The extension of a code to 'r' concatenations.
    This corresponds to S^r in the text. -/
def code_extension (S : Code) (r : ℕ) : Finset (Fin r → Word) :=
  Fintype.piFinset (fun _ => S)

/-- The "flattening" map: (w₁, ..., wᵣ) ↦ w₁ ++ ... ++ wᵣ -/
def concat_tuple (f : Fin r → Word) : Word :=
  (List.ofFn f).flatten

/-- The Key Lemma:
    (Σ 2^-|w|)^r = Σ 2^-|w₁...wᵣ|
-/
lemma kraft_sum_pow_eq_sum_extension (r : ℕ) :
    (∑ w ∈ S, (2 : ℝ) ^ (-(w.length : ℝ))) ^ r =
    ∑ f ∈ code_extension S r, (2 : ℝ) ^ (-(concat_tuple f).length : ℝ) := by
  -- 1. Convert power of sum to sum over Pi-type (S^r)
  rw [Finset.sum_pow']
  -- 2. This gives a sum over f : Fin r → Word.
  --    Target: ∏ i, 2^-|f i| = 2 ^ -(∑ |f i|)
  apply Finset.sum_congr rfl
  intro f hf
  rw [← Real.rpow_sum_of_pos (by norm_num)]
  -- 3. Match the length of the flattened list
  congr 1
  rw [neg_inj, concat_tuple]
  simp [List.length_flatten, List.sum_ofFn]

/-- The Unique Decodability Lemma:
    If S is UD, then the map (w₁...wᵣ) ↦ w₁++...++wᵣ is injective. -/
lemma extension_injective
    (hUD : UniquelyDecodable S) (r : ℕ) :
    Set.InjOn concat_tuple (code_extension S r) := by
  intro f g hf hg h_eq
  dsimp [concat_tuple] at h_eq
  -- We apply the definition of UniquelyDecodable.
  -- We need to pass it two lists: List.ofFn f and List.ofFn g
  apply UniquelyDecodable.of_lists_eq hUD (List.ofFn f) (List.ofFn g)
  · -- Proof that elements of f are in S
    intro w hw
    rw [List.mem_ofFn] at hw
    rcases hw with ⟨i, rfl⟩
    -- The fact that f ∈ code_extension S r means ∀ i, f i ∈ S
    rw [code_extension, Fintype.mem_piFinset] at hf
    exact hf i
  · -- Proof that elements of g are in S
    intro w hw
    rw [List.mem_ofFn] at hw
    rcases hw with ⟨i, rfl⟩
    rw [code_extension, Fintype.mem_piFinset] at hg
    exact hg i
  · -- The flattened lists are equal (hypothesis)
    exact h_eq
  -- Conclusion: List.ofFn f = List.ofFn g
  -- This implies f = g
  intro h_list_eq
  funext i
  rw [← List.ofFn_get (f) i, ← List.ofFn_get (g) i, h_list_eq]

end Kraft
