import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Card

import Kraft.PrefixFree

/-! ## Definitions -/

/--
  Definition 3.3: A code is uniquely decodable if every string can be
  decomposed into codewords in at most one way.

  In Lean, we formalize "decomposition" as a `List Word`.
  If two lists of codewords `L₁` and `L₂` join to make the same string,
  then `L₁` must equal `L₂`.
-/
def UniquelyDecodable (S : Code) : Prop :=
  ∀ (L₁ L₂ : List Word),
    (∀ w ∈ L₁, w ∈ S) →        -- All words in decomposition 1 are in S
    (∀ w ∈ L₂, w ∈ S) →        -- All words in decomposition 2 are in S
    L₁.flatten = L₂.flatten →  -- They form the same target string
    L₁ = L₂                    -- Conclusion: The decompositions are identical

lemma flatten_eq_nil_of_no_empty
    {L : List Word}
    (h_no_empty : ∀ w ∈ L, w ≠ ([] : Word))
    (h_flat : L.flatten = ([] : Word)) :
    L = [] := by
  cases L with
  | nil => rfl
  | cons w L' =>
    simp at h_flat  -- h_flat : w = [] ∧ L'.flatten = []
    have hw : w ≠ [] := h_no_empty _ (by simp)
    exact (hw h_flat.1).elim

-- If you join a list of words and get nothing,
-- and the code doesn't allow empty words,
-- then the list must be empty.
lemma flatten_eq_nil_of_no_empty_word {S : Code} {L : List Word}
    (h_eps : [] ∉ S)
    (h_in : ∀ w ∈ L, w ∈ S)
    (h_flat : L.flatten = []) :
    L = [] :=
  flatten_eq_nil_of_no_empty
    (by
      intro w hw
      have hwS : w ∈ S := h_in w hw
      intro hw_nil
      apply h_eps
      simpa [hw_nil] using hwS)
    h_flat


/--
If a list starts with a non-empty word, the flattened tail is strictly
shorter than the whole flattened list.
-/
lemma length_flatten_tail_lt_cons {w : Word} {L : List Word}
    (hw : w ≠ []) :
    L.flatten.length < (w :: L).flatten.length := by
  have hw_pos : 0 < w.length := by
    apply List.length_pos_of_ne_nil
    exact hw
  simp [List.flatten_cons, Nat.lt_add_of_pos_left hw_pos]


/--
Intuition: If two rows of tiles have the same total length,
and the first tile of the top row is shorter than the first tile of the bottom row,
then the top tile is a prefix of the bottom tile.
-/
lemma prefix_of_append_le {α : Type} {a b c d : List α}
  (h_eq : a ++ b = c ++ d)
  (h_le : a.length ≤ c.length) :
  a <+: c := by
  -- 1. 'a' is just the first length(a) characters of the whole string (LHS)
  have ha : a = (a ++ b).take a.length := by simp

  -- 2. Since LHS = RHS, we can swap them
  rw [h_eq] at ha

  -- 3. Now ha says: a = (c ++ d).take a.length
  -- Because length(a) ≤ length(c), taking length(a) from (c ++ d)
  -- is the same as just taking from c. 'd' is never touched.
  rw [List.take_append_of_le_length h_le] at ha

  -- 4. So a = c.take a.length.
  -- Taking the first n characters of c is always a prefix of c.
  rw [ha]
  exact (List.take_prefix _ _)


/-- Theorem 3.4: A prefix-free code (without empty word) is uniquely decodable. -/
theorem prefix_free_implies_uniquely_decodable
  (S : Code)
  (h_pf : PrefixFree S)
  (h_eps : [] ∉ S) :
  UniquelyDecodable S := by
  -- We start by introducing the two decompositions L₁ and L₂
  intro L₁ L₂ hS₁ hS₂ h_join

  -- We set up strong induction on `n = L₁.flatten.length`.
  -- We generalize L₁ and L₂ because they will change in the inductive step (we peel off the heads).
  generalize h_len : L₁.flatten.length = n
  revert L₁ L₂

  induction n using Nat.strongRecOn with
    | ind n ih =>
      -- Re-introduce the variables that depend on n
      intro L₁ L₂ hS₁ hS₂ h_join_eq flatten_L₁_n
      -- 1. Split on L₁
      cases L₁ with
      | nil =>
        -- Case: L₁ = []
        -- We know L₁.flatten is [], so L₂.flatten is [].
        -- Helper lemma proves L₂ must be [] too.
        symm at h_join_eq
        rw [List.flatten_nil] at h_join_eq
        rw [flatten_eq_nil_of_no_empty_word h_eps hS₂ h_join_eq]

      | cons w₁ L₁' =>

        -- Case: L₁ = w₁ :: L₁'
        cases L₂ with
        | nil =>
          -- Case: L₂ = [] but L₁ is not. Symmetric contradiction.
          rw [List.flatten_nil] at h_join_eq
          injection (flatten_eq_nil_of_no_empty_word h_eps hS₁ h_join_eq) -- "cons w₁ L₁' = nil" is impossible

        | cons z₁ L₂' =>
          -- Case: L₁ = w₁ :: L₁' AND L₂ = z₁ :: L₂'
          -- Simplify the flatten equality: (w₁ ++ L₁'.flatten) = (z₁ ++ L₂'.flatten)
          simp only [List.flatten_cons] at *
          wlog h_len : w₁.length ≤ z₁.length generalizing w₁ z₁ L₁' L₂'
          · -- ⊢ w₁ :: L₁' = z₁ :: L₂'
            symm
            -- Now apply the theorem ("this") with variables SWAPPED
            apply this _ _ hS₂ _ _ _ hS₁ _
            · -- ⊢ List.length z₁ ≤ List.length w₁
              apply Nat.le_of_not_le h_len
            · -- ⊢ (z₁ ++ L₂'.flatten).length = n
              rw [←h_join_eq]
              exact flatten_L₁_n
            · -- ⊢ z₁ ++ L₂'.flatten = w₁ ++ L₁'.flatten
              symm
              exact h_join_eq
          · -- Assume wlog that |w₁| ≤ |z₁|
            -- 1. prove w₁ = z₁
            have h_eq_wz : w₁ = z₁ := by
              apply h_pf (hS₁ _ (by simp)) (hS₂ _ (by simp))
              apply prefix_of_append_le h_join_eq h_len

            -- 2. Now we know w₁ = z₁
            subst h_eq_wz
            -- ⊢ w₁ :: L₁' = w₁ :: L₂'
            -- "Subtract" w₁ from the equation
            simp

            -- ⊢ L₁' = L₂'
            -- 3. Finally,  we can apply the Induction Hypothesis
            apply ih L₁'.flatten.length _ L₁' L₂' _ _ _ (by rfl)
            · -- Prove strictly smaller length
              subst n
              -- ⊢ L₁'.flatten.length < (w₁ ++ L₁'.flatten).length
              apply length_flatten_tail_lt_cons
              intro h_nil
              have w₁_in_S : w₁ ∈ S := hS₁ _ (by simp)
              have : ([] : Word) ∈ S := by simpa [h_nil] using w₁_in_S
              exact h_eps this
            · -- Prove L₁' is a valid code
              -- ⊢ ∀ (w : Word), w ∈ L₁' → w ∈ S
              intro w hw; apply hS₁; exact List.mem_cons_of_mem _ hw
            · -- Prove L₂' is a valid code
              -- ⊢ ∀ (w : Word), w ∈ L₂' → w ∈ S
              intro w hw; apply hS₂; exact List.mem_cons_of_mem _ hw
            · -- ⊢ L₁'.flatten = L₂'.flatten
              simp only [List.append_cancel_left_eq] at h_join_eq
              exact h_join_eq

/-- Corollary 3.2:
      If a finite set S of words is prefix-free and |S| ≥ 2
      then it is uniquely decodable.
-/
theorem prefix_free_of_card_ge_2_implies_UD
  (S : Code)
  (h_pf : PrefixFree S)
  (h_size : 2 ≤ S.card) :
  UniquelyDecodable S := by

  have h_eps_not : ([] : Word) ∉ S := by
    intro h_eps
    have : S.card ≤ 1 := by
      simp [prefixFree_singleton_nil (S:=S) h_pf h_eps]
    omega
  exact prefix_free_implies_uniquely_decodable S h_pf h_eps_not
