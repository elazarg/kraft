import Mathlib.Data.List.Basic

-- We treat "Words" as lists of booleans (bits)
abbrev Word := List Bool
-- A "Code" is a set of Words
abbrev Code := Set Word

/-! ## Definitions -/

/-- Definition 3.1: A code is prefix-free if no codeword is a prefix of another. -/
def PrefixFree (S : Code) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x <+: y → x = y

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

/-! ## The Main Theorem -/

-- If you join a list of words and get nothing,
-- and the code doesn't allow empty words,
-- then the list must be empty.
lemma flatten_eq_nil_of_no_empty_word {S : Code} {L : List Word}
    (h_eps : [] ∉ S)
    (h_in : ∀ w ∈ L, w ∈ S)
    (h_flat : L.flatten = []) :
    L = [] := by
  cases L with
  | nil => rfl
  | cons w L' =>
    -- If L is (w :: L'), then w ++ L'.flatten = [].
    -- This implies w = [].
    simp at h_flat
    have w_empty : w = [] := h_flat.1
    -- But w must be in S, and S doesn't allow [], so contradiction.
    have w_in_S : w ∈ S := h_in w (by simp)
    rw [w_empty] at w_in_S
    contradiction

/--
Geometric intuition: If two rows of tiles have the same total length,
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
  apply List.take_prefix

/-- Theorem 3.4: A prefix-free code (without empty word) is uniquely decodable. -/
theorem prefix_free_implies_uniquely_decodable
  (S : Code)
  (h_pf : PrefixFree S)
  (h_eps : [] ∉ S) :
  UniquelyDecodable S := by
  -- We start by introducing the two decompositions L₁ and L₂
  intro L₁ L₂ hS₁ hS₂ h_join

  -- The proof in the text is by strong induction on the length of the target string `x`.
  -- Let `x` be the string formed by joining the words.
  let x := L₁.flatten
  have hx : x = L₁.flatten := rfl

  -- We set up strong induction on `n = x.length`.
  -- We generalize L₁ and L₂ because they will change in the inductive step (we peel off the heads).
  generalize h_len : x.length = n
  revert L₁ L₂ x

  induction n using Nat.strongRecOn with
    | ind n ih =>
      -- We re-introduce the variables that depend on n
      intro L₁ L₂ hS₁ hS₂ h_join_eq flat1 flat_is_flatten flat_len

      -- Now 'ih' is available with the type:
      -- ih : ∀ (m : ℕ), m < n → ∀ (x : List Word) ...
      -- 1. Split on L₁
      cases L₁ with
      | nil =>
        -- Case: L₁ = []
        -- We know L₁.flatten is [], so L₂.flatten is [].
        -- Helper lemma proves L₂ must be [] too.
        rw [List.flatten_nil] at h_join_eq
        symm at h_join_eq
        have L₂_nil := flatten_eq_nil_of_no_empty_word h_eps hS₂ h_join_eq
        rw [L₂_nil]

      | cons w₁ L₁' =>
        -- Case: L₁ = w₁ :: L₁'
        cases L₂ with
        | nil =>
          -- Case: L₂ = [] but L₁ is not. Symmetric contradiction.
          rw [List.flatten_nil] at h_join_eq
          have L₁_nil := flatten_eq_nil_of_no_empty_word h_eps hS₁ h_join_eq
          injection L₁_nil -- "cons w₁ L₁' = nil" is impossible

        | cons z₁ L₂' =>
          -- Case: L₁ = w₁ :: L₁' AND L₂ = z₁ :: L₂'
          -- This is where the real math happens.

          -- Simplify the flatten equality: (w₁ ++ L₁'.flatten) = (z₁ ++ L₂'.flatten)
          simp only [List.flatten_cons] at h_join_eq

          -- Assume wlog that |w₁| ≤ |z₁|
          rcases Nat.le_total w₁.length z₁.length with h_len_le | h_len_le

          -- SUBCASE 1: |w₁| ≤ |z₁|
          ·
            -- 1. Prove w₁ is a prefix of z₁
            have h_prefix : w₁ <+: z₁ := by
              apply prefix_of_append_le h_join_eq h_len_le

            -- 2. Use PrefixFree to prove w₁ = z₁
            have h_eq_wz : w₁ = z₁ := by
              apply h_pf w₁ (hS₁ w₁ (by simp)) z₁ (hS₂ z₁ (by simp))
              exact h_prefix

            -- 3. Now we know w₁ = z₁, we can "cancel" them
            subst h_eq_wz
            -- "Subtract" w₁ from the equation
            simp

            -- 4. PREPARE for the Induction Hypothesis
            -- Define the new length explicitly
            let m := L₁'.flatten.length

            -- Prove strictly smaller length separately
            have h_lt : m < n := by
               -- Unwrap the generalized variables
               subst n flat1
               -- Use list arithmetic
               rw [List.flatten_cons, List.length_append]
               apply Nat.lt_add_of_pos_left
               apply List.length_pos_of_ne_nil
               -- Contradiction with empty word
               intro h_nil
               apply h_eps
               rw [←h_nil]
               apply hS₁
               apply List.mem_cons_self

            -- 5. Apply IH
            apply ih m h_lt L₁' L₂'
            · intro w hw; apply hS₁; exact List.mem_cons_of_mem _ hw
            · intro w hw; apply hS₂; exact List.mem_cons_of_mem _ hw
            · simp only [List.append_cancel_left_eq] at h_join_eq
              exact h_join_eq -- Pass the "cancelled" equation here
            · rfl -- x = flatten
            · rfl -- len = m
          -- SUBCASE 2: |z₁| ≤ |w₁|
          ·
            -- This block is identical to Subcase 1, just swap w₁ and z₁
            sorry
