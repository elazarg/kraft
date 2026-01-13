
/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
import Kraft.Basic

namespace Kraft

variable {α : Type _}

/-- A set of lists is uniquely decodable if distinct concatenations yield distinct strings. -/
def UniquelyDecodable (S : Set (List α)) : Prop :=
  ∀ (L1 L2 : List (List α)),
    (∀ w ∈ L1, w ∈ S) → (∀ w ∈ L2, w ∈ S) →
    L1.flatten = L2.flatten → L1 = L2

lemma UniquelyDecodable.flatten_injective
  {S : Set (List α)} (h : UniquelyDecodable S) :
  Function.Injective (fun (L : {L : List (List α) // ∀ x ∈ L, x ∈ S}) => L.1.flatten) :=
by
  intro L1 L2 hflat
  -- Reduce to UD on the underlying lists; use Subtype.ext
  apply Subtype.ext
  exact h L1.1 L2.1 L1.2 L2.2 hflat

/-- If a code is uniquely decodable, it does not contain the empty string.

The empty string ε can be "decoded" as either zero or two copies of itself,
violating unique decodability. -/
lemma epsilon_not_mem_of_uniquely_decodable
    {S : Set (List α)}
    (h : UniquelyDecodable S) :
    [] ∉ S := by
  intro h_in
  -- UniquelyDecodable implies [] cannot be decomposed in two ways.
  -- But if [] ∈ S, then [] = [] (1 part) and [] = [] ++ [] (2 parts).
  unfold UniquelyDecodable at h
  specialize h (L1 := [[]]) (L2 := [[], []]) (by simp [h_in]) (by simp [h_in]) (by simp)
  simp at h

lemma prefixFree_uniqDecodable
    {S : Set (List α)} (hε : [] ∉ S) (hpf : PrefixFree S) :
    UniquelyDecodable S := by
  intro L1 L2 hL1 hL2 hflat
  -- Prove L1 = L2 by induction on L1, generalizing L2.
  revert L2
  induction L1 with
  | nil =>
      intro L2 hL2 hflat
      cases L2 with
      | nil =>
          rfl
      | cons b bs =>
          -- From [] = b ++ bs.flatten we get b = [], contradicting hε.
          have hbS : b ∈ S := hL2 b (by simp)
          have hbne : b ≠ ([] : List α) := by
            intro hb0
            apply hε
            simpa [hb0] using hbS
          have : b ++ bs.flatten = ([] : List α) := by
            -- hflat : [] = (b :: bs).flatten = b ++ bs.flatten
            simpa using hflat.symm
          have : b = ([] : List α) := (List.append_eq_nil_iff.mp this).1
          exact (hbne this).elim
  | cons a as ih =>
      intro L2 hL2 hflat
      cases L2 with
      | nil =>
          -- Symmetric contradiction: a ++ as.flatten = []
          have haS : a ∈ S := hL1 a (by simp)
          have hane : a ≠ ([] : List α) := by
            intro ha0
            apply hε
            simpa [ha0] using haS
          have : a ++ as.flatten = ([] : List α) := by
            simpa using hflat
          have : a = ([] : List α) := (List.append_eq_nil_iff.mp this).1
          exact (hane this).elim
      | cons b bs =>
          have haS : a ∈ S := hL1 a (by simp)
          have hbS : b ∈ S := hL2 b (by simp)

          have hL1_tail : ∀ x ∈ as, x ∈ S := by
            intro x hx
            exact hL1 x (by simp [hx])
          have hL2_tail : ∀ x ∈ bs, x ∈ S := by
            intro x hx
            exact hL2 x (by simp [hx])

          -- flatten equations expand to append equations
          have hab : a ++ as.flatten = b ++ bs.flatten := by
            simpa using hflat

          -- Compare heads via append_eq_append_iff: one is a prefix of the other.
          rw [List.append_eq_append_iff] at hab
          rcases hab with ⟨m, hm_head, hm_tail⟩ | ⟨m, hm_head, hm_tail⟩
          · -- Case: b = a ++ m
            have hapre : a <+: b := ⟨m, hm_head.symm⟩
            have hab_eq : a = b := hpf a haS b hbS hapre

            have ha_eq : a = a ++ m := by
              calc
                a = b := hab_eq
                _ = a ++ m := hm_head
            have ha_eq' : a ++ m = a := ha_eq.symm
            have hm_len0 : m.length = 0 := by
              have := congrArg List.length ha_eq'
              simpa [List.length_append] using this
            have hm_nil : m = ([] : List α) := List.length_eq_zero_iff.mp hm_len0

            have hflat_tail : as.flatten = bs.flatten := by
              simpa [hm_nil] using hm_tail

            have : as = bs := ih hL1_tail _ hL2_tail hflat_tail
            simp [hab_eq, this]
          · -- Case: a = b ++ m
            -- So b <+: a; prefix-free gives a = b, hence m = []
            have hbpre : b <+: a := ⟨m, hm_head.symm⟩
            have hab_eq : b = a := hpf b hbS a haS hbpre

            -- From a = b ++ m and b = a we get b = b ++ m, hence m = []
            have hb_eq : b = b ++ m := by
              calc
                b = a := hab_eq
                _ = b ++ m := hm_head
            have hb_eq' : b ++ m = b := hb_eq.symm
            have hm_len0 : m.length = 0 := by
              -- lengths: (b ++ m).length = b.length
              have := congrArg List.length hb_eq'
              -- simp gives b.length + m.length = b.length
              simpa [List.length_append] using this
            have hm_nil : m = ([] : List α) := List.length_eq_zero_iff.mp hm_len0

            -- Tail equality simplifies to as.flatten = bs.flatten
            have hflat_tail : as.flatten = bs.flatten := by
              -- hm_tail is the “rest” equality produced by append_eq_append_iff
              grind only

            -- Apply IH to tails
            have : as = bs := ih hL1_tail _ hL2_tail hflat_tail
            -- Assemble
            simp [hab_eq, this]

/-- Prefix-free codes are uniquely decodable.

If `S` is prefix-free (no codeword is a prefix of another) and does not contain the empty string,
then any string formed by concatenating codewords from `S` can be parsed into those codewords
in exactly one way.

The proof proceeds by structural induction on the list of codewords `L₁`.. -/
theorem prefix_free_is_uniquely_decodable
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
theorem prefix_free_is_uniquely_decodable_of_card_ge_two
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
  exact prefix_free_is_uniquely_decodable h0 hS

end Kraft
