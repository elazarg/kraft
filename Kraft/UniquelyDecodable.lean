
import Kraft.Basic

namespace Kraft

variable {α : Type _}

/-- Prefix-free codes are uniquely decodable (assuming the empty string is excluded).

If `S` is prefix-free (no codeword is a prefix of another) and `[] ∉ S`, then `S`
is uniquely decodable: any concatenation of codewords can be parsed in exactly one way.

The proof proceeds by strong induction on the total length of the concatenated string.
At each step, the first codeword is uniquely determined by the prefix-free property. -/
theorem prefix_free_is_uniquely_decodable (S : Finset (List α)) (h : PrefixFree (S : Set (List α))) (h_eps : [] ∉ S) :
    UniquelyDecodable (S : Set (List α)) := by
  -- We prove by strong induction on $|x|$ that every word $x \in \{0,1\}^*$ can be written in at most one way as $x = w_1 \dots w_r$ (for any $r$), where $w_1,\dots,w_r \in S$.
  have h_induction : ∀ x : List α, ∀ L1 L2 : List (List α), (∀ w ∈ L1, w ∈ S) → (∀ w ∈ L2, w ∈ S) → L1.flatten = L2.flatten → L1 = L2 := by
    intros x L1 L2 hL1 hL2 hflatten
    induction L1 generalizing L2 with
    | nil => induction L2
             · rfl
             · simp_all only [List.mem_cons,  List.not_mem_nil, IsEmpty.forall_iff, List.flatten_cons, List.append_left_eq_self, List.nil_eq, forall_const, forall_eq_or_imp, List.flatten_nil, List.append_eq_nil_iff, and_true]
    | cons w1 L1 ih =>
      rcases L2 with (_ | ⟨ x, L2 ⟩)
      · simp_all only [List.mem_cons, forall_eq_or_imp, List.flatten, List.append_eq, List.append_eq_nil_iff, false_and]
      · simp_all only [List.mem_cons, forall_eq_or_imp, List.flatten, List.append_eq]
        -- Since $w1$ and $x$ are both in $S$ and $S$ is prefix-free, we must have $w1 = x$.
        have hw1_eq_x : x = w1 := by
          have := h _ hL1.1 _ hL2.1
          have := h _ hL2.1 _ hL1.1
          rw [List.append_eq_append_iff] at hflatten
          -- `hflatten` is one of the two "overlap" cases
          cases hflatten with
          | inl hcase =>
              rcases hcase with ⟨t, hx, _⟩
              -- hx : x = w1 ++ t, so w1 <+: x
              have hw1x : w1 = x :=
                h w1 hL1.1 x hL2.1 ⟨t, hx.symm⟩
              simp [hw1x]  -- gives x = w1
          | inr hcase =>
              rcases hcase with ⟨t, hw, _⟩
              -- hw : w1 = x ++ t, so x <+: w1
              exact h x hL2.1 w1 hL1.1 ⟨t, hw.symm⟩
        simp_all only [true_and, List.append_cancel_left_eq, forall_const, List.cons.injEq]
        apply ih
        · intro w a
          simp_all only
        · simp_all only
  exact fun L1 L2 h1 h2 h3 => h_induction (L1.flatten) L1 L2 h1 h2 h3

/-- Prefix-free codes with at least two codewords are uniquely decodable.

This variant avoids explicitly assuming `[] ∉ S` by deriving it from the cardinality
constraint: if `|S| ≥ 2` and `S` is prefix-free, then `[]` cannot be in `S`
(since `[]` is a prefix of every other string). -/
theorem prefix_free_is_uniquely_decodable_of_card_ge_two (S : Finset (List α)) (h : PrefixFree (S: Set (List α))) (h_card : S.card ≥ 2) :
    UniquelyDecodable (S: Set (List α)) := by
  have h_eps_not_mem : [] ∉ S := by
    intro h0
    obtain ⟨ w, hw, hw' ⟩ := Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨ Finset.singleton_subset_iff.mpr h0, by
      intro a
      subst a
      simp_all only [Finset.card_singleton, ge_iff_le, Nat.reduceLeDiff]
    ⟩)
    specialize h _ h0 _ hw
    simp_all only [List.nil_prefix, Finset.mem_singleton]
  exact prefix_free_is_uniquely_decodable S h h_eps_not_mem

end Kraft
