
import Kraft.Basic

namespace Kraft

/-
If a finite set $S$ of words is prefix-free and $\epsilon \notin S$ then it is uniquely decodable.
-/
theorem prefix_free_is_uniquely_decodable (S : Finset (List Bool)) (h : PrefixFree (S : Set (List Bool))) (h_eps : [] ∉ S) :
    UniquelyDecodable (S : Set (List Bool)) := by
  -- We prove by strong induction on $|x|$ that every word $x \in \{0,1\}^*$ can be written in at most one way as $x = w_1 \dots w_r$ (for any $r$), where $w_1,\dots,w_r \in S$.
  have h_induction : ∀ x : List Bool, ∀ L1 L2 : List (List Bool), (∀ w ∈ L1, w ∈ S) → (∀ w ∈ L2, w ∈ S) → L1.flatten = L2.flatten → L1 = L2 := by
    intros x L1 L2 hL1 hL2 hflatten
    induction L1 generalizing L2 with
    | nil => induction L2 <;> simp_all
    | cons w1 L1 ih =>
      rcases L2 with ( _ | ⟨ x, L2 ⟩ ) <;> simp_all +decide [ List.flatten ]
      -- Since $w1$ and $x$ are both in $S$ and $S$ is prefix-free, we must have $w1 = x$.
      have hw1_eq_x : x = w1 := by
        have := h _ hL1.1 _ hL2.1
        have := h _ hL2.1 _ hL1.1
        rw [ List.append_eq_append_iff ] at hflatten
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
      simp_all only [true_and, List.append_cancel_left_eq]
      apply ih
      · intro w a
        simp_all only
      · simp_all only
  exact fun L1 L2 h1 h2 h3 => h_induction ( L1.flatten ) L1 L2 h1 h2 h3

/-
If a finite set $S$ of words is prefix-free and $|S| \geq 2$ then it is uniquely decodable.
-/
theorem prefix_free_is_uniquely_decodable_of_card_ge_two (S : Finset (List Bool)) (h : PrefixFree (S: Set (List Bool))) (h_card : S.card ≥ 2) :
    UniquelyDecodable (S: Set (List Bool)) := by
  have h_eps_not_mem : []∉ S := by
    intro h0
    obtain ⟨ w, hw, hw' ⟩ := Finset.exists_of_ssubset ( Finset.ssubset_iff_subset_ne.mpr ⟨ Finset.singleton_subset_iff.mpr h0, by intro a; subst a; simp_all⟩ )
    specialize h _ h0 _ hw
    simp_all
  exact prefix_free_is_uniquely_decodable S h h_eps_not_mem

end Kraft
