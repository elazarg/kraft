import Mathlib.Data.List.Sort
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Finset

import Mathlib.Tactic.Linarith

import Batteries.Data.List.Basic

import Kraft.DyadicHelpers
import Kraft.PrefixFree
import Kraft.Converse_lemma

open BigOperators

-- General disjointness for codes starting with different bits
lemma disjoint_cons {S1 S2 : Code} :
    Disjoint (S1.image (List.cons true)) (S2.image (List.cons false)) := by
  rw [Finset.disjoint_left]
  intro w h1 h2
  rw [Finset.mem_image] at h1 h2
  rcases h1 with ⟨w1, _, rfl⟩
  rcases h2 with ⟨w2, _, heads_distinct⟩
  simp at heads_distinct -- true = false contradiction

-- Prefix-free is preserved under 'cons b'
lemma prefixFree_cons (b : Bool) {S : Code} (h : PrefixFree S) :
    PrefixFree (S.image (List.cons b)) := by
  intro x y hx hy hpre
  rw [Finset.mem_image] at hx hy
  rcases hx with ⟨wx, hwx_in, rfl⟩
  rcases hy with ⟨wy, hwy_in, rfl⟩
  simp at *; exact h hwx_in hwy_in hpre

lemma prefixFree_union_cons {S1 S2 : Code}
    (h1 : PrefixFree S1) (h2 : PrefixFree S2) :
    PrefixFree ((S1.image (List.cons true)) ∪ (S2.image (List.cons false))) := by
  intro x y hx hy hpre
  rw [Finset.mem_union] at hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · apply prefixFree_cons true h1 hx hy hpre
  · rw [Finset.mem_image] at hx hy; rcases hx with ⟨_, _, rfl⟩; rcases hy with ⟨_, _, rfl⟩; simp at hpre
  · rw [Finset.mem_image] at hx hy; rcases hx with ⟨_, _, rfl⟩; rcases hy with ⟨_, _, rfl⟩; simp at hpre
  · apply prefixFree_cons false h2 hx hy hpre


/-! ## 2. Construction -/

section Helpers

variable {h : ℕ} {lengths : List ℕ}

variable {n : ℕ} {reqs weights : List ℕ}

/--
  Helper 2: The divisibility argument.
  The weight at the split point (w_last) divides the accumulated sum (S_prev).
-/
lemma split_divisibility
    (h_w : weights = reqs.map (fun l => 2^(n - l)))
    (h_sorted : reqs.IsChain (· ≤ ·))
    (idx : ℕ) (h_idx : idx < reqs.length) :
    let w_last := 2^(n - reqs[idx])
    let S_prev := (weights.take idx).sum
    w_last ∣ S_prev := by
  intro w_last S_prev
  apply List.dvd_sum
  intros x hx
  rw [List.mem_take_iff_getElem] at hx
  rcases hx with ⟨i, hi_lt, rfl⟩

  -- 1. Establish index validity for 'reqs' manually
  have h_len : weights.length = reqs.length := by rw [h_w, List.length_map]
  have h_i_reqs : i < reqs.length := by
    rw [←h_len]
    exact Nat.lt_of_lt_of_le (lt_min_iff.mp hi_lt).left (by omega)

  -- 2. Simplify the element access
  -- 'simp' is smarter than 'rw' here; it handles the dependent index proof (h_i_reqs)
  simp only [h_w, List.getElem_map]

  -- 3. Proceed with divisibility logic
  rw [Nat.pow_dvd_pow_iff_le_right (by decide)]
  rw [List.isChain_iff_pairwise] at h_sorted
  · simp_all
    have h_le : reqs[i] ≤ reqs[idx] :=
      List.pairwise_iff_getElem.mp h_sorted i idx h_i_reqs h_idx (lt_min_iff.mp hi_lt).left
    apply Nat.le_add_of_sub_le
    apply Nat.sub_le_sub_left h_le

/--
If you take a prefix of `I.toList` and turn it into a finset, it’s a subset of `I`.
This is the basic "prefix picks elements from I" fact.
-/
lemma take_toFinset_subset {α : _} [DecidableEq α] (I : Finset α) (k : ℕ) :
    (I.toList.take k).toFinset ⊆ I := by
  intro x hx
  -- `x ∈ toFinset` gives `x ∈ list`
  have hx_list : x ∈ I.toList.take k := by
    simpa using (List.mem_toFinset.mp hx)
  -- prefix membership implies membership in the full list
  have hx_full : x ∈ I.toList := List.mem_of_mem_take hx_list
  -- and `toList` membership is exactly finset membership
  simpa using (Finset.mem_toList.mp hx_full)

/-- Divisibility helper for lists -/
lemma dvd_sum_of_dvd_forall {l : List ℕ} {k : ℕ} (h : ∀ x ∈ l, k ∣ x) : k ∣ l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp; apply Nat.dvd_add
    · exact h a List.mem_cons_self
    · exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- Uniqueness of a least index satisfying `P`. -/
lemma least_index_unique (P : ℕ → Prop) (k1 k2 : ℕ)
    (h1 : P k1) (h1min : ∀ j < k1, ¬ P j)
    (h2 : P k2) (h2min : ∀ j < k2, ¬ P j) :
    k1 = k2 := by
  by_contra hne
  wlog hk : k1 < k2
  · have hk' : k2 < k1 := lt_of_le_of_ne (le_of_not_gt hk) (Ne.symm hne)
    -- swap roles
    exact (this P k2 k1 h2 h2min h1 h1min (by simpa [eq_comm] using hne) hk')
  -- contradiction: k1 < k2 but k1 satisfies P, contradicting minimality of k2
  exact h2min k1 hk h1

-- Helper: Mass of a list of lengths at a specific height h.
def mass (h : ℕ) (lengths : List ℕ) : ℕ :=
  (lengths.map (fun l => 2^(h - l))).sum
/--
`Nat.find` version of "first prefix whose sum reaches capacity".

If there exists *some* prefix whose sum is ≥ cap, then there is a *least* such prefix,
and every shorter prefix is strictly below cap.
-/
lemma exists_min_prefix_sum_ge (cap : ℕ) (ws : List ℕ)
    (h_ex : ∃ k, cap ≤ (ws.take k).sum) :
    ∃ k, cap ≤ (ws.take k).sum ∧ ∀ j < k, (ws.take j).sum < cap := by
  let P : ℕ → Prop := fun k => cap ≤ (ws.take k).sum
  have hP : ∃ k, P k := h_ex
  let k : ℕ := Nat.find hP
  refine ⟨k, ?_, ?_⟩
  · exact Nat.find_spec hP
  · intro j hj
    -- `Nat.find_min'` says any smaller index fails P
    have hmin : ¬ P j := Nat.find_min hP hj
    -- goal is `¬ (sum ≥ cap)`; rewrite `≥` as `≤` and unfold P
    simpa [P, ge_iff_le] using hmin

/--
  Helper 4: Algebraic final step.
  If the prefix sum of weights is exactly 2^n, and total weights ≤ 2^(n+1),
  then Left Mass = 2^n and Right Mass ≤ 2^n.
-/
lemma mass_split_algebra (n k : ℕ) (reqs weights : List ℕ)
    (h_w : weights = reqs.map (fun l => 2^(n - l)))
    (h_left_sum : (weights.take k).sum = 2^n)
    (h_bound : weights.sum ≤ 2^(n+1)) :
    mass n (reqs.take k) = 2^n ∧ mass n (reqs.drop k) ≤ 2^n := by
  dsimp [mass]
  constructor
  · -- 1. Prove Left Mass = 2^n
    rw [List.map_take, ←h_w]
    exact h_left_sum
  · -- 2. Prove Right Mass ≤ 2^n
    rw [List.map_drop, ←h_w]
    have h_total := List.sum_take_add_sum_drop weights k
    omega


-- A. Mass Constraints
/--
  If 0 is in the list, it contributes 2^h to the mass.
  Since total mass ≤ 2^h, no other elements can exist.
-/
lemma mass_zero_implies_singleton
    (h_mass : mass h lengths ≤ 2^h)
    (h_zero : 0 ∈ lengths) :
    lengths = [0] := by
  dsimp [mass] at h_mass
  rw [List.mem_iff_append] at h_zero
  rcases h_zero with ⟨pre, post, rfl⟩
  rw [List.map_append, List.sum_append] at h_mass
  rw [List.map_cons, List.sum_cons] at h_mass
  simp only [Nat.sub_zero] at h_mass
  have h_rest_zero : (pre.map (fun l => 2 ^ (h - l))).sum + (post.map (fun l => 2 ^ (h - l))).sum = 0 := by
    omega
  have h_pre_nil : pre = [] := by
    match pre with
    | [] => rfl
    | x :: xs =>
      simp only [List.map_cons, List.sum_cons] at h_rest_zero
      have : 2 ^ (h - x) > 0 := Nat.pow_pos (by decide)
      omega
  have h_post_nil : post = [] := by
    match post with
    | [] => rfl
    | x :: xs =>
      simp only [List.map_cons, List.sum_cons] at h_rest_zero
      have : 2 ^ (h - x) > 0 := Nat.pow_pos (by decide)
      omega
  subst pre post
  rfl

end Helpers

-- Helper: Lengths of a code as a multiset
def lengthMultiset (S : Code) : Multiset ℕ := S.val.map List.length

-- Helper: Lengths of a disjoint union are the sum of length multisets
lemma lengthMultiset_union_of_disjoint {S1 S2 : Code} (h : Disjoint S1 S2) :
    lengthMultiset (S1 ∪ S2) = lengthMultiset S1 + lengthMultiset S2 := by
  dsimp [lengthMultiset]
  -- S1 ∪ S2 is Finset.disjUnion because they are disjoint
  rw [<-Finset.disjUnion_eq_union _ _ h]
  -- val of disjUnion is map sum
  simp only [Finset.disjUnion_val, Multiset.map_add]


/-!
# Theorem 3.2 (Converse of Kraft)

Goal (your `theorem_3_2`):
If `∑_{i∈I} 2^{-l(i)} ≤ 1`, build an injective `w : I → {0,1}*` such that
(1) image is prefix-free, and (2) `|w(i)| = l(i)`.

The construction is the standard "binary tree / half-splitting" recursion:
split the index set into two parts whose Kraft sums are ≤ 1/2, decrement all lengths,
recurse, then prefix `true` on the left and `false` on the right.
-/

/-! ## Small helper lemmas used by the induction step -/

section Thm32Helpers
variable {α : Type _} [DecidableEq α]
variable (I : Finset α) (l : α → ℕ)

-- If there is a zero-length requirement, the inequality forces `I` to be empty or singleton.
-- (Because one element with l=0 contributes exactly 1, and all other contributions are positive.)
lemma kraft_singleton_of_exists_len_zero
    (h_sum : (∑ i ∈ I, (2 ^ l i : ℚ)⁻¹) ≤ 1)
    (hz : ∃ i ∈ I, l i = 0) :
    I = ∅ ∨ ∃ i, I = {i} := by
  -- proof idea:
  -- pick i0 with l i0 = 0. Then the summand at i0 is 1.
  -- If there were any other j ∈ I, its summand is > 0, so total sum > 1. Contradiction.
  -- hence card I ≤ 1, so I is empty or singleton.
  contrapose! h_sum;
  obtain ⟨ i, hi, hi' ⟩ := hz;
  rw [Finset.sum_eq_add_sum_diff_singleton hi];
  apply lt_add_of_le_of_pos (by norm_num [hi'])
  apply Finset.sum_pos (by simp)
  apply Finset.nonempty_of_ne_empty
  simp_all
  intro a
  simp_all only [Finset.notMem_empty]


-- For the positive-length case, split I into S and its complement so that both sums ≤ 1/2.
-- If total ≤ 1/2, take S = I. Otherwise use corollary_3_1_half to carve S with sum = 1/2.
noncomputable def halfSplit
    (h_pos : ∀ i ∈ I, 0 < l i)
    (h_sum : (∑ i ∈ I, (2 ^ l i : ℚ)⁻¹) ≤ 1) :
    {S // S ⊆ I ∧
         (∑ i ∈ S, (2 ^ l i : ℚ)⁻¹) ≤ (1/2 : ℚ) ∧
         (∑ i ∈ I \ S, (2 ^ l i : ℚ)⁻¹) ≤ (1/2 : ℚ)} := by
  by_cases hIhalf : (∑ i ∈ I, (2 ^ l i : ℚ)⁻¹) ≤ (1/2 : ℚ)
  · -- Case 1: Total sum ≤ 1/2.
    refine ⟨I, ?_, ?_, ?_⟩
    · exact Finset.Subset.rfl
    · exact hIhalf
    · simp only [Finset.sdiff_self, Finset.sum_empty]
      norm_num

  · -- Case 2: Total sum > 1/2.
    have h_ge_half : (∑ i ∈ I, (2 ^ l i : ℚ)⁻¹) ≥ (1/2 : ℚ) := by linarith

    -- The existential witness from your corollary
    let exists_S := corollary_3_1_half I l h_pos h_ge_half

    -- Extract S using Classical Choice
    let S := Classical.choose exists_S
    have h_spec := Classical.choose_spec exists_S
    rcases h_spec with ⟨hSsub, hS_eq⟩

    refine ⟨S, hSsub, ?_, ?_⟩
    · -- S sum is exactly 1/2
      rw [hS_eq]
    · -- I \ S sum is ≤ 1/2
      -- We explicitly provide the function f := ... to resolve the ambiguity
      have h_decomp := Finset.sum_sdiff (f := fun i => (2 ^ l i : ℚ)⁻¹) hSsub

      -- Now h_decomp is: sum(I \ S) + sum(S) = sum(I)

      -- Substitute known value: sum(S) = 1/2
      rw [hS_eq] at h_decomp

      -- linarith combines:
      -- 1. h_decomp: sum(I \ S) + 1/2 = sum(I)
      -- 2. h_sum:    sum(I) ≤ 1
      -- Result:      sum(I \ S) ≤ 1/2
      linarith

-- Decrementing a positive nat that is ≤ h+1 yields something ≤ h.
lemma sub_one_le_of_le_succ {h n : ℕ} (hnpos : 0 < n) (hle : n ≤ h+1) :
    n - 1 ≤ h := by
  omega

-- Length equation: if 0 < n then (n-1)+1 = n
lemma sub_one_add_one_eq {n : ℕ} (hnpos : 0 < n) : (n - 1) + 1 = n := by
  -- `Nat.sub_add_cancel` wants `1 ≤ n`
  exact Nat.sub_add_cancel (Nat.succ_le_iff.mp hnpos)

end Thm32Helpers


/-! ## Main auxiliary theorem: induct on a height bound h -/

section Thm32Aux

variable {α : Type _} [DecidableEq α]

-- This is the real induction statement:
-- assume a *uniform* bound `l i ≤ h` over i∈I, plus Kraft sum ≤ 1,
-- then build the code.
theorem theorem_3_2_aux
    (h : ℕ) (I : Finset α) (l : α → ℕ)
    (h_bound : ∀ i ∈ I, l i ≤ h)
    (h_sum : (∑ i ∈ I, (2 ^ l i : ℚ)⁻¹) ≤ 1) :
    ∃ w : α → Word,
      Set.InjOn w I ∧
      PrefixFree (I.image w) ∧
      ∀ i ∈ I, (w i).length = l i := by
  induction h generalizing I l with
  | zero =>
      -- h = 0: all lengths on I are 0.
      -- Then each summand is 1, so sum = card I ≤ 1, hence card I ≤ 1.
      -- So I is empty or singleton. Construct w accordingly (always [] works).
      -- PrefixFree on empty/singleton is trivial, injective on singleton is trivial.
      exists (fun _ => ∅)
      simp_all
      constructor
      · simp [Set.InjOn]
        rw [Finset.card_le_one] at h_sum
        apply h_sum
      · simp [Finset.image]
        if I=∅ then
          simp_all [PrefixFree]
        else
          simp_all [PrefixFree]
  | succ h ih =>
      -- h = h+1 step.

      -- First: handle the "some length is 0" corner case.
      by_cases hz : (∃ i ∈ I, l i = 0)
      · -- Then I is empty or singleton (see helper), and we finish like base case.
        have : I = ∅ ∨ ∃ i, I = {i} :=
          kraft_singleton_of_exists_len_zero I l h_sum hz
        -- build w from cases
        specialize ih I l
        obtain ⟨w, h_1⟩ := hz
        obtain ⟨left, right⟩ := h_1
        cases this with
        | inl h_1 => simp_all
        | inr h_2 =>
          obtain ⟨w_1, h_1⟩ := h_2
          simp_all
      · -- Otherwise, all lengths are positive on I.
        have h_pos : ∀ i ∈ I, 0 < l i := by
          intro i hi
          have : l i ≠ 0 := by
            intro h0
            exact hz ⟨i, hi, h0⟩
          exact Nat.pos_of_ne_zero this

        -- Choose S ⊆ I s.t. sum over S ≤ 1/2 and sum over I\S ≤ 1/2.
        let split := halfSplit (I := I) (l := l) h_pos h_sum
        rcases split with ⟨S, hSsub, hS_le_half, hC_le_half⟩
        let C : Finset α := I \ S

        -- Define decremented lengths l' i = l i - 1
        let l' : α → ℕ := fun i => l i - 1

        -- Show the *scaled* Kraft sums for S and C with l' are ≤ 1 (since original ≤ 1/2).
        have hS_sum' : (∑ i ∈ S, (2 ^ l' i : ℚ)⁻¹) ≤ 1 := by
          -- use finset_sum_inv_pow_sub_one on S:
          --   sum 2^{-(l-1)} = 2 * sum 2^{-l}
          -- then `linarith` with hS_le_half.
          -- Need: ∀ i∈S, 0 < l i (follows from h_pos + hSsub).
          -- 1. Establish the scaling relation: sum(2^-(l-1)) = 2 * sum(2^-l)
            have h_scale : ∑ i ∈ S, (2 ^ l' i : ℚ)⁻¹ = 2 * ∑ i ∈ S, (2 ^ l i : ℚ)⁻¹ := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              dsimp [l']
              apply Dyadic.inv_pow_sub_one
              -- Discharge the positivity requirement (l i > 0)
              exact h_pos i (hSsub hi)

            -- 2. Substitute and use the bound hS_le_half (sum ≤ 1/2)
            rw [h_scale]
            -- 2 * (something ≤ 1/2) is ≤ 1
            linarith [hS_le_half]

        have hC_sum' : (∑ i ∈ C, (2 ^ l' i : ℚ)⁻¹) ≤ 1 := by
          -- same for C = I \ S, using hC_le_half
          -- 1. Establish the scaling relation for C
            have h_scale_C : ∑ i ∈ C, (2 ^ l' i : ℚ)⁻¹ = 2 * ∑ i ∈ C, (2 ^ l i : ℚ)⁻¹ := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              dsimp [l']
              apply Dyadic.inv_pow_sub_one
              -- Prove i ∈ I to use h_pos (since C = I \ S)
              exact h_pos i (Finset.mem_sdiff.mp hi).1

            -- 2. Substitute and use the bound hC_le_half
            rw [h_scale_C]
            linarith [hC_le_half]

        -- Show bound `l' i ≤ h` on S and C (since l i ≤ h+1 and l i > 0).
        have hS_bound' : ∀ i ∈ S, l' i ≤ h := by
          intro i hi
          have hiI : i ∈ I := hSsub hi
          have hle : l i ≤ h+1 := h_bound i hiI
          exact sub_one_le_of_le_succ (hnpos := h_pos i hiI) hle

        have hC_bound' : ∀ i ∈ C, l' i ≤ h := by
          intro i hi
          have hiI : i ∈ I := by
            -- mem of sdiff implies mem of I
            exact (Finset.mem_sdiff.mp hi).1
          have hle : l i ≤ h+1 := h_bound i hiI
          exact sub_one_le_of_le_succ (hnpos := h_pos i hiI) hle

        -- Apply IH on S and C.
        rcases ih S l' hS_bound' hS_sum' with ⟨w0, hw0_inj, hw0_pf, hw0_len⟩
        rcases ih (I := C) (l := l') hC_bound' hC_sum' with
          ⟨w1, hw1_inj, hw1_pf, hw1_len⟩

        -- Combine by prefixing a different bit on each side.
        let w : α → Word := fun i => if i ∈ S then true :: w0 i else false :: w1 i

        refine ⟨w, ?_, ?_, ?_⟩

        · -- Injective on I:
          -- If w i = w j, then either both i,j ∈ S (strip true:: and use hw0_inj),
          -- or both i,j ∈ C (strip false:: and use hw1_inj),
          -- mixed case impossible since true≠false.
          --
          -- This is a standard by_cases on membership in S.
          intro x hx y hy h_eq
          dsimp [w] at h_eq
          split_ifs at h_eq with hxS hyS
          · -- Case 1: Both x, y ∈ S
            -- The heads match (true), so w0 x = w0 y. Use hw0_inj.
            simp only [List.cons.injEq] at h_eq
            simp at h_eq
            exact hw0_inj hxS hyS h_eq
          · -- Case 2: x ∈ S, y ∉ S (so y ∈ C)
            -- Heads are true vs false. Contradiction.
            simp at h_eq
          · -- Case 3: x ∉ S, y ∈ S (so x ∈ C)
            -- Heads are false vs true. Contradiction.
            simp at h_eq
          · -- Case 4: Both x, y ∉ S (so x, y ∈ C)
            -- The heads match (false), so w1 x = w1 y. Use hw1_inj.
            simp only [List.cons.injEq] at h_eq
            simp at h_eq
            have hxC : x ∈ C := by simp_all [C]
            have hyC : y ∈ C := by simp_all [C]
            exact hw1_inj hxC hyC h_eq

        · -- PrefixFree on I.image w:
          -- First rewrite the image as a union of two "cons" images:
          --   I.image w = (S.image w0).image (List.cons true) ∪ (C.image w1).image (List.cons false)
          -- Then use `prefixFree_union_cons` with hw0_pf and hw1_pf.
          --
          -- You already proved `prefixFree_union_cons` in Converse_thm.lean.
          --
          -- The only bookkeeping work is the `Finset.ext` rewrite of `I.image w`.
          have h_img :
              I.image w
                = ((S.image w0).image (List.cons true)) ∪ ((C.image w1).image (List.cons false)) := by
            -- prove by ext; cases on i∈S; use simp [w, C, Finset.mem_sdiff]
            nth_rewrite 1 [← Finset.union_sdiff_of_subset hSsub]
            simp only [Finset.image_union, Finset.image_image]
            apply congr_arg₂ <;> apply Finset.image_congr <;> intro i hi
            · simp [w]
              assumption
            · simp [w] at hi ⊢
              simp [hi.2]
          -- now apply prefixfree
          -- (no disjointness lemma needed; `prefixFree_union_cons` handles cross cases by head-bit contradiction)
          simpa [h_img] using (prefixFree_union_cons (S1 := S.image w0) (S2 := C.image w1) hw0_pf hw1_pf)

        · -- Lengths: for i∈I, if i∈S then
          --   length (true::w0 i) = (l i - 1)+1 = l i
          -- similarly for i∈C.
          intro i hi
          by_cases hiS : i ∈ S
          · -- i in S
            have : (w0 i).length = l' i := hw0_len i hiS
            unfold w
            simp [hiS, l', this, sub_one_add_one_eq (h_pos i (hSsub hiS))]
          · -- i in C = I \ S
            have hiC : i ∈ C := by
              -- from hi∈I and hiS false
              exact Finset.mem_sdiff.mpr ⟨hi, hiS⟩
            have : (w1 i).length = l' i := hw1_len i hiC
            unfold w
            simp [hiS, l', this, sub_one_add_one_eq (h_pos i hi)]

end Thm32Aux


/-! ## Final wrapper: choose h = max length on I and invoke the aux theorem -/

theorem theorem_3_2 {α : _} (I : Finset α) (l : α → ℕ)
    (h_sum : (∑ i ∈ I, (2 ^ l i : ℚ)⁻¹) ≤ 1) :
    ∃ w : α → Word,
      Set.InjOn w I ∧
      PrefixFree (I.image w) ∧
      ∀ i ∈ I, (w i).length = l i := by
  let h : ℕ := I.sup l
  have h_bound : ∀ i ∈ I, l i ≤ h := by
    intros a ha
    exact Finset.le_sup ha
  classical
  exact theorem_3_2_aux (h := h) (I := I) (l := l) h_bound h_sum
