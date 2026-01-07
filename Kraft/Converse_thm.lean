import Mathlib.Data.List.Sort
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.GCD.Basic

import Batteries.Data.List.Basic

import Kraft.PrefixFree

open BigOperators

/--
Theorem 3.2: Let I be a finite set and let l : I → ℕ satisfy ∑ 2^{-l(i)} ≤ 1.
There exists an injective mapping w : I → {0,1}* whose image is prefix-free,
and furthermore |w(i)| = l(i).
-/
theorem theorem_3_2 {α : _} (I : Finset α) (l : α → ℕ)
    (h_sum : ∑ i ∈ I, (2 ^ l i : ℚ)⁻¹ ≤ 1) :
    ∃ w : α → Word,
      Set.InjOn w I ∧
      PrefixFree (I.image w) ∧
      ∀ i ∈ I, (w i).length = l i :=
  sorry


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
This is the basic “prefix picks elements from I” fact.
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
