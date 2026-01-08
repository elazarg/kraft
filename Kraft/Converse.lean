import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset

import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

import Kraft.Basic

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000

namespace Kraft

open scoped BigOperators Real Nat

variable {I : Type _} [Fintype I] [DecidableEq I]

/-- **Kraft's Inequality (Tight Converse)**:
    If ∑ 2^(-l) ≤ 1, there exists a prefix-free code with these lengths. -/

/-
If a multiset of natural numbers is a sub-multiset of the image of a function on a finite type, then there is a subset of the domain whose image is that multiset.
-/
lemma exists_subset_of_multiset_le_map (f : I → ℕ) (m : Multiset ℕ)
    (h : m ≤ Multiset.map f Finset.univ.val) :
    ∃ S : Finset I, Multiset.map f S.val = m := by
  by_contra! h
  -- Since the multiset of values in $m$ is a sub-multiset of the image of $f$ on the universal set, we can construct the desired Finset $S$ by taking the union of the subsets of the domain corresponding to each value in $m$.
  have h_union : ∃ S : Finset I, Multiset.map f S.val = m := by
    have h_count : ∀ v ∈ m.toFinset, Multiset.count v m ≤ Finset.card (Finset.filter (fun i => f i = v) Finset.univ) := by
      intro v hv
      have h_card : Multiset.count v m ≤ Multiset.count v (Multiset.map f Finset.univ.val) := by
        exact Multiset.count_le_of_le _ ‹_›
      rw [ Multiset.count_map ] at h_card
      simpa [ eq_comm ] using h_card
    have h_union : ∃ S : Finset I, ∀ v ∈ m.toFinset, Finset.card (Finset.filter (fun i => f i = v) S) = Multiset.count v m := by
      have h_union : ∀ v ∈ m.toFinset, ∃ S_v : Finset I, S_v ⊆ Finset.filter (fun i => f i = v) Finset.univ ∧ Finset.card S_v = Multiset.count v m := by
        exact fun v hv => Finset.exists_subset_card_eq ( h_count v hv )
      choose! S hS₁ hS₂ using h_union
      use Finset.biUnion m.toFinset S
      intro v hv
      rw [ ← hS₂ v hv ]
      rw [ Finset.card_eq_sum_ones ]
      rw [ Finset.card_eq_sum_ones ]
      rw [ Finset.sum_subset ]
      ·
        intro x hx
        -- 1. Unpack that x is in the biUnion and satisfies the filter (f x = v)
        simp only [Finset.mem_filter, Finset.mem_biUnion] at hx
        obtain ⟨⟨u, hu_m, hx_Su⟩, hfx⟩ := hx

        -- 2. Use the property that S u contains only elements mapping to u
        have hfu : f x = u := by
          -- hS₁ : S u ⊆ {i | f i = u}
          have := hS₁ u hu_m hx_Su
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
          exact this

        -- 3. Conclude u = v, therefore x ∈ S v
        simp_all
      · simp [ Finset.mem_biUnion ]
        exact fun x hx => ⟨ v, Multiset.mem_toFinset.mp hv, hx, Finset.mem_filter.mp ( hS₁ v hv hx ) |>.2 ⟩
    obtain ⟨ S, hS ⟩ := h_union
    use S.filter (fun i => f i ∈ m)
    ext v
    by_cases hv : v ∈ m <;> simp_all [ Multiset.count_map ]
    · convert hS v hv using 1
      exact congr_arg Finset.card (Finset.filter_congr fun x hx => by
        apply Iff.intro
        · intro a
          simp_all only
        · intro a
          subst a
          simp_all only [and_self]
      )
    · intro a a_1 a_2
      subst a_2
      exact hv
  exact h _ h_union.choose_spec

lemma pairwise_monotone
    {l : List ℕ} (h_sorted : l.Pairwise (fun a b => a ≤ b))
    {i j : ℕ} (hij : i < j) (hj : j < l.length) :
    l[i]! ≤ l[j]! := by
  have hget : ∀ (p q : Fin l.length), p < q → l.get p ≤ l.get q :=
    List.pairwise_iff_get.mp h_sorted
  have hi : i < l.length := lt_trans hij hj
  have := hget ⟨i, hi⟩ ⟨j, hj⟩ (by simpa using hij)
  simp_all

/-
If a list of natural numbers is sorted non-decreasingly and the sum of $2^{-x}$ is at least 1, then there is a prefix whose sum is exactly 1.
-/
lemma exists_prefix_sum_eq_one_of_sorted {l : List ℕ} (h_sorted : l.Pairwise (· ≤ ·))
    (h_sum : (l.map (fun x => (1 / 2 : ℝ) ^ x)).sum ≥ 1) :
    ∃ l', l' <+: l ∧ (l'.map (fun x => (1 / 2 : ℝ) ^ x)).sum = 1 := by
  -- Let $k$ be the smallest index such that $s_k \geq 1$.
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k ≤ l.length ∧ (∑ i ∈ Finset.range k, (1 / 2 : ℝ) ^ l[i]!) ≥ 1 ∧ ∀ j < k, (∑ i ∈ Finset.range j, (1 / 2 : ℝ) ^ l[i]!) < 1 := by
    have h_exists_k : ∃ k : ℕ, k ≤ l.length ∧ (∑ i ∈ Finset.range k, (1 / 2 : ℝ) ^ l[i]!) ≥ 1 := by
      use l.length
      convert h_sum.le using 1
      norm_num [ Finset.sum_range ]
    exact ⟨ Nat.find h_exists_k, Nat.find_spec h_exists_k |>.1, Nat.find_spec h_exists_k |>.2, fun j hj => not_le.1 fun h => Nat.find_min h_exists_k hj ⟨ Nat.le_trans ( Nat.le_of_lt hj ) ( Nat.find_spec h_exists_k |>.1 ), h ⟩ ⟩
  -- Let $M$ be the integer such that $s_{k-1} = M / 2^{l_k}$.
  obtain ⟨M, hM⟩ : ∃ M : ℕ, (∑ i ∈ Finset.range (k - 1), (1 / 2 : ℝ) ^ l[i]!) = M / 2 ^ l[k - 1]! := by
    -- Since $l$ is sorted non-decreasingly, we have $l[i] \leq l[k-1]$ for all $i < k-1$.
    have h_le : ∀ i < k - 1, l[i]! ≤ l[k - 1]! := by
      intro i hi
      have hkpos' : k.sub 0 ≠ 0 := by
        -- i < k-1 forces k ≠ 0
        intro hk0
        have : k - 1 = 0 := by simp_all
        omega
      have hk1 : k - 1 < l.length := by
        obtain ⟨hklen, _⟩ := hk
        exact lt_of_lt_of_le (Nat.pred_lt hkpos') hklen
      have := List.pairwise_iff_get.mp h_sorted
      exact pairwise_monotone (l := l) h_sorted hi hk1
    -- Since $l[i] \leq l[k-1]$ for all $i < k-1$, we can write each term $(1 / 2)^{l[i]!}$ as $(1 / 2)^{l[k-1]!} \cdot 2^{l[k-1]! - l[i]!}$.
    have h_term : ∀ i < k - 1, (1 / 2 : ℝ) ^ l[i]! = (1 / 2 : ℝ) ^ l[k - 1]! * 2 ^ (l[k - 1]! - l[i]!) := by
      intro i hi
      rw [ show ( 1 / 2 : ℝ ) = ( 2⁻¹ : ℝ ) by norm_num, inv_pow ]
      rw [ ← Nat.add_sub_of_le ( h_le i hi ) ]
      ring_nf
      norm_num [ mul_assoc, ← mul_pow ]
    rw [ Finset.sum_congr rfl fun i hi => h_term i ( Finset.mem_range.mp hi ) ]
    norm_num [ ← Finset.mul_sum _ _ _, div_eq_mul_inv ]
    exact ⟨ ∑ i ∈ Finset.range ( k - 1 ), 2 ^ ( l[k - 1]?.getD 0 - l[i]?.getD 0 ), by simp [ div_eq_mul_inv, mul_comm ] ⟩
  -- Since $s_{k-1} < 1$, we have $M < 2^{l_k}$, so $M \leq 2^{l_k} - 1$.
  have hM_le : M ≤ 2 ^ l[k - 1]! - 1 := by
    have := hk.2.2 ( k - 1 )
    rcases k with ( _ | k ) <;> norm_num at *
    exact Nat.le_sub_one_of_lt ( by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; rw [ hM, div_lt_one ( by positivity ) ] at this; linarith )
  -- Now consider $s_k = s_{k-1} + (1/2)^{l_k} = (M + 1) / 2^{l_k}$.
  have hsk : (∑ i ∈ Finset.range k, (1 / 2 : ℝ) ^ l[i]!) = (M + 1) / 2 ^ l[k - 1]! := by
    rcases k <;> simp_all [Finset.sum_range_succ]
    · linarith
    · ring
  -- Since $s_k \geq 1$, we have $M + 1 \geq 2^{l_k}$.
  have hM_ge : M + 1 ≥ 2 ^ l[k - 1]! := by
    exact_mod_cast ( by rw [ hsk ] at hk; rw [ ge_iff_le ] at hk; rw [ le_div_iff₀ ( by positivity ) ] at hk; linarith : ( 2 : ℝ ) ^ l[k - 1]! ≤ M + 1 )
  -- Combining $M \leq 2^{l_k} - 1$ and $M + 1 \geq 2^{l_k}$, we get $M = 2^{l_k} - 1$.
  have hM_eq : M = 2 ^ l[k - 1]! - 1 := by
    exact eq_tsub_of_add_eq ( by linarith [ Nat.sub_add_cancel ( Nat.one_le_pow ( l[k - 1]! ) 2 zero_lt_two ) ] )
  -- Thus $s_k = (2^{l_k} - 1 + 1) / 2^{l_k} = 1$.
  have hsk_eq_one : (∑ i ∈ Finset.range k, (1 / 2 : ℝ) ^ l[i]!) = 1 := by
    rw [ hsk, hM_eq, Nat.cast_sub <| Nat.one_le_pow _ _ zero_lt_two ]
    norm_num
  refine' ⟨ l.take k, _, _ ⟩
  · exact List.take_prefix _ _
  · convert hsk_eq_one using 1
    have h_sum_eq : ∀ (l : List ℕ) (k : ℕ), k ≤ l.length → (∑ i ∈ Finset.range k, (1 / 2 : ℝ) ^ l[i]!) = (List.map (fun x => (1 / 2 : ℝ) ^ x) (List.take k l)).sum := by
      intros l k hk
      induction k with
      | zero => simp
      | succ k ih =>
        -- 1. Split the sum on the left (0 to k -> 0 to k-1 + k)
        rw [Finset.sum_range_succ]
        -- 2. Split the list on the right (take (k+1) -> take k ++ [l[k]])
        have h_take : l.take (k + 1) = l.take k ++ [l.get ⟨k, Nat.lt_of_succ_le hk⟩] := by
          simp_all
        rw [h_take, List.map_append, List.sum_append]
        -- 3. Use IH for the prefix
        rw [ih (Nat.le_of_succ_le hk)]
        -- 4. Prove the last terms are equal
        simp_all [lt_of_lt_of_le (Nat.lt_succ_self k) hk]
    rw [ h_sum_eq l k hk.1 ]

/-
Let $I$ be a finite set and let $\ell\colon I \to \mathbb{N}$ satisfy $\sum_{i \in I} 2^{-\ell(i)} \geq 1$. There exists a subset $S \subseteq I$ such that $\sum_{i \in S} 2^{-\ell(i)} = 1$.
-/
lemma exists_subset_sum_eq_one (l : I → ℕ)
    (h_sum : 1 ≤ ∑ i, (1 / 2 : ℝ) ^ l i) :
    ∃ S : Finset I, ∑ i ∈ S, (1 / 2 : ℝ) ^ l i = 1 := by
  -- Let $n = |I|$ and let $\ell'_1,\dots,\ell'_n$ consist of $(\ell(i))_{i \in I}$ arranged in nonincreasing order.
  set n := Fintype.card I
  obtain ⟨ℓ', hℓ'⟩ : ∃ ℓ' : Fin n → ℕ, Multiset.ofList (List.ofFn ℓ') = Multiset.map l Finset.univ.val := by
    -- Let $ℓ'$ be the list of values of $l$ on the elements of $I$.
    obtain ⟨ℓ', hℓ'⟩ : ∃ ℓ' : List ℕ, List.length ℓ' = n ∧ Multiset.ofList ℓ' = Multiset.map l Finset.univ.val := by
      use Finset.univ.val.map l |> Multiset.toList
      simp_all [n]
    use fun i => ℓ'.get (i.cast hℓ'.1.symm) -- Cast the Fin n to a valid index for ℓ'
    convert hℓ'.2 using 2
    have h_len : (List.ofFn fun i : Fin n => ℓ'.get (i.cast hℓ'.1.symm)).length = ℓ'.length := by
      simp only [List.length_ofFn, hℓ'.1]
    refine' List.ext_get h_len _
    simp_all
  -- Apply `exists_prefix_sum_eq_one_of_sorted` to the sorted list.
  obtain ⟨l'', hl''⟩ : ∃ l'' : List ℕ, l''.Perm (List.ofFn ℓ') ∧ List.Pairwise (· ≤ ·) l'' ∧ (l''.map (fun x => (1 / 2 : ℝ) ^ x)).sum ≥ 1 := by
    refine' ⟨ List.ofFn ℓ' |> List.insertionSort ( · ≤ · ), _, _, _ ⟩
    · exact List.perm_insertionSort (fun x1 x2 ↦ x1 ≤ x2) (List.ofFn ℓ')
    · exact List.pairwise_insertionSort _ _
    · have h_sum_eq : (List.map (fun x => (1 / 2 : ℝ) ^ x) (List.ofFn ℓ')).sum = ∑ i, (1 / 2 : ℝ) ^ (l i) := by
        have h_sum_eq : (List.map (fun x => (1 / 2 : ℝ) ^ x) (List.ofFn ℓ')).sum = Multiset.sum (Multiset.map (fun x => (1 / 2 : ℝ) ^ x) (Multiset.ofList (List.ofFn ℓ'))) := by
          rfl
        simp_all
      have h_sum_eq : (List.map (fun x => (1 / 2 : ℝ) ^ x) (List.insertionSort (· ≤ ·) (List.ofFn ℓ'))).sum = (List.map (fun x => (1 / 2 : ℝ) ^ x) (List.ofFn ℓ')).sum := by
        have h_sum_eq : List.Perm (List.insertionSort (· ≤ ·) (List.ofFn ℓ')) (List.ofFn ℓ') := by
          exact List.perm_insertionSort (fun x1 x2 ↦ x1 ≤ x2) (List.ofFn ℓ')
        exact List.Perm.sum_eq ( h_sum_eq.map _ )
      linarith
  -- Apply `exists_prefix_sum_eq_one_of_sorted` to the sorted list `l''`.
  obtain ⟨l''', hl'''⟩ : ∃ l''' : List ℕ, l''' <+: l'' ∧ (l'''.map (fun x => (1 / 2 : ℝ) ^ x)).sum = 1 := by
    apply exists_prefix_sum_eq_one_of_sorted hl''.2.1 hl''.2.2
  -- The elements of this prefix correspond to a subset $S$ of $I$.
  obtain ⟨S, hS⟩ : ∃ S : Finset I, Multiset.map l S.val = Multiset.ofList l''' := by
    apply_rules [ exists_subset_of_multiset_le_map ]
    have h_subset : Multiset.ofList l''' ≤ Multiset.ofList l'' := by
      exact hl'''.1.sublist.subperm
    exact h_subset.trans ( by rw [ ← hℓ' ] ; exact Multiset.le_iff_exists_add.mpr ⟨ ∅, by simp [ hl''.1.symm ] ⟩ )
  replace hS := congr_arg ( fun m => Multiset.sum ( m.map fun x => ( 1 / 2 : ℝ ) ^ x ) ) hS
  simp_all
  apply Exists.intro
  exact hS

@[simp]
def range (w: I → List Bool) := ((Finset.univ.image w): Set (List Bool))

/-
Let $I$ be a finite set and let $\ell\colon I \to \mathbb{N}$ satisfy $\sum_{i\in I} 2^{-\ell(i)} \leq 1$.
There exists an injective mapping $w \colon I \to \{0,1\}^*$ whose image is prefix-free, and furthermore $|w(i)| = \ell(i)$.
-/
theorem kraft_inequality_tight (l : I → ℕ)
    (h : ∑ i, (1 / 2 : ℝ) ^ l i ≤ 1) :
    ∃ w : I → List Bool, (
      Function.Injective w
      ∧ PrefixFree (range w)
      ∧ ∀ i, (w i).length = l i)
 := by
  by_contra h_contra
  -- Let $m = \max_{i \in I} \ell(i)$.
  let m : ℕ := Finset.univ.sup l
  -- We prove this by strong induction on $m$.
  have h_ind : ∀ m : ℕ, ∀ (I : Type _) [Fintype I] [DecidableEq I]
       (l : I → ℕ), (∀ i, l i ≤ m)
        → (∑ i, (1 / 2 : ℝ) ^ l i) ≤ 1
        → ∃ (w : I → (List Bool)),
          (Function.Injective w)
          ∧ PrefixFree (range w)
          ∧ (∀ i, ((w i).length = (l i))) := by
    intro m
    induction m with
    | zero =>
      intro I _ _ l hl hsum
      by_cases hI : Nonempty I
      · simp_all
        interval_cases z : Fintype.card I <;> simp_all [ Fintype.card_eq_one_iff ]
        obtain ⟨w, h_1⟩ := z
        simp_all only [forall_const]
        apply Exists.intro
        · constructor
          · intro a₁ a₂ a
            simp_all only
          · constructor
            · intro x a y a_1 a_2
              simp_all
            · rfl
      · -- hI : ¬ Nonempty I
        haveI : IsEmpty I := ⟨fun i => hI ⟨i⟩⟩
        refine ⟨(fun i => (isEmptyElim i)), ?_, ?_, ?_⟩
        · intro a
          exact (isEmptyElim a)
        · intro x hx
          exact (False.elim (by
            -- since there are no elements, Finset.univ is empty; membership impossible
            simp at hx))
        · intro i
          exact (isEmptyElim i)
    | succ m ih =>
      intro I _ _ l hl hsum
      by_cases h_exists_zero : ∃ i, l i = 0
      · obtain ⟨i₀, hi₀⟩ : ∃ i₀, l i₀ = 0 := h_exists_zero
        have h_card : Fintype.card I = 1 := by
          have h_card : ∑ i, (1 / 2 : ℝ) ^ l i ≥ 1 := by
            exact le_trans ( by norm_num [ hi₀ ] ) ( Finset.single_le_sum ( fun i _ => by positivity ) ( Finset.mem_univ i₀ ) )
          have h_card : ∑ i ∈ Finset.univ.erase i₀, (1 / 2 : ℝ) ^ l i = 0 := by
            norm_num +zetaDelta at *
            rw [ sub_eq_zero, hi₀, pow_zero ]
            linarith
          simp_all
          rw [ Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_univ i₀ ) ] at h_card
          exact le_antisymm ( le_of_not_gt fun h => absurd h_card <| ne_of_gt <| sub_pos_of_lt <| lt_add_of_le_of_pos ( by norm_num [ hi₀ ] ) <| Finset.sum_pos ( fun x hx => inv_pos.mpr <| pow_pos zero_lt_two _ ) <| Finset.card_pos.mp <| by simp [ Finset.card_sdiff, * ] ) ( Fintype.card_pos_iff.mpr ⟨ i₀ ⟩ )
        rw [ Fintype.card_eq_one_iff ] at h_card
        obtain ⟨ x, hx ⟩ := h_card
        use fun _ => List.replicate (l x) Bool.true
        simp [ Function.Injective, hx ]
        simp [PrefixFree]
      · -- If $\sum_{i \in I} 2^{-\ell(i)} \leq \frac{1}{2}$, then we can take $S = I$.
        by_cases h_sum_half : (∑ i, (1 / 2 : ℝ) ^ (l i)) ≤ 1 / 2
        · -- Define $\ell'\colon I \to \mathbb{N}$ by $\ell'(i) = \ell(i) - 1$.
          set l' : I → ℕ := fun i => l i - 1 with hl'_def
          -- By the induction hypothesis, there exists an injective mapping $w' \colon I \to \{0,1\}^*$ whose image is prefix-free, and furthermore $|w'(i)| = \ell'(i)$.
          obtain ⟨w', hw'_inj, hw'_prefix, hw'_length⟩ : ∃ (w' : I → (List Bool)), (Function.Injective w') ∧ (PrefixFree (range w')) ∧ (∀ i, ((w' i).length = (l' i))) := by
            apply ih I l'
            · exact fun i => Nat.sub_le_of_le_add <| by linarith [ hl i ]
            · convert mul_le_mul_of_nonneg_left h_sum_half zero_le_two using 1 <;> norm_num [ pow_succ', Finset.mul_sum _ _ _ ]
              exact Finset.sum_congr rfl fun i _ => by rw [ show l i = l' i + 1 by rw [ Nat.sub_add_cancel ( Nat.pos_of_ne_zero fun hi => h_exists_zero ⟨ i, hi ⟩ ) ] ]; ring
          use fun i => false :: w' i
          simp_all +decide [ Function.Injective, PrefixFree ]
          exact ⟨ hw'_inj, hw'_prefix, fun i => Nat.succ_pred_eq_of_pos ( Nat.pos_of_ne_zero ( h_exists_zero i ) ) ⟩
        · -- Otherwise, we can find a subset $S \subseteq I$ such that $\sum_{i \in S} 2^{-\ell(i)} = \frac{1}{2}$.
          obtain ⟨S, hS⟩ : ∃ S : Finset I, (∑ i ∈ S, (1 / 2 : ℝ) ^ (l i)) = 1 / 2 := by
            have h_subset : ∃ S : Finset I, (∑ i ∈ S, (1 / 2 : ℝ) ^ (l i - 1)) = 1 := by
              apply exists_subset_sum_eq_one
              have h_subset : ∑ i, (1 / 2 : ℝ) ^ (l i - 1) = 2 * ∑ i, (1 / 2 : ℝ) ^ (l i) := by
                rw [ Finset.mul_sum _ _ _ ]
                exact Finset.sum_congr rfl fun i _ => by rw [ show ( 1 / 2 : ℝ ) ^ ( l i - 1 ) = 2 * ( 1 / 2 : ℝ ) ^ l i by rw [ show ( 1 / 2 : ℝ ) ^ l i = ( 1 / 2 : ℝ ) ^ ( l i - 1 ) * ( 1 / 2 : ℝ ) by rw [ ← pow_succ, Nat.sub_add_cancel ( Nat.pos_of_ne_zero fun hi => h_exists_zero ⟨ i, hi ⟩ ) ] ] ; ring ]
              linarith
            obtain ⟨ S, hS ⟩ := h_subset
            use S
            convert congr_arg ( · * ( 1 / 2 : ℝ ) ) hS using 1 <;> norm_num [ Finset.sum_mul _ _ _ ]
            exact Finset.sum_congr rfl fun i hi => by rw [ ← pow_succ, Nat.sub_add_cancel ( Nat.pos_of_ne_zero fun hi' => h_exists_zero ⟨ i, hi' ⟩ ) ]
          -- Define $\ell'\colon I \to \mathbb{N}$ by $\ell'(i) = \ell(i) - 1$.
          set l' : I → ℕ := fun i => l i - 1 with hl'_def
          -- By the induction hypothesis, there exist injective maps $w_0\colon S \to \{0,1\}^*$ and $w_1\colon S^c \to \{0,1\}^*$ such that $w_0(S)$ and $w_1(S^c)$ are prefix-free; $|w_0(i)| = \ell'(i)$ for all $i \in S$; and $|w_1(i)| = \ell'(i)$ for all $i \in S^c$.
          obtain ⟨w0, hw0_inj, hw0_prefix, hw0_len⟩ : ∃ w0 : S → (List Bool), (Function.Injective w0) ∧ (PrefixFree (range w0)) ∧ (∀ i, ((w0 i).length = (l' i))) := by
            apply ih
            · exact fun i => Nat.sub_le_of_le_add <| by linarith [ hl i ]
            · rw [ ← Finset.sum_coe_sort ] at *
              convert mul_le_mul_of_nonneg_left hS.le zero_le_two using 1 <;> norm_num [ pow_succ', ← mul_assoc, Finset.mul_sum _ _ _ ]
              exact Finset.sum_congr rfl fun x hx => by rw [ show l ( x : I ) = l' ( x : I ) + 1 from by rw [ Nat.sub_add_cancel ( Nat.pos_of_ne_zero fun hi => h_exists_zero ⟨ x, hi ⟩ ) ] ] ; ring

          obtain ⟨w1, hw1_inj, hw1_prefix, hw1_len⟩ : ∃ w1 : { x // x ∉ S } → (List Bool), (Function.Injective w1) ∧ (PrefixFree (range w1)) ∧ (∀ i, ((w1 i).length = (l' i))) := by
            apply ih { x // x ∉ S } (fun i => l' i)
            · exact fun i => Nat.sub_le_of_le_add <| by linarith [ hl i ]
            · have h_sum_complement : ∑ i ∈ Finset.univ \ S, (1 / 2 : ℝ) ^ (l i) ≤ 1 / 2 := by
                norm_num at *; linarith
              have h_sum_complement : ∑ i ∈ Finset.univ \ S, (1 / 2 : ℝ) ^ (l i - 1) ≤ 1 := by
                have h_sum_complement : ∑ i ∈ Finset.univ \ S, (1 / 2 : ℝ) ^ (l i - 1) = 2 * ∑ i ∈ Finset.univ \ S, (1 / 2 : ℝ) ^ (l i) := by
                  rw [ Finset.mul_sum _ _ _ ] ; refine' Finset.sum_congr rfl fun i hi => _ ; rcases k : l i with ( _ | k ) <;> simp_all [ pow_succ' ]
                linarith
              convert h_sum_complement using 1
              refine' Finset.sum_bij ( fun x _ => x ) _ _ _ _ <;> simp
              exact fun _ _ => rfl
          -- Define $w\colon I \to \{0, 1\}^*$ by
          use fun i => if hi : i ∈ S then false :: w0 ⟨i, hi⟩ else true :: w1 ⟨i, hi⟩
          refine' ⟨ _, _, _ ⟩
          · intro i j hij
            by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp +decide [ hi, hj ] at hij ⊢
            · exact Subtype.ext_iff.mp ( hw0_inj hij )
            · exact congr_arg Subtype.val ( hw1_inj hij )
          ·
            -- abbreviate the combined map (same as your `use fun i => if ...`)
            let w : I → List Bool :=
              fun i => if hi : i ∈ S then (false :: w0 ⟨i, hi⟩) else (true :: w1 ⟨i, hi⟩)

            -- goal: PrefixFree ↑(Finset.image w Finset.univ)
            -- unfold PrefixFree
            intro x hx y hy hxy

            -- move membership from Set-coe to Finset membership, so we can `mem_image` cleanly
            have hx' : x ∈ ((Finset.univ : Finset I).image w : Finset (List Bool)) := by
              simpa using hx
            rcases Finset.mem_image.mp hx' with ⟨i, hiU, rfl⟩

            have hy' : y ∈ ((Finset.univ : Finset I).image w : Finset (List Bool)) := by
              simpa using hy
            rcases Finset.mem_image.mp hy' with ⟨j, hjU, rfl⟩

            by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
            · -- i∈S, j∈S
              -- reduce the prefix fact to the tails
              have hxy' : (false :: w0 ⟨i, hi⟩) <+: (false :: w0 ⟨j, hj⟩) := by
                simpa [w, hi, hj] using hxy
              rcases hxy' with ⟨t, ht⟩
              -- ht : 0 :: w0 j = (0 :: w0 i) ++ t
              have ht_tail : w0 ⟨i, hi⟩ <+: w0 ⟨j, hj⟩ := by
                refine ⟨t, ?_⟩
                -- strip the leading cons from ht
                have : false :: (w0 ⟨i, hi⟩ ++ t) = (false :: w0 ⟨j, hj⟩) := by
                  simpa [List.cons_append] using ht
                exact (List.cons.inj this).2

              -- membership facts for hw0_prefix
              have mem_i : w0 ⟨i, hi⟩ ∈ (↑((Finset.univ : Finset (↥S)).image w0) : Set (List Bool)) := by
                have : w0 ⟨i, hi⟩ ∈ ((Finset.univ : Finset (↥S)).image w0 : Finset (List Bool)) :=
                  Finset.mem_image_of_mem w0 (by simp)
                simp
              have mem_j : w0 ⟨j, hj⟩ ∈ (↑((Finset.univ : Finset (↥S)).image w0) : Set (List Bool)) := by
                have : w0 ⟨j, hj⟩ ∈ ((Finset.univ : Finset (↥S)).image w0 : Finset (List Bool)) :=
                  Finset.mem_image_of_mem w0 (by simp)
                simp

              have tail_eq : w0 ⟨i, hi⟩ = w0 ⟨j, hj⟩ :=
                hw0_prefix _ mem_i _ mem_j ht_tail

              simp [w, hi, hj, tail_eq]

            · -- i∈S, j∉S : impossible (0 :: …) <+: (1 :: …)
              have hxy' : (false :: w0 ⟨i, hi⟩) <+: (true :: w1 ⟨j, hj⟩) := by
                simp [w, hi, hj] at hxy
              rcases hxy' with ⟨t, ht⟩
              -- ht : 1 :: w1 j = (0 :: w0 i) ++ t = 0 :: (w0 i ++ t)
              have : true = false := by
                have : (true :: w1 ⟨j, hj⟩) = false :: (w0 ⟨i, hi⟩ ++ t) := by
                  simp [List.cons_append] at ht
                exact (List.cons.inj this).1
              cases this

            · -- i∉S, j∈S : impossible (1 :: …) <+: (0 :: …)
              have hxy' : (true :: w1 ⟨i, hi⟩) <+: (false :: w0 ⟨j, hj⟩) := by
                simp [w, hi, hj] at hxy
              rcases hxy' with ⟨t, ht⟩
              have : false = true := by
                have : (false :: w0 ⟨j, hj⟩) = true :: (w1 ⟨i, hi⟩ ++ t) := by
                  simp [List.cons_append] at ht
                exact (List.cons.inj this).1
              cases this

            · -- i∉S, j∉S
              have hxy' : (true :: w1 ⟨i, hi⟩) <+: (true :: w1 ⟨j, hj⟩) := by
                 simpa [w, hi, hj] using hxy
              rcases hxy' with ⟨t, ht⟩
              have ht_tail : w1 ⟨i, hi⟩ <+: w1 ⟨j, hj⟩ := by
                refine ⟨t, ?_⟩
                have : true :: (w1 ⟨i, hi⟩ ++ t) = (true :: w1 ⟨j, hj⟩)  := by
                  simpa [List.cons_append] using ht

                exact (List.cons.inj this).2

              have mem_i : w1 ⟨i, hi⟩ ∈ (↑((Finset.univ : Finset {x // x ∉ S}).image w1) : Set (List Bool)) := by
                have : w1 ⟨i, hi⟩ ∈ ((Finset.univ : Finset {x // x ∉ S}).image w1 : Finset (List Bool)) :=
                  Finset.mem_image_of_mem w1 (by simp)
                simp
              have mem_j : w1 ⟨j, hj⟩ ∈ (↑((Finset.univ : Finset {x // x ∉ S}).image w1) : Set (List Bool)) := by
                have : w1 ⟨j, hj⟩ ∈ ((Finset.univ : Finset {x // x ∉ S}).image w1 : Finset (List Bool)) :=
                  Finset.mem_image_of_mem w1 (by simp)
                simp

              have tail_eq : w1 ⟨i, hi⟩ = w1 ⟨j, hj⟩ :=
                hw1_prefix _ mem_i _ mem_j ht_tail

              simp [w, hi, hj, tail_eq]
          ·
            have hpos (i : I) : 0 < l i :=
              Nat.pos_of_ne_zero (by intro h0; exact h_exists_zero ⟨i, h0⟩)

            intro i
            by_cases hi : i ∈ S
            · simp [hi, hw0_len, l', Nat.sub_add_cancel (hpos i)]
            · simp [hi, hw1_len, l', Nat.sub_add_cancel (hpos i)]

  let m : ℕ := (Finset.univ : Finset I).sup l
  have hlm : ∀ i : I, l i ≤ m := by
    intro i; exact Finset.le_sup (s := (Finset.univ : Finset I)) (f := l) (by simp)
  have : ∃ w: I → List Bool, Function.Injective w ∧ PrefixFree (range w) ∧ ∀ i, (w i).length = l i :=
    h_ind m I l hlm h
  exact False.elim (h_contra this)
