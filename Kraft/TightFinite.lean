import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset

import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

import Kraft.Basic

namespace Kraft

open scoped BigOperators Real Nat

variable {I : Type _} [Fintype I] [DecidableEq I]

/-- If a multiset of natural numbers is a sub-multiset of the image of a function on a finite type,
then there exists a subset of the domain whose image equals that multiset.

This is used to lift a prefix of a sorted list of lengths back to a subset of the index type. -/
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
        simp_all only [ne_eq, Multiset.mem_toFinset]
      · simp [ Finset.mem_biUnion ]
        exact fun x hx => ⟨ v, Multiset.mem_toFinset.mp hv, hx, Finset.mem_filter.mp ( hS₁ v hv hx ) |>.2 ⟩
    obtain ⟨ S, hS ⟩ := h_union
    use S.filter (fun i => f i ∈ m)
    ext v
    by_cases hv : v ∈ m
    · simp_all only [ne_eq, Multiset.mem_toFinset, Finset.filter_val, Multiset.count_map, Multiset.filter_filter]
      convert hS v hv using 1
      exact congr_arg Finset.card (Finset.filter_congr fun x hx => by
        apply Iff.intro
        · intro a
          simp_all only
        · intro a
          subst a
          simp_all only [and_self]
      )
    · simp_all only [Finset.filter_val, Multiset.count_map, Multiset.filter_filter, not_false_eq_true, Multiset.count_eq_zero_of_notMem, Multiset.card_eq_zero, Multiset.filter_eq_nil, not_and]
      intro a a_1 a_2
      subst a_2
      exact hv
  exact h _ h_union.choose_spec

/-- In a list sorted by `≤`, earlier elements are at most later elements. -/
lemma pairwise_monotone
    {l : List ℕ} (h_sorted : l.Pairwise (fun a b => a ≤ b))
    {i j : ℕ} (hij : i < j) (hj : j < l.length) :
    l[i]! ≤ l[j]! := by
  have hget : ∀ (p q : Fin l.length), p < q → l.get p ≤ l.get q :=
    List.pairwise_iff_get.mp h_sorted
  have hi : i < l.length := lt_trans hij hj
  have := hget ⟨i, hi⟩ ⟨j, hj⟩ (by simpa using hij)
  simp_all only [List.get_eq_getElem, getElem!_pos]

/-- If a sorted list of lengths has Kraft sum ≥ 1, some prefix has Kraft sum exactly 1.

This is the key combinatorial lemma for the converse of Kraft's inequality: by sorting lengths
in non-decreasing order and taking partial sums, we can find a subset with sum exactly 1/2
(after appropriate scaling). The integrality of dyadic rationals makes the sum hit 1 exactly. -/
lemma exists_prefix_sum_eq_one_of_sorted {l : List ℕ} (h_sorted : l.Pairwise (· ≤ ·))
    (h_sum : (l.map (fun x => (1 / 2 : ℝ) ^ x)).sum ≥ 1) :
    ∃ l', l' <+: l ∧ (l'.map (fun x => (1 / 2 : ℝ) ^ x)).sum = 1 := by
  -- Let $k$ be the smallest index such that $s_k \geq 1$.
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k ≤ l.length ∧ (∑ i ∈ Finset.range k, (1 / 2 : ℝ) ^ l[i]!) ≥ 1 ∧ ∀ j < k, (∑ i ∈ Finset.range j, (1 / 2 : ℝ) ^ l[i]!) < 1 := by
    have h_exists_k : ∃ k : ℕ, k ≤ l.length ∧ (∑ i ∈ Finset.range k, (1 / 2 : ℝ) ^ l[i]!) ≥ 1 := by
      use l.length
      convert h_sum.le using 1
      norm_num [Finset.sum_range]
    -- Take the smallest such k
    use Nat.find h_exists_k
    obtain ⟨hk_len, hk_ge⟩ := Nat.find_spec h_exists_k
    refine ⟨hk_len, hk_ge, fun j hj => ?_⟩
    -- For j < k, the sum must be < 1 (otherwise k wouldn't be minimal)
    by_contra h_not_lt
    push_neg at h_not_lt
    exact Nat.find_min h_exists_k hj ⟨Nat.le_trans (Nat.le_of_lt hj) hk_len, h_not_lt⟩
  -- Let $M$ be the integer such that $s_{k-1} = M / 2^{l_k}$.
  obtain ⟨M, hM⟩ : ∃ M : ℕ, (∑ i ∈ Finset.range (k - 1), (1 / 2 : ℝ) ^ l[i]!) = M / 2 ^ l[k - 1]! := by
    -- Since $l$ is sorted non-decreasingly, we have $l[i] \leq l[k-1]$ for all $i < k-1$.
    have h_le : ∀ i < k - 1, l[i]! ≤ l[k - 1]! := by
      intro i hi
      have hkpos' : k.sub 0 ≠ 0 := by
        -- i < k-1 forces k ≠ 0
        intro hk0
        have : k - 1 = 0 := by simp_all only [one_div, inv_pow, ge_iff_le, List.getElem!_eq_getElem?_getD, Nat.default_eq_zero, Nat.sub_eq, tsub_zero, zero_tsub]
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
    rcases k
    · simp_all only [zero_le, Finset.range_zero, Finset.sum_empty, not_lt_zero, IsEmpty.forall_iff]
      linarith
    · simp_all only [one_div, inv_pow, Finset.sum_range_succ, add_tsub_cancel_right]
      ring

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
          simp_all only [one_div, inv_pow, ge_iff_le, List.getElem!_eq_getElem?_getD, Nat.default_eq_zero, Nat.ofNat_pos,
            pow_pos, Nat.cast_pred, Nat.cast_pow, Nat.cast_ofNat, le_refl, sub_add_cancel, ne_eq, pow_eq_zero_iff',
            OfNat.ofNat_ne_zero, false_and, not_false_eq_true, div_self, List.map_take, List.get_eq_getElem,
            List.take_append_getElem]
        rw [h_take, List.map_append, List.sum_append]
        -- 3. Use IH for the prefix
        rw [ih (Nat.le_of_succ_le hk)]
        -- 4. Prove the last terms are equal
        simp_all only [lt_of_lt_of_le (Nat.lt_succ_self k) hk, Nat.ofNat_pos,
                      pow_pos, Nat.cast_pred, le_refl, sub_add_cancel,  List.get_eq_getElem,
                      List.take_append_getElem, getElem!_pos, List.map_cons, List.map_nil,
                      List.sum_cons, List.sum_nil, add_zero]
    rw [ h_sum_eq l k hk.1 ]

/-- If the Kraft sum over a finite index set is ≥ 1, there exists a subset with sum exactly 1.

This lemma is used in the recursive construction: when the total sum exceeds 1/2, we can
partition the indices into two parts each with sum exactly 1/2, enabling the inductive step. -/
lemma exists_subset_sum_eq_one (l : I → ℕ)
    (h_sum : 1 ≤ ∑ i, (1 / 2 : ℝ) ^ l i) :
    ∃ S : Finset I, ∑ i ∈ S, (1 / 2 : ℝ) ^ l i = 1 := by
  -- Let $n = |I|$ and let $\ell'_1,\dots,\ell'_n$ consist of $(\ell(i))_{i \in I}$ arranged in nonincreasing order.
  set n := Fintype.card I
  obtain ⟨ℓ', hℓ'⟩ : ∃ ℓ' : Fin n → ℕ, Multiset.ofList (List.ofFn ℓ') = Multiset.map l Finset.univ.val := by
    -- Let $ℓ'$ be the list of values of $l$ on the elements of $I$.
    obtain ⟨ℓ', hℓ'⟩ : ∃ ℓ' : List ℕ, List.length ℓ' = n ∧ Multiset.ofList ℓ' = Multiset.map l Finset.univ.val := by
      use Finset.univ.val.map l |> Multiset.toList
      simp_all only [n, Multiset.length_toList, Multiset.card_map, Finset.card_val, Finset.card_univ, Multiset.coe_toList, and_self]
    use fun i => ℓ'.get (i.cast hℓ'.1.symm) -- Cast the Fin n to a valid index for ℓ'
    convert hℓ'.2 using 2
    have h_len : (List.ofFn fun i : Fin n => ℓ'.get (i.cast hℓ'.1.symm)).length = ℓ'.length := by
      simp only [List.length_ofFn, hℓ'.1]
    refine' List.ext_get h_len _
    simp_all only [List.get_eq_getElem, Fin.coe_cast, List.getElem_ofFn, implies_true]
  -- Apply `exists_prefix_sum_eq_one_of_sorted` to the sorted list.
  obtain ⟨l'', hl''⟩ : ∃ l'' : List ℕ, l''.Perm (List.ofFn ℓ') ∧ List.Pairwise (· ≤ ·) l'' ∧ (l''.map (fun x => (1 / 2 : ℝ) ^ x)).sum ≥ 1 := by
    refine' ⟨ List.ofFn ℓ' |> List.insertionSort ( · ≤ · ), _, _, _ ⟩
    · exact List.perm_insertionSort (fun x1 x2 ↦ x1 ≤ x2) (List.ofFn ℓ')
    · exact List.pairwise_insertionSort _ _
    · have h_sum_eq : (List.map (fun x => (1 / 2 : ℝ) ^ x) (List.ofFn ℓ')).sum = ∑ i, (1 / 2 : ℝ) ^ (l i) := by
        have h_sum_eq : (List.map (fun x => (1 / 2 : ℝ) ^ x) (List.ofFn ℓ')).sum = Multiset.sum (Multiset.map (fun x => (1 / 2 : ℝ) ^ x) (Multiset.ofList (List.ofFn ℓ'))) := by
          rfl
        simp_all only [ Multiset.map_map, Function.comp_apply, Finset.sum_map_val]
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
  simp_all only [Multiset.map_map, Multiset.map_coe, Multiset.sum_coe]
  apply Exists.intro
  exact hS

/-- The image of a code function as a set. -/
@[simp]
def range (w: I → List Bool) := ((Finset.univ.image w): Set (List Bool))

/-- **Converse of Kraft's Inequality** (finite case): If `Σ 2^{-ℓ(i)} ≤ 1`, there exists
an injective function `w : I → List Bool` whose image is prefix-free with `|w(i)| = ℓ(i)`.

The proof is by strong induction on the maximum length. We partition the index set into
two parts S and Sᶜ, each with Kraft sum ≤ 1/2, then recursively construct codes for each
and prepend 0 to one and 1 to the other. -/
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
      · simp_all only [nonpos_iff_eq_zero, pow_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Nat.cast_le_one]
        interval_cases z : Fintype.card I <;> simp_all [ Fintype.card_eq_one_iff ]
        obtain ⟨w, h_1⟩ := z
        simp_all only [forall_const]
        apply Exists.intro
        · constructor
          · intro a₁ a₂ a
            simp_all only
          · constructor
            · intro x a y a_1 a_2
              simp_all only [Set.mem_range, exists_const]
            · rfl
      · -- hI : ¬ Nonempty I
        haveI : IsEmpty I := ⟨fun i => hI ⟨i⟩⟩
        refine ⟨(fun i => isEmptyElim i), ?_, ?_, ?_⟩
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
          -- The term (1/2)^0 = 1 already saturates the sum
          have h_sum_ge : ∑ i, (1 / 2 : ℝ) ^ l i ≥ 1 :=
            le_trans (by norm_num [hi₀]) (Finset.single_le_sum (fun _ _ => by positivity) (Finset.mem_univ i₀))
          -- So the sum over remaining elements must be 0
          have h_rest_zero : ∑ i ∈ Finset.univ.erase i₀, (1 / 2 : ℝ) ^ l i = 0 := by
            have h1 : ∑ i, (1 / 2 : ℝ) ^ l i = 1 := le_antisymm hsum h_sum_ge
            simp_all only [not_exists, not_and, Finset.mem_univ, Finset.sum_erase_eq_sub, pow_zero, sub_self]
          -- A sum of positive terms is 0 only if the set is empty
          have h_empty : Finset.univ.erase i₀ = ∅ := by
            by_contra h_ne
            have := Finset.sum_pos (fun x _ => by positivity : ∀ x ∈ Finset.univ.erase i₀, 0 < (1/2 : ℝ) ^ l x)
                    (Finset.nonempty_of_ne_empty h_ne)
            linarith
          simp only [Finset.erase_eq_empty_iff, Finset.univ_eq_empty_iff] at h_empty
          -- h_empty : IsEmpty I ∨ Finset.univ = {i₀}
          rcases h_empty with h_empty | h_univ
          · exact (h_empty.false i₀).elim
          · simp [← Finset.card_univ, h_univ]
        rw [ Fintype.card_eq_one_iff ] at h_card
        obtain ⟨ x, hx ⟩ := h_card
        use fun _ => List.replicate (l x) Bool.true
        simp [Function.Injective, hx, PrefixFree]
      · -- If $\sum_{i \in I} 2^{-\ell(i)} \leq \frac{1}{2}$, then we can take $S = I$.
        by_cases h_sum_half : (∑ i, (1 / 2 : ℝ) ^ (l i)) ≤ 1 / 2
        · -- Define $\ell'\colon I \to \mathbb{N}$ by $\ell'(i) = \ell(i) - 1$.
          let l' : I → ℕ := fun i => l i - 1
          -- By the induction hypothesis, there exists an injective mapping $w' \colon I \to \{0,1\}^*$ whose image is prefix-free, and furthermore $|w'(i)| = \ell'(i)$.
          obtain ⟨w', hw'_inj, hw'_prefix, hw'_length⟩ : ∃ (w' : I → (List Bool)), (Function.Injective w') ∧ (PrefixFree (range w')) ∧ (∀ i, ((w' i).length = (l' i))) := by
            apply ih I l'
            · exact fun i => Nat.sub_le_of_le_add <| by linarith [ hl i ]
            · convert mul_le_mul_of_nonneg_left h_sum_half zero_le_two using 1 <;> norm_num [ pow_succ', Finset.mul_sum _ _ _ ]
              exact Finset.sum_congr rfl fun i _ => by rw [ show l i = l' i + 1 by rw [ Nat.sub_add_cancel ( Nat.pos_of_ne_zero fun hi => h_exists_zero ⟨ i, hi ⟩ ) ] ]; ring
          use fun i => false :: w' i
          simp_all only [Function.Injective, PrefixFree, range, Finset.coe_image, Finset.coe_univ,
                         Set.image_univ, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff, not_exists,
                         List.cons.injEq, true_and, List.cons_prefix_cons, List.length_cons]
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
          let l' : I → ℕ := fun i => l i - 1
          -- By the induction hypothesis,
          -- there exist injective maps $w_0\colon S \to bool^*$ and $w_1\colon S^c \to bool^*$
          -- such that $w_0(S)$ and $w_1(S^c)$ are prefix-free;
          -- $|w_0(i)| = \ell'(i)$ for all $i \in S$; and $|w_1(i)| = \ell'(i)$ for all $i \in S^c$.
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
                  rw [ Finset.mul_sum _ _ _ ]
                  refine' Finset.sum_congr rfl (fun i hi => _)
                  rcases k : l i with ( _ | k )
                  · exfalso
                    apply h_exists_zero
                    use i
                  · simp [ pow_succ' ]
                linarith
              convert h_sum_complement using 1
              refine' Finset.sum_bij ( fun x _ => x ) _ _ _ _ <;> simp
              exact fun _ _ => rfl
          -- Define $w\colon I \to \{false, true\}^*$ by
          use fun i => if hi : i ∈ S then false :: w0 ⟨i, hi⟩
                                     else true  :: w1 ⟨i, hi⟩
          refine' ⟨ _, _, _ ⟩
          · intro i j hij
            by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp [ hi, hj ] at hij ⊢
            · exact Subtype.ext_iff.mp ( hw0_inj hij )
            · exact congr_arg Subtype.val ( hw1_inj hij )
          ·
            -- abbreviate the combined map (same as your `use fun i => if ...`)
            let w : I → List Bool :=
              fun i => if hi : i ∈ S then (false :: w0 ⟨i, hi⟩) else (true :: w1 ⟨i, hi⟩)

            intro x hx y hy hxy

            -- move membership from Set-coe to Finset membership, so we can `mem_image` cleanly
            have hx' : x ∈ range w := by simpa using hx
            rcases Finset.mem_image.mp hx' with ⟨i, hiU, rfl⟩

            have hy' : y ∈ range w := by simpa using hy
            rcases Finset.mem_image.mp (hy') with ⟨j, hjU, rfl⟩

            by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp only [w, hi, hj] at hxy ⊢
            · -- i∈S, j∈S: use prefix-freeness of w0
              have := (List.cons_prefix_cons (a := false)).mp hxy
              exact congrArg _ (hw0_prefix _ (by simp) _ (by simp) this.2)
            · -- i∈S, j∉S: impossible (false :: …) <+: (true :: …)
              exact absurd (List.cons_prefix_cons.mp hxy).1 Bool.false_ne_true
            · -- i∉S, j∈S: impossible (true :: …) <+: (false :: …)
              exact absurd (List.cons_prefix_cons.mp hxy).1.symm Bool.false_ne_true
            · -- i∉S, j∉S: use prefix-freeness of w1
              have := (List.cons_prefix_cons (a := true)).mp hxy
              exact congrArg _ (hw1_prefix _ (by simp) _ (by simp) this.2)
          ·
            have hpos (i : I) : 0 < l i :=
              Nat.pos_of_ne_zero (by intro h0; exact h_exists_zero ⟨i, h0⟩)

            intro i
            by_cases hi : i ∈ S
            · simp [hi, hw0_len, l', Nat.sub_add_cancel (hpos i)]
            · simp [hi, hw1_len, l', Nat.sub_add_cancel (hpos i)]

  let m : ℕ := Finset.univ.sup l
  have hlm : ∀ i : I, l i ≤ m := by
    intro i
    exact Finset.univ.le_sup (f := l) (by simp)
  have : ∃ w: I → List Bool, Function.Injective w ∧ PrefixFree (range w) ∧ ∀ i, (w i).length = l i :=
    h_ind m I l hlm h
  exact False.elim (h_contra this)
