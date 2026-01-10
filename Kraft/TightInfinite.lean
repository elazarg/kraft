import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.RelIso.Basic

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Kraft.Basic
import Kraft.InequalityFinite

namespace Kraft

open scoped BigOperators Real

/-- Converts a natural number `n` to a big-endian list of bits of length `width`.

For example, `natToBits 5 4 = [false, true, false, true]` representing 0101₂ = 5. -/
def natToBits (n width : ℕ) : List Bool :=
  List.ofFn (fun i : Fin width => n.testBit (width - 1 - i))

/-- `natToBits` is injective for numbers less than `2^width`. -/
lemma natToBits_inj {n m width : ℕ} (hn : n < 2 ^ width) (hm : m < 2 ^ width)
    (h : natToBits n width = natToBits m width) : n = m := by
      refine' Nat.eq_of_testBit_eq fun i => _
      by_cases hi : i < width <;> simp_all [Nat.testBit]
      · replace h := congr_arg ( fun l => l[width - 1 - i ]! ) h
        simp_all [Nat.shiftRight_eq_div_pow]
        unfold Kraft.natToBits at h
        simp_all [ Nat.testBit, Nat.shiftRight_eq_div_pow ]

        have hw : 0 < width := (by exact Nat.zero_lt_of_lt hi)
        have hcond : width - 1 - i < width := by
          -- ≤ width-1 < width
          have hle : width - 1 - i ≤ width - 1 := Nat.sub_le _ _
          exact lt_of_le_of_lt hle (Nat.pred_lt (by exact Nat.ne_zero_of_lt hi))

        have hsub : width - 1 - (width - 1 - i) = i := by
          -- `i ≤ width-1` since `i < width`
          have hi' : i ≤ width - 1 := Nat.le_pred_of_lt hi
          -- standard arithmetic on `Nat` subtraction
          omega

        -- extract the Bool equality from `h` and convert == to =
        have hbool : (n / 2 ^ i % 2 == 1) = (m / 2 ^ i % 2 == 1) := by simpa [hcond, hsub] using h
        simpa [Nat.beq_eq_true_eq, decide_eq_decide] using hbool

      · rw [ Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow ]
        rw [ Nat.div_eq_of_lt ( lt_of_lt_of_le hn ( Nat.pow_le_pow_right ( by decide ) hi ) ), Nat.div_eq_of_lt ( lt_of_lt_of_le hm ( Nat.pow_le_pow_right ( by decide ) hi ) ) ]

/-- `natToBits n w` is a prefix of `natToBits m v` iff `w ≤ v` and `m` lies in the
dyadic interval `[n·2^{v-w}, (n+1)·2^{v-w})`. This characterizes when two codewords
in our construction have a prefix relationship. -/
lemma natToBits_prefix_iff {n m w v : ℕ} (hn : n < 2 ^ w) (hm : m < 2 ^ v) :
    natToBits n w <+: natToBits m v ↔ w ≤ v ∧ n * 2 ^ (v - w) ≤ m ∧ m < (n + 1) * 2 ^ (v - w) := by
      constructor <;> intro h_1
      · -- If `natToBits n w` is a prefix of `natToBits m v`, then `w ≤ v`.
        have h_le : w ≤ v := by
          have := h_1.length_le
          unfold Kraft.natToBits at this
          simp_all only [List.length_ofFn]
        -- If `natToBits n w` is a prefix of `natToBits m v`, then `m >> (v - w) = n`.
        have h_shift : m / 2 ^ (v - w) = n := by
          have h_shift : ∀ k < w, m.testBit (v - 1 - k) = n.testBit (w - 1 - k) := by
            rw [ Kraft.natToBits, Kraft.natToBits ] at h_1
            obtain ⟨ k, hk ⟩ := h_1
            intro i hi
            replace hk := congr_arg ( fun l => l[i]! ) hk
            have hiv : i < v := lt_of_lt_of_le hi h_le
            have hnmi : m.testBit (v - 1 - i) = n.testBit (w - 1 - i) := by
                -- 1. Accessing index 'i' in 'L1 ++ k' falls into 'L1' because i < length L1
                simp_all
                rw [List.getElem?_append_left] at hk
                · -- 2. Accessing index 'i' in 'List.ofFn f' is just 'f i'
                  rw [List.getElem?_ofFn] at hk
                  simp_all
                · -- Proof that i < length L1 (for step 1)
                  simp [hi]
            exact hnmi
          refine' Nat.eq_of_testBit_eq _
          intro i
          specialize h_shift ( w - 1 - i )
          rcases lt_trichotomy i ( w - 1 ) with hi | rfl | hi <;> simp_all [ Nat.testBit ]
          · convert h_shift ( by omega ) using 2 <;> norm_num [ Nat.shiftRight_eq_div_pow ]
            · rw [ Nat.div_div_eq_div_mul ]
              rw [ ← pow_add, show v - w + i = v - 1 - ( w - 1 - i ) by omega ]
            · rw [ Nat.sub_sub_self ( by omega ) ]
          · rcases w with ( _ | w ) <;> simp_all [ Nat.shiftRight_eq_div_pow ]
            · rw [ Nat.div_eq_of_lt hm, Nat.zero_mod ]
            · convert h_shift using 1
              rw [ show v - 1 = v - ( w + 1 ) + w by omega, pow_add ]
              norm_num [ Nat.div_div_eq_div_mul ]
          · rw [ Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow ]
            rw [ Nat.div_eq_of_lt, Nat.div_eq_of_lt ]
            · exact hn.trans_le ( Nat.pow_le_pow_right ( by decide ) ( by omega ) )
            · rw [ Nat.div_lt_iff_lt_mul <| by positivity ]
              rw [ ← pow_add ]
              exact hm.trans_le ( pow_le_pow_right₀ ( by decide ) ( by omega ) )
        exact ⟨ h_le, by nlinarith [ Nat.div_mul_le_self m ( 2 ^ ( v - w ) ), pow_pos ( zero_lt_two' ℕ ) ( v - w ) ], by nlinarith [ Nat.div_add_mod m ( 2 ^ ( v - w ) ), Nat.mod_lt m ( pow_pos ( zero_lt_two' ℕ ) ( v - w ) ), pow_pos ( zero_lt_two' ℕ ) ( v - w ) ] ⟩
      · -- Since $m$ lies in the dyadic interval corresponding to $n$, the binary representation of $m$ starts with the binary representation of $n$.
        have h_binary : ∀ i : Fin w, (m.testBit (v - 1 - i)) = (n.testBit (w - 1 - i)) := by
          intro i
          have h_div : m / 2 ^ (v - w) = n := by
            exact Nat.le_antisymm ( Nat.le_of_lt_succ <| Nat.div_lt_of_lt_mul <| by linarith ) ( Nat.le_div_iff_mul_le ( by positivity ) |>.2 <| by linarith )
          -- 1. Replace n with the division form given in h_div
          rw [← h_div]

          -- 2. Use the lemma that relates bit-testing on division to bit-testing on the original number
          -- Lemma: (m / 2^k).testBit i = m.testBit (i + k)
          rw [Nat.testBit_div_two_pow]

          -- 3. Now the goal is m.testBit (...) = m.testBit (...).
          -- We just need to prove the indices are equal.
          congr 1

          -- 4. Prove the arithmetic equality: (v - 1 - i) = (w - 1 - i) + (v - w)
          -- We need to unpack the fact that i < w and w ≤ v to ensure subtraction behaves nicely.
          have hi : ↑i < w := i.isLt
          have hwv : w ≤ v := h_1.1
          omega
        unfold Kraft.natToBits
        refine' ⟨ List.ofFn fun i : Fin ( v - w ) => m.testBit ( v - 1 - ( w + i ) ), _ ⟩
        refine' List.ext_get _ _ <;> simp_all [ List.getElem_append ]
        intro i hi
        split_ifs <;> simp_all [ Nat.sub_sub, add_comm ]
        exact Eq.symm ( h_binary ⟨ i, by linarith ⟩ )

/-- The "address" function for constructing prefix-free codes.

For a monotone length sequence `l`, `kraft_A l n` is chosen so that `kraft_A l n / 2^{l n}`
equals the partial Kraft sum `Σ_{k<n} 2^{-l k}`. The codeword for index `n` is then
`natToBits (kraft_A l n) (l n)`. -/
def kraft_A (l : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => (kraft_A l n + 1) * 2 ^ (l (n + 1) - l n)

/-- `kraft_A l n / 2^{l n}` equals the partial Kraft sum `Σ_{k<n} 2^{-l k}`.

This is the key invariant that ensures non-overlapping dyadic intervals. -/
lemma kraft_A_div_pow_eq_sum (l : ℕ → ℕ) (h_mono : Monotone l) (n : ℕ) :
    (kraft_A l n : ℝ) / 2 ^ l n = ∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ l k := by
      induction n <;> simp_all [Finset.sum_range_succ]
      -- Substitute the definition of `kraft_A` into the left-hand side.
      have h_sub : (Kraft.kraft_A l (Nat.succ ‹_›) : ℝ) = (Kraft.kraft_A l ‹_› + 1) * 2 ^ (l (Nat.succ ‹_›) - l ‹_›) := by
        norm_cast
      rw [ ← ‹ ( Kraft.kraft_A l _ : ℝ ) / 2 ^ l _ = ∑ x ∈ Finset.range _, ( 2 ^ l x ) ⁻¹ ›, h_sub ]
      rw [ show l ( _ + 1 ) = l _ + ( l ( _ + 1 ) - l _ ) by rw [ Nat.add_sub_of_le ( h_mono ( Nat.le_succ _ ) ) ] ]
      ring_nf
      -- Combine like terms and simplify the expression.
      field_simp
      ring_nf
      norm_num [ ← mul_pow ]

/-- Converse of Kraft's inequality for monotone length sequences indexed by ℕ.

Given a monotone `l : ℕ → ℕ` with summable Kraft sum ≤ 1, we construct a prefix-free
code by assigning to index `n` the codeword `natToBits (kraft_A l n) (l n)`. -/
theorem kraft_inequality_tight_nat_mono (l : ℕ → ℕ) (h_mono : Monotone l)
    (h_summable : Summable (fun i => (1 / 2 : ℝ) ^ l i))
    (h_sum : ∑' i, (1 / 2 : ℝ) ^ l i ≤ 1) :
    ∃ w : ℕ → List Bool,
      Function.Injective w ∧
      Kraft.PrefixFree (Set.range w) ∧
      ∀ i, (w i).length = l i := by
        -- By definition of $kraft_A$, we know that $kraft_A n < 2^{l n}$ for all $n$.
        have h_kraft_A_lt : ∀ n, kraft_A l n < 2 ^ l n := by
          intro n
          -- The partial Kraft sum equals kraft_A / 2^l
          have h_eq : (kraft_A l n : ℝ) / 2 ^ l n = ∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ l k :=
            kraft_A_div_pow_eq_sum l h_mono n
          -- Partial sum < partial sum with one more term
          have h_lt_succ : ∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ l k < ∑ k ∈ Finset.range (n + 1), (1 / 2 : ℝ) ^ l k := by
            simp [Finset.sum_range_succ]
          -- Partial sum ≤ tsum
          have h_le_tsum : ∑ k ∈ Finset.range (n + 1), (1 / 2 : ℝ) ^ l k ≤ ∑' k, (1 / 2 : ℝ) ^ l k :=
            Summable.sum_le_tsum _ (fun _ _ => by positivity) h_summable
          -- Combine: partial sum < tsum ≤ 1
          have h_lt_one : ∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ l k < 1 :=
            lt_of_lt_of_le (lt_of_lt_of_le h_lt_succ h_le_tsum) h_sum
          rw [<-h_eq, div_lt_one (by positivity)] at h_lt_one
          exact_mod_cast h_lt_one
        refine' ⟨ fun n => natToBits ( kraft_A l n ) ( l n ), _, _, _ ⟩
        · intro n m hnm
          -- Since $kraft_A n < 2^{l n}$ and $kraft_A m < 2^{l m}$, and $natToBits$ is injective, we have $kraft_A n = kraft_A m$.
          have h_kraft_A_eq : kraft_A l n = kraft_A l m := by
            apply natToBits_inj
            exact h_kraft_A_lt n
            · unfold Kraft.natToBits at hnm
              replace hnm := congr_arg List.length hnm
              simp_all only [one_div, inv_pow, List.length_ofFn]
            · have := congr_arg List.length hnm
              norm_num [ Kraft.natToBits ] at this
              simp_all only [one_div, inv_pow]
          -- Since $kraft_A$ is strictly increasing, we have $n = m$.
          have h_kraft_A_inj : StrictMono (kraft_A l) := by
            refine' strictMono_nat_of_lt_succ _
            intro n
            exact lt_of_lt_of_le ( by norm_num ) ( Nat.mul_le_mul_left _ ( Nat.one_le_pow _ _ ( by norm_num ) ) )
          exact h_kraft_A_inj.injective h_kraft_A_eq
        · rintro _ ⟨ n, rfl ⟩ _ ⟨ m, rfl ⟩ hnm
          by_cases hnm' : n = m <;> simp_all [ natToBits_prefix_iff ]
          -- Since $l n \le l m$, we have $S_n \le S_m < S_n + 2^{-l n}$.
          have h_sum_bounds : (∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ l k) ≤ (∑ k ∈ Finset.range m, (1 / 2 : ℝ) ^ l k) ∧ (∑ k ∈ Finset.range m, (1 / 2 : ℝ) ^ l k) < (∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ l k) + (1 / 2 : ℝ) ^ l n := by
            have h_sum_bounds : (kraft_A l n : ℝ) / 2 ^ l n ≤ (kraft_A l m : ℝ) / 2 ^ l m ∧ (kraft_A l m : ℝ) / 2 ^ l m < (kraft_A l n : ℝ) / 2 ^ l n + (1 / 2 : ℝ) ^ l n := by
              field_simp
              norm_num [ mul_assoc, ← mul_pow ]
              norm_cast
              rw [ show 2 ^ l m = 2 ^ l n * 2 ^ ( l m - l n ) by rw [ ← pow_add, Nat.add_sub_of_le hnm.1 ] ]
              constructor <;> nlinarith [ pow_pos ( zero_lt_two' ℕ ) ( l n ), pow_pos ( zero_lt_two' ℕ ) ( l m - l n ) ]
            convert h_sum_bounds using 2 <;> norm_num [ kraft_A_div_pow_eq_sum ]
            · rw [ kraft_A_div_pow_eq_sum ]
              assumption
            · rw [ kraft_A_div_pow_eq_sum ]
              assumption
            · rw [ kraft_A_div_pow_eq_sum ]
              assumption
            · rw [ kraft_A_div_pow_eq_sum ]
              assumption
          cases lt_or_gt_of_ne hnm' <;> simp_all
          · -- Since $n < m$, we have $\sum_{k=n}^{m-1} 2^{-l k} \geq 2^{-l n}$.
            have h_sum_ge : ∑ k ∈ Finset.Ico n m, (1 / 2 : ℝ) ^ l k ≥ (1 / 2 : ℝ) ^ l n := by
              exact le_trans ( by norm_num ) ( Finset.single_le_sum ( fun x _ => by positivity ) ( Finset.left_mem_Ico.mpr ‹_› ) )
            simp_all [ Finset.sum_Ico_eq_sub _ ( by linarith : n ≤ m ) ]
            linarith
          · -- Since $m < n$, we have $\sum_{k=m}^{n-1} 2^{-l k} \geq 2^{-l n}$.
            have h_sum_ge : ∑ k ∈ Finset.Ico m n, (1 / 2 : ℝ) ^ l k ≥ (1 / 2 : ℝ) ^ l n := by
              exact le_trans ( by norm_num ) ( Finset.single_le_sum ( fun x _ => by positivity ) ( Finset.mem_Ico.mpr ⟨ le_rfl, by linarith ⟩ ) ) |> le_trans <| Finset.sum_le_sum fun x hx => pow_le_pow_of_le_one ( by norm_num ) ( by norm_num ) <| h_mono <| Finset.mem_Ico.mp hx |>.2.le
            simp_all [ Finset.sum_Ico_eq_sub _ ( by linarith : m ≤ n ) ]
            linarith
        · unfold Kraft.natToBits
          intro i
          simp_all only [one_div, inv_pow, List.length_ofFn]

/-- A strict total order on indices: first by length, then by an auxiliary embedding.

This is used to enumerate elements in an order that makes the length function monotone. -/
def KraftOrder {I : Type _} (l : I → ℕ) (e : I ↪ ℕ) (i j : I) : Prop :=
  Prod.Lex (· < ·) (· < ·) (l i, e i) (l j, e j)

/-- `KraftOrder` is equivalent to: `l i < l j` or (`l i = l j` and `e i < e j`). -/
lemma KraftOrder_iff {I : Type _} {l : I → ℕ} {e : I ↪ ℕ} {i j : I} :
    KraftOrder l e i j ↔ l i < l j ∨ (l i = l j ∧ e i < e j) :=
  Prod.lex_iff

/-- `KraftOrder` is a strict total order. -/
lemma KraftOrder_isStrictTotalOrder {I : Type _} (l : I → ℕ) (e : I ↪ ℕ) :
    IsStrictTotalOrder I (KraftOrder l e) where
  trichotomous a b := by
    simp only [KraftOrder_iff]
    rcases lt_trichotomy (l a) (l b) with h | h | h
    · exact Or.inl (Or.inl h)
    · rcases lt_trichotomy (e a) (e b) with h' | h' | h'
      · left; right
        exact ⟨h, h'⟩
      · right; left
        exact e.injective h'
      · right; right; right
        exact ⟨h.symm, h'⟩
    · exact Or.inr (Or.inr (Or.inl h))
  irrefl a h := by
    simp only [KraftOrder_iff] at h
    rcases h with h | ⟨_, h⟩ <;> exact lt_irrefl _ h
  trans a b c hab hbc := by
    simp only [KraftOrder_iff] at *
    rcases hab with hab | ⟨hab, hab'⟩ <;> rcases hbc with hbc | ⟨hbc, hbc'⟩
    · exact Or.inl (lt_trans hab hbc)
    · left
      rw [<-hbc] at *
      exact hab
    · left
      rw [<-hab] at *
      exact hbc
    · right
      rw [<-hab] at *
      exact ⟨hbc, lt_trans hab' hbc'⟩

/-- Initial segments of `KraftOrder` are finite when length fibers are finite.

Since each length has only finitely many indices (by summability), the set of
indices smaller than any given index is finite. -/
lemma KraftOrder_finite_initial_segment {I : Type _} (l : I → ℕ) (e : I ↪ ℕ)
    (h_finite : ∀ k, {i | l i = k}.Finite) (i : I) :
    {j | KraftOrder l e j i}.Finite := by
  have h_subset : {j | KraftOrder l e j i} ⊆ {j | l j < l i} ∪ {j | l j = l i} := by
    intro j hj
    simp only [KraftOrder_iff] at hj
    rcases hj with h | ⟨h, _⟩ <;> simp [h]
  refine Set.Finite.subset ?_ h_subset
  apply Set.Finite.union
  · -- Case 1: Strictly smaller lengths
    -- We rewrite the set of elements with smaller length as a bounded Union of fibers
    have h_decomp : {j | l j < l i} = ⋃ k ∈ Finset.range (l i), {j | l j = k} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_range]
      constructor
      · intro h
        use (l x)
      · intro ⟨k, hk_lt, hk_eq⟩; rw [hk_eq]; exact hk_lt
    rw [h_decomp]
    -- A finite union of finite sets is finite
    apply Set.Finite.biUnion
    · exact (Finset.range (l i)).finite_toSet
    · simp_all
  · -- Case 2: Equal length
    exact h_finite (l i)

/-- The rank of an element is the number of elements strictly smaller in `KraftOrder`.

This gives a bijection between `I` and `ℕ` that makes `l` monotone. -/
noncomputable def kraftRank {I : Type _} (l : I → ℕ) (e : I ↪ ℕ)
    (h_finite : ∀ k, {i | l i = k}.Finite) (i : I) : ℕ :=
  (KraftOrder_finite_initial_segment l e h_finite i).toFinset.card

/-- `kraftRank` is strictly monotone with respect to `KraftOrder`. -/
lemma kraftRank_lt_of_KraftOrder {I : Type _} (l : I → ℕ) (e : I ↪ ℕ)
    (h_finite : ∀ k, {i | l i = k}.Finite) {i j : I} (h : KraftOrder l e i j) :
    kraftRank l e h_finite i < kraftRank l e h_finite j := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · -- Subset: {x | x < i} ⊆ {x | x < j} by transitivity
    intro x
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    intro h
    exact (KraftOrder_isStrictTotalOrder l e).trans x i j h (by assumption)
  · -- Strictness: i ∈ {x | x < j} but i ∉ {x | x < i}
    simp only [ne_eq, Finset.ext_iff, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_forall]
    use i
    intro hm
    rw [<-hm] at h
    unfold KraftOrder at h
    simp_all only [KraftOrder, true_iff, Prod.lex_def]
    omega

/-- `kraftRank` is surjective onto ℕ when `I` is infinite. -/
lemma kraftRank_surjective {I : Type _} [Infinite I] (l : I → ℕ) (e : I ↪ ℕ)
    (h_finite : ∀ k, {i | l i = k}.Finite) :
    Function.Surjective (kraftRank l e h_finite) := by
  have hsto := KraftOrder_isStrictTotalOrder l e
  -- kraftRank is injective (distinct elements have distinct ranks)
  have h_inj : Function.Injective (kraftRank l e h_finite) := by
    intro i j hij
    rcases hsto.trichotomous i j with h | rfl | h
    · exact absurd hij (ne_of_lt (kraftRank_lt_of_KraftOrder l e h_finite h))
    · rfl
    · exact absurd hij (ne_of_gt (kraftRank_lt_of_KraftOrder l e h_finite h))
  -- The range is an initial segment: if n is in range, so is every m < n
  have h_initial : ∀ n, (∃ i, kraftRank l e h_finite i = n) → ∀ m < n, ∃ i, kraftRank l e h_finite i = m := by
    intro n ⟨i, hi⟩ m hm
    -- The image of {j | j < i} under kraftRank is exactly {0, ..., n-1}
    have h_image : Finset.image (kraftRank l e h_finite)
        (KraftOrder_finite_initial_segment l e h_finite i).toFinset = Finset.range n := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        simp only [Finset.mem_image, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx
        obtain ⟨j, hj, rfl⟩ := hx
        exact Finset.mem_range.mpr (hi ▸ kraftRank_lt_of_KraftOrder l e h_finite hj)
      · rw [Finset.card_range, Finset.card_image_of_injective _ (fun _ _ => by
          intro a
          subst hi
          apply h_inj
          simp_all only)]
        simp_all [kraftRank]
    have hi := Finset.ext_iff.mp h_image m
    simp only [Finset.mem_image, Set.Finite.mem_toFinset, Set.mem_setOf_eq,
               Finset.mem_range, hm, iff_true] at hi
    obtain ⟨a, ⟨_, hl⟩⟩ := hi
    use a
  -- The range is infinite (since I is infinite and kraftRank is injective)
  have h_infinite : Set.Infinite (Set.range (kraftRank l e h_finite)) :=
    Set.infinite_range_of_injective h_inj
  -- An infinite initial segment of ℕ is all of ℕ
  rw [Set.infinite_iff_exists_gt] at h_infinite
  intro n
  obtain ⟨val_i, ⟨⟨witness_i, h_rank_eq⟩, h_n_lt_i⟩⟩ := h_infinite n
  -- We found a value `val_i` (witnessed by `witness_i`) such that `n < val_i`.
  -- Since the range is an initial segment, `n` must also be in the range.
  exact h_initial val_i ⟨witness_i, h_rank_eq⟩ n h_n_lt_i

/-- `kraftRank` is injective (distinct elements have distinct ranks). -/
lemma kraftRank_injective {I : Type _} (l : I → ℕ) (e : I ↪ ℕ)
    (h_finite : ∀ k, {i | l i = k}.Finite) :
    Function.Injective (kraftRank l e h_finite) := by
  intro i j hij
  rcases (KraftOrder_isStrictTotalOrder l e).trichotomous i j with h | rfl | h
  · exact absurd hij (ne_of_lt (kraftRank_lt_of_KraftOrder l e h_finite h))
  · rfl
  · exact absurd hij (ne_of_gt (kraftRank_lt_of_KraftOrder l e h_finite h))

/-- An infinite index type with summable Kraft sum can be reordered to make lengths monotone.

This reduces the infinite case to the monotone case by using `kraftRank` to enumerate
elements in increasing order of length. -/
lemma exists_equiv_nat_monotone_of_infinite {I : Type _} [Infinite I] (l : I → ℕ)
    (h_summable : Summable (fun i => (1 / 2 : ℝ) ^ l i)) :
    ∃ e : ℕ ≃ I, Monotone (l ∘ e) := by
      have h_countable : Countable I := by
        have := h_summable.countable_support
        simp_all [ Function.support ]
        exact Set.countable_univ_iff.mp this
      -- Let `e = Encodable.encode`.
      obtain ⟨e, he⟩ : ∃ e : I ↪ ℕ, True := by
        simp
        exact countable_iff_nonempty_embedding.mp h_countable
      have h_finite : ∀ k, {i : I | l i = k}.Finite := by
        intro k
        refine' Set.Finite.subset ( h_summable.tendsto_cofinite_zero.eventually ( gt_mem_nhds <| show 0 < ( 1 / 2 : ℝ ) ^ k by positivity ) ) _
        intros x hx
        simp_all only [one_div, inv_pow, Set.mem_setOf_eq, Set.mem_compl_iff, lt_self_iff_false, not_false_eq_true]
      -- By definition of `kraftRank`, we know that `kraftRank` is a bijection between `I` and `ℕ`.
      have h_bij : Function.Bijective (kraftRank l e h_finite) := by
        exact ⟨ kraftRank_injective l e h_finite, kraftRank_surjective l e h_finite ⟩
      obtain ⟨e_iso, he_iso⟩ : ∃ e_iso : ℕ ≃ I, ∀ n, kraftRank l e h_finite (e_iso n) = n := by
        exact ⟨ Equiv.symm ( Equiv.ofBijective _ h_bij ), fun n => Equiv.apply_symm_apply ( Equiv.ofBijective _ h_bij ) n ⟩
      refine ⟨e_iso, fun n m hnm => ?_⟩
      contrapose! hnm
      have := kraftRank_lt_of_KraftOrder l e h_finite (KraftOrder_iff.mpr (Or.inl hnm))
      simp_all

/-- Extends a length function on `Fin k` to all of `ℕ`, preserving monotonicity.

For `i < k`, returns `l i`. For `i ≥ k`, returns `l(k-1) + (i - k + 1)`. -/
def l_ext {k : ℕ} (l : Fin k → ℕ) (hk : k ≠ 0) (i : ℕ) : ℕ :=
  if h : i < k then l ⟨i, h⟩ else l ⟨k - 1, by omega⟩ + (i - k + 1)

/-- `l_ext` agrees with `l` on `Fin k`. -/
lemma l_ext_eq {k : ℕ} (l : Fin k → ℕ) (hk : k ≠ 0) (i : Fin k) :
    l_ext l hk i = l i := by
      unfold Kraft.l_ext
      simp_all only [Fin.is_lt, ↓reduceDIte, Fin.eta]

/-- `l_ext` is monotone when `l` is monotone. -/
lemma l_ext_monotone {k : ℕ} (l : Fin k → ℕ) (h_mono : Monotone l) (hk : k ≠ 0) :
    Monotone (l_ext l hk) := by
      -- Let's prove the monotonicity of `l_ext` by considering different cases.
      intro i j hij
      simp [Kraft.l_ext] at *
      split_ifs <;> try omega
      · exact h_mono hij
      · exact le_add_of_le_of_nonneg ( h_mono ( Nat.le_pred_of_lt ‹_› ) ) ( Nat.zero_le _ )

/-- Converse of Kraft's inequality for monotone length sequences on `Fin k`.

Uses `kraft_A` to assign addresses that correspond to non-overlapping dyadic intervals. -/
lemma kraft_inequality_tight_finite_mono {k : ℕ} (l : Fin k → ℕ) (h_mono : Monotone l)
    (h_sum : ∑ i, (1 / 2 : ℝ) ^ l i ≤ 1) :
    ∃ w : Fin k → List Bool,
      Function.Injective w ∧
      Kraft.PrefixFree (Set.range w) ∧
      ∀ i, (w i).length = l i := by
        -- For `i ≥ k`, `kraft_A L i / 2^{L i} = \sum_{j=0}^{i-1} 2^{-L j} = (\sum_{j=0}^{k-1} 2^{-L j}) + \sum_{j=k}^{i-1} 2^{-L j}`.
        have k_nonempty: ∀ (i : Fin k), k ≠ 0 := fun i => (Fin.pos i).ne'
        have h_split_sum : ∀ i : Fin k, kraft_A (l_ext l (by linarith [ Fin.is_lt i ])) i < 2 ^ (l i) := by
          intro i
          let l' := l_ext l (k_nonempty i)
          have h_split_sum : kraft_A l' i / (2 : ℝ) ^ l' i
                           = ∑ j ∈ Finset.range i, (1 / 2 : ℝ) ^ l' j := by
            convert kraft_A_div_pow_eq_sum _ ( l_ext_monotone l h_mono _ ) i using 1
          have h_split_sum_lt : ∑ j ∈ Finset.range i, (1 / 2 : ℝ) ^ l' j < 1 := by
            have h_split_sum_le : ∑ j ∈ Finset.range k, (1 / 2 : ℝ) ^ l' j ≤ 1 := by
              rw [ Finset.sum_range ]
              unfold l' Kraft.l_ext
              simp_all only [one_div, inv_pow, Fin.is_lt, ↓reduceDIte, Fin.eta]
            refine' lt_of_lt_of_le ( _ ) h_split_sum_le
            rw [ ← Finset.sum_range_add_sum_Ico _ ( show ( i : ℕ ) ≤ k from i.2.le ) ]
            exact lt_add_of_pos_right _ ( Finset.sum_pos ( fun _ _ => by positivity ) ( by
              simp_all only [one_div, inv_pow, Finset.nonempty_Ico, Fin.is_lt]
            ) )
          rw [ div_eq_iff ] at h_split_sum  <;> norm_num at *
          exact_mod_cast ( by nlinarith [ pow_pos ( zero_lt_two' ℝ ) ( l i ), show ( 2 : ℝ ) ^ Kraft.l_ext l _ i = 2 ^ l i from by rw [l_ext_eq l (Fin.pos i).ne' i] ] : ( Kraft.kraft_A ( Kraft.l_ext l _) i : ℝ ) < 2 ^ l i )
        refine' ⟨ _, _, _, _ ⟩
        · intro i
          have k_nzero : k ≠ 0 := k_nonempty i
          use natToBits ( Kraft.kraft_A ( l_ext l ( by tauto ) ) i ) ( l i )
        · intro i j hij
          let l' := l_ext l (k_nonempty i)
          -- Since `natToBits` is injective, we have `kraft_A L i = kraft_A L j`.
          have h_kraft_A_eq : Kraft.kraft_A l' i = Kraft.kraft_A l' j := by
            apply natToBits_inj <;> unfold Kraft.natToBits at *
            · exact h_split_sum i
            · unfold l'
              replace hij := congr_arg List.length hij
              simp_all [ ]
            · unfold l'
              convert hij using 1
              replace hij := congr_arg List.length hij
              simp_all [ ]
          -- Since `kraft_A` is strictly monotone, we have `i = j`.
          have h_kraft_A_mono : StrictMono (Kraft.kraft_A l') := by
            refine' strictMono_nat_of_lt_succ _
            intro n
            apply Nat.lt_of_lt_of_le
            · exact Nat.lt_add_one _
            · apply Nat.le_mul_of_pos_right
              exact pow_pos (by decide) _
          exact Fin.ext <| h_kraft_A_mono.injective h_kraft_A_eq
        · intro x hx y hy hxy
          obtain ⟨ i, rfl ⟩ := hx
          obtain ⟨ j, rfl ⟩ := hy
          let l' := l_ext l (k_nonempty i)
          simp_all [ natToBits_prefix_iff ]
          -- If `i < j`, then `S_j \ge S_i + 2^{-l i}`, contradiction.
          by_cases hij : i < j
          · have h_contradiction : (Kraft.kraft_A l' j : ℝ) / 2 ^ (l j)
                                 ≥ (Kraft.kraft_A l' i : ℝ) / 2 ^ (l i) + (1 / 2 : ℝ) ^ (l i) := by
              have h_contradiction : (Kraft.kraft_A l' j : ℝ) / 2 ^ (l j)
                                    = (∑ k ∈ Finset.range j, (1 / 2 : ℝ) ^ l' k)
                                    ∧ (Kraft.kraft_A l' i : ℝ) / 2 ^ (l i)
                                    = (∑ k ∈ Finset.range i, (1 / 2 : ℝ) ^ l' k) := by
                apply And.intro
                · convert kraft_A_div_pow_eq_sum _ ( l_ext_monotone l h_mono ( by tauto ) ) j using 1
                  simp_all only [l', l_ext, Fin.is_lt, ↓reduceDIte, Fin.eta]
                · convert kraft_A_div_pow_eq_sum _ _ _ using 1
                  · simp_all only [l', l_ext, Fin.is_lt, ↓reduceDIte, Fin.eta]
                  · exact l_ext_monotone l h_mono ( by tauto )
              rw [ h_contradiction.1, h_contradiction.2, ← Finset.sum_range_add_sum_Ico _ ( show ( i : ℕ ) ≤ j from Nat.le_of_lt hij ) ]
              set A := ∑ k_1 ∈ Finset.range (↑i), (1 / 2 : ℝ) ^ l'  k_1
              set B := ∑ k_1 ∈ Finset.Ico (↑i) (↑j), (1 / 2 : ℝ) ^ l'  k_1
              set C := (1 / 2 : ℝ) ^ l i
              have hiIco : (↑i) ∈ Finset.Ico (↑i) (↑j) := by
                exact Finset.left_mem_Ico.2 (show (↑i) < (↑j) from hij)
              have hC_le_B :
                  (1 / 2 : ℝ) ^ l i ≤
                    ∑ k_1 ∈ Finset.Ico (↑i) (↑j), (1 / 2 : ℝ) ^ l' k_1 := by
                -- single term ≤ sum over Ico
                have h :=
                  (Finset.single_le_sum (s := Finset.Ico (↑i) (↑j))
                    (f := fun k_1 => (1 / 2 : ℝ) ^ l' k_1)
                    (by intro _ _; positivity)
                    (by exact Finset.left_mem_Ico.mpr hij))
                -- h : (1/2)^(l_ext ... ↑i) ≤ ∑ ...
                -- rewrite l_ext at ↑i using ↑i < k (since i : Fin k)
                simpa [l', l_ext, (show (↑i) < k from i.is_lt)] using h
              have h_add : A + (1 / 2 : ℝ) ^ l i ≤ A + B :=
                add_le_add_right (α := ℝ) (a := A) hC_le_B
              simp_all
              unfold C
              simp
              assumption
            contrapose! h_contradiction
            rw [ div_add', div_lt_div_iff₀ ] <;> norm_cast <;> norm_num
            norm_num [ ← mul_pow ]
            norm_cast
            convert mul_lt_mul_of_pos_right hxy.2.2 ( pow_pos ( zero_lt_two' ℕ ) ( l i ) ) using 1
            rw [ show l j = l i + ( l j - l i ) by rw [ Nat.add_sub_of_le hxy.1 ] ]
            unfold l'
            ring_nf
            norm_num
          · cases lt_or_eq_of_le ( le_of_not_gt hij ) <;> simp_all [Fin.ext_iff]
            · -- Since `j < i`, we have `l j < l i`.
              have h_lt : l j < l i := by
                refine' lt_of_le_of_ne ( h_mono hij ) _
                intro h
                simp_all
                -- Since `l` is monotone, `kraft_A` is strictly increasing.
                have h_kraft_A_mono : StrictMono (Kraft.kraft_A l') := by
                  refine' strictMono_nat_of_lt_succ _
                  intro n
                  exact Nat.lt_of_lt_of_le ( Nat.lt_succ_self _ ) ( Nat.le_mul_of_pos_right _ ( pow_pos ( by decide ) _ ) )
                linarith [ h_kraft_A_mono ( show ( j : ℕ ) < i from by assumption ) ]
              linarith
            · -- 1. Convert the value equality (↑j = ↑i) to index equality (j = i)
              have heq : j = i := Fin.ext (by assumption)
              -- 2. Substitute j with i everywhere
              subst heq
              -- 3. The goal is now X = X
              rfl
        · unfold Kraft.natToBits
          intro i
          simp_all only [one_div, inv_pow, List.length_ofFn]

/-- Any finite type can be sorted by a function to ℕ.

Given a fintype `I` and a function `l : I → ℕ`, produces an equivalence
`e : Fin (card I) ≃ I` such that `l ∘ e` is monotone (i.e., maps increasing
indices to non-decreasing length values). Uses insertion sort internally. -/
lemma exists_equiv_fin_monotone {I : Type _} [Fintype I] (l : I → ℕ) :
    ∃ e : Fin (Fintype.card I) ≃ I, Monotone (l ∘ e) := by
      have h_order_iso : ∃ (e : Fin (Fintype.card I) ≃ I), ∀ i j, i ≤ j → l (e i) ≤ l (e j) := by
        -- By definition of `Finset.sort`, we can obtain a sorted list of elements from `I` based on `l`.
        obtain ⟨sorted_list, h_sorted⟩ : ∃ sorted_list : List I, List.Pairwise (fun x y => l x ≤ l y) sorted_list ∧ List.length sorted_list = Fintype.card I ∧ List.Nodup sorted_list ∧ ∀ x ∈ sorted_list, x ∈ Finset.univ := by
          have h_insertion_sort : ∀ {xs : List I}, List.Nodup xs → ∃ sorted_list : List I, List.Pairwise (fun x y => l x ≤ l y) sorted_list ∧ List.length sorted_list = List.length xs ∧ List.Nodup sorted_list ∧ ∀ x ∈ sorted_list, x ∈ xs := by
            have h_insertion_sort : ∀ {xs : List I}, List.Nodup xs → ∃ sorted_list : List I, List.Pairwise (fun x y => l x ≤ l y) sorted_list ∧ List.length sorted_list = List.length xs ∧ List.Nodup sorted_list ∧ ∀ x ∈ sorted_list, x ∈ xs := by
              intro xs h_nodup
              exact ⟨List.insertionSort (fun x y => l x ≤ l y) xs, by
                convert List.pairwise_insertionSort _ _
                · exact ⟨ fun x y => le_total _ _ ⟩
                · exact ⟨ fun x y z hxy hyz => le_trans hxy hyz ⟩, by
                exact List.length_insertionSort (fun x y ↦ l x ≤ l y) xs, by
                exact List.Perm.nodup_iff ( List.perm_insertionSort _ _ ) |>.2 h_nodup, by
                exact fun x hx => List.mem_insertionSort ( fun x y => l x ≤ l y ) |>.1 hx⟩
            assumption
          simpa using h_insertion_sort ( Finset.nodup_toList Finset.univ )
        have h_equiv : ∃ e : Fin (Fintype.card I) ≃ I, ∀ i, e i = sorted_list[i] := by
          have h_equiv : Function.Bijective (fun i : Fin (Fintype.card I) => sorted_list[i]) := by
            have h_equiv : Function.Injective (fun i : Fin (Fintype.card I) => sorted_list[i]) := by
              intro i j hij
              have := List.nodup_iff_injective_get.mp h_sorted.2.2.1
              exact Fin.ext <| by simpa [ h_sorted.2.1 ] using this hij
            have := Fintype.bijective_iff_injective_and_card ( fun i : Fin ( Fintype.card I ) => sorted_list[i] )
            simp_all only [Fin.getElem_fin, Multiset.bijective_iff_map_univ_eq_univ, Fin.univ_val_map, Fintype.card_fin, and_self, iff_true]
          exact ⟨ Equiv.ofBijective _ h_equiv, fun i => rfl ⟩
        obtain ⟨ e, he ⟩ := h_equiv
        refine' ⟨ e, fun i j hij => _ ⟩
        have := List.pairwise_iff_get.mp h_sorted.1
        cases lt_or_eq_of_le hij <;> simp_all [ Fin.ext_iff ]
        exact this ⟨ i, by linarith [ Fin.is_lt i, Fin.is_lt j ] ⟩ ⟨ j, by linarith [ Fin.is_lt i, Fin.is_lt j ] ⟩ ‹_›
      exact ⟨ h_order_iso.choose, fun i j hij => h_order_iso.choose_spec i j hij ⟩

/-- **Converse of Kraft's Inequality** (infinite case).

For any index set `I` (finite or infinite) and length function `l : I → ℕ`,
if `∑' i, 2^{-l(i)} ≤ 1`, then there exists an injective prefix-free code
`w : I → List Bool` with the prescribed lengths.

The proof handles two cases:
- **Finite case**: Sort indices by length and apply `kraft_inequality_tight_finite_mono`
- **Infinite case**: Use equivalence with ℕ and apply `kraft_inequality_tight_nat_mono` -/
theorem kraft_inequality_tight_infinite {I : Type _} (l : I → ℕ)
    (h_summable : Summable (fun i ↦ (1 / 2 : ℝ) ^ l i))
    (h_sum : ∑' i, (1 / 2 : ℝ) ^ l i ≤ 1) :
    ∃ w : I → List Bool,
      Function.Injective w ∧
      PrefixFree (Set.range w) ∧
      ∀ i, (w i).length = l i := by
  by_cases h_finite : Finite I
  · haveI := Fintype.ofFinite I
    -- By `exists_equiv_fin_monotone`, there exists an equivalence `e : Fin (card I) ≃ I` such that `l ∘ e` is monotone.
    obtain ⟨e, he⟩ : ∃ e : Fin (Fintype.card I) ≃ I, Monotone (l ∘ e) := by
      exact exists_equiv_fin_monotone l
    -- By `kraft_inequality_tight_finite_mono`, there exists `w' : Fin (card I) → List Bool` satisfying the conditions for `l ∘ e`.
    obtain ⟨w', hw'⟩ : ∃ w' : Fin (Fintype.card I) → List Bool, Function.Injective w' ∧ Kraft.PrefixFree (Set.range w') ∧ ∀ i, (w' i).length = l (e i) := by
      have h_sum_eq : ∑ i, (1 / 2 : ℝ) ^ (l (e i)) ≤ 1 := by
        convert h_sum using 1
        rw [ tsum_fintype, ← Equiv.sum_comp e ]
      exact kraft_inequality_tight_finite_mono (fun i ↦ l (e i)) he h_sum_eq
    refine' ⟨ w' ∘ e.symm, _, _, _ ⟩ <;> simp_all [Function.Injective]
    exact fun a₁ a₂ h => e.symm.injective ( hw'.1 h )
  · have h_equiv : ∃ e : ℕ ≃ I, Monotone (l ∘ e) := by
      convert exists_equiv_nat_monotone_of_infinite l h_summable using 1
      simpa using h_finite
    obtain ⟨ e, he ⟩ := h_equiv
    have h_exists_w : ∃ w : ℕ → List Bool, Function.Injective w ∧ Kraft.PrefixFree (Set.range w) ∧ ∀ i, (w i).length = l (e i) := by
      have h_exists_w_1 : ∑' i : ℕ, (1 / 2 : ℝ) ^ l (e i) ≤ 1 := by
        convert h_sum using 1
        conv_rhs => rw [ ← Equiv.tsum_eq e ]
      have h_exists_w : Summable (fun i : ℕ => (1 / 2 : ℝ) ^ l (e i)) := by
        convert h_summable.comp_injective e.injective using 1
      exact kraft_inequality_tight_nat_mono (fun i ↦ l (e i)) he h_exists_w h_exists_w_1
    obtain ⟨ w, hw₁, hw₂, hw₃ ⟩ := h_exists_w
    refine' ⟨ fun i => w ( e.symm i ), _, _, _ ⟩
    · exact hw₁.comp e.symm.injective
    · intro x hx y hy hxy
      simp_all only [one_div, inv_pow, not_finite_iff_infinite, Set.mem_range]
      obtain ⟨w_1, h⟩ := hx
      obtain ⟨w_2, h_1⟩ := hy
      subst h h_1
      apply hw₂
      · simp_all only [Set.mem_range, exists_apply_eq_apply]
      · simp_all only [Set.mem_range, exists_apply_eq_apply]
      · simp_all only
    · intro i
      simp_all only [one_div, inv_pow, not_finite_iff_infinite, Equiv.apply_symm_apply]

end Kraft
