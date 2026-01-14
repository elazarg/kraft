import Mathlib.Data.Finite.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Hom.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Tactic.Linarith

namespace Kraft

open scoped BigOperators Real

section Numerator
/-- Generalized interval start function for constructing prefix-free codes over alphabet of size D.

For a monotone length sequence `l`, `kraft_numerator D l n` is chosen so that
`kraft_numerator D l n / D^{l n}` equals the partial Kraft sum `Σ_{k<n} D^{-l k}`. -/
def kraft_numerator (D : ℕ) (l : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => (kraft_numerator D l n + 1) * D ^ (l (n + 1) - l n)

/-- `kraft_numerator D l n / D^{l n}` equals the partial Kraft sum `Σ_{k<n} (1/D)^{l k}`.

This is the key invariant that ensures non-overlapping D-adic intervals. -/
lemma kraft_numerator_div_pow_eq_sum (D : ℕ) (hD : 1 < D) (l : ℕ → ℕ) (h_mono : Monotone l) (n : ℕ) :
    (kraft_numerator D l n : ℝ) / D ^ l n = ∑ k ∈ Finset.range n, (1 / D : ℝ) ^ l k := by
  have hD_pos : (0 : ℝ) < D := by exact_mod_cast Nat.zero_lt_of_lt hD
  have hD_ne : (D : ℝ) ≠ 0 := ne_of_gt hD_pos
  induction n with
  | zero => simp only [kraft_numerator, CharP.cast_eq_zero, zero_div, Finset.range_zero, Finset.sum_empty]
  | succ n ih =>
    simp only [one_div, inv_pow, Finset.sum_range_succ]
    have h_sub : (kraft_numerator D l (n + 1) : ℝ) = (kraft_numerator D l n + 1) * D ^ (l (n + 1) - l n) := by
      simp only [kraft_numerator, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow]
    rw [h_sub]
    simp_all only [one_div, inv_pow]
    rw [← ih]
    rw [show l (n + 1) = l n + (l (n + 1) - l n) by rw [Nat.add_sub_of_le (h_mono (Nat.le_succ n))]]
    rw [pow_add]
    field_simp
    simp only [add_tsub_cancel_left]

/-- Closed form for `kraft_numerator` as a Nat sum of scaled powers. -/
lemma kraft_numerator_eq_sum_pow_range
    (D : ℕ) (l : ℕ → ℕ) (hmono : Monotone l) :
    ∀ n, kraft_numerator D l n = ∑ t ∈ Finset.range n, D ^ (l n - l t) := by
  intro n
  induction n with
  | zero =>
      simp [kraft_numerator]
  | succ n ih =>
      -- Notation
      have hln : l n ≤ l (n+1) := hmono (Nat.le_succ n)
      set a : ℕ := l (n+1) - l n

      -- Start from the RHS for `n+1`
      -- split off last term, then factor out `D^a` from the prefix sum
      simp [Finset.sum_range_succ, kraft_numerator, ih]

      -- Goal after simp is essentially:
      --   (∑ t∈range n, D^(l(n+1)-l t)) + D^(l(n+1)-l n)
      -- = ( (∑ t∈range n, D^(l n - l t)) + 1 ) * D^(l(n+1)-l n)

      -- Turn the prefix sum into a factored form
      have hfac :
          (∑ t ∈ Finset.range n, D ^ (l (n+1) - l t))
            = D ^ a * (∑ t ∈ Finset.range n, D ^ (l n - l t)) := by
        -- rewrite each term using exponent arithmetic:
        -- (l(n+1)-l t) = (l(n+1)-l n) + (l n - l t)
        -- then use `pow_add` and pull out `D^a`
        calc
          (∑ t ∈ Finset.range n, D ^ (l (n+1) - l t))
              = ∑ t ∈ Finset.range n, (D ^ a) * (D ^ (l n - l t)) := by
                  refine Finset.sum_congr rfl ?_
                  intro t ht
                  have ht' : t < n := Finset.mem_range.mp ht
                  have hlt : l t ≤ l n := hmono (Nat.le_of_lt_succ (Nat.lt_succ_of_lt ht'))
                  have hlt' : l t ≤ l (n+1) := le_trans hlt hln
                  -- exponent identity
                  have hexp : (l (n+1) - l t) = a + (l n - l t) := by
                    -- `a = l(n+1)-l n`
                    dsimp [a]
                    omega
                  -- finish
                  simp [hexp, pow_add, mul_comm]
          _   = D ^ a * (∑ t ∈ Finset.range n, D ^ (l n - l t)) := by
                  -- pull out constant
                  simp [Finset.mul_sum]

      -- Now finish the `succ` step by rewriting with `hfac`
      -- and using `l(n+1)-l n = a`
      -- also: the last term is exactly `D^a`
      have hlast : D ^ (l (n+1) - l n) = D ^ a := by simp [a]
      -- substitute and algebra
      simp [hfac, hlast, Nat.mul_add, Nat.mul_comm]

/--
Separation property for `A = kraft_numerator D l`:
if `i < j` then you cannot have `A j / D^(l j - l i) = A i` (even assuming `l i ≤ l j`).
-/
lemma kraft_numerator_div_separated_of_lt
    {D : ℕ} {l : ℕ → ℕ} (hD : 1 < D)
    (hmono : Monotone l) :
    ∀ {i j : ℕ}, i < j →
      ¬ (l i ≤ l j ∧ kraft_numerator D l j / D ^ (l j - l i) = kraft_numerator D l i) := by
  intro i j hij
  rintro ⟨hij_len, hdiv⟩

  have hDpos : 0 < D := Nat.zero_lt_of_lt hD
  set A : ℕ → ℕ := kraft_numerator D l
  set d : ℕ := D ^ (l j - l i)
  have hdpos : 0 < d := by
    dsimp [d]
    exact Nat.pow_pos hDpos

  -- Closed forms for A i and A j
  have hAi : A i = ∑ t ∈  Finset.range i, D ^ (l i - l t) := by
    simpa [A] using (kraft_numerator_eq_sum_pow_range D l hmono i)
  have hAj : A j = ∑ t ∈ Finset.range j, D ^ (l j - l t) := by
    simpa [A] using (kraft_numerator_eq_sum_pow_range D l hmono j)

  -- The partial sum up to `i+1` sits inside the sum up to `j`
  have hsub : Finset.range (i+1) ⊆ Finset.range j := by
    -- i+1 ≤ j since i< j
    exact Finset.range_mono (Nat.succ_le_of_lt hij)

  have hle_part :
      (∑ t ∈  Finset.range (i+1), D ^ (l j - l t))
        ≤ (∑ t ∈  Finset.range j, D ^ (l j - l t)) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
    intro x hx _hx'
    exact Nat.zero_le _

  have hle_part' :
      (∑ t ∈  Finset.range (i+1), D ^ (l j - l t)) ≤ A j := by
    simpa [hAj] using hle_part

  -- Rewrite the `range (i+1)` sum as (range i) + last
  have hsplit :
      (∑ t ∈  Finset.range (i+1), D ^ (l j - l t))
        = (∑ t ∈  Finset.range i, D ^ (l j - l t)) + D ^ (l j - l i) := by
    simp [Finset.sum_range_succ]

  -- Show the prefix sum is a multiple of `d` with coefficient `A i`
  have hmul_prefix :
      (∑ t ∈  Finset.range i, D ^ (l j - l t))
        = d * (∑ t ∈  Finset.range i, D ^ (l i - l t)) := by
    -- each term: D^(l j - l t) = D^(l j - l i) * D^(l i - l t)
    -- because l t ≤ l i ≤ l j
    calc
      (∑ t ∈  Finset.range i, D ^ (l j - l t))
          = ∑ t ∈  Finset.range i, d * (D ^ (l i - l t)) := by
              refine Finset.sum_congr rfl ?_
              intro t ht
              have ht' : t < i := Finset.mem_range.mp ht
              have hti : l t ≤ l i := hmono (Nat.le_of_lt ht')
              have htj : l t ≤ l j := le_trans hti hij_len
              have hexp : (l j - l t) = (l j - l i) + (l i - l t) := by
                -- needs l t ≤ l i ≤ l j
                omega
              -- unfold d and finish
              simp [d, hexp, pow_add, mul_comm]
      _   = d * (∑ t ∈  Finset.range i, D ^ (l i - l t)) := by
              simp [Finset.mul_sum]

  -- Now assemble: sum_{t≤i} = d*(A i + 1)
  have hlower :
      d * (A i + 1) ≤ A j := by
    -- start from hle_part' and rewrite LHS
    -- LHS = (prefix over range i) + d
    -- prefix = d * (sum range i ...)
    -- sum range i ... = A i
    have : (∑ t ∈  Finset.range (i+1), D ^ (l j - l t))
              = d * (A i + 1) := by
      -- rewrite using hsplit, hmul_prefix, hAi
      calc
        (∑ t ∈  Finset.range (i+1), D ^ (l j - l t))
            = (∑ t ∈  Finset.range i, D ^ (l j - l t)) + D ^ (l j - l i) := by
                exact hsplit
        _   = d * (∑ t ∈ Finset.range i, D ^ (l i - l t)) + d := by
                simp [hmul_prefix, d]
        _   = d * (A i) + d := by
                simp [hAi]
        _   = d * (A i + 1) := by
                simp [Nat.mul_add]
    -- apply ≤ using hle_part'
    simpa [this] using hle_part'
  rw [mul_comm] at hlower
  -- Divide both sides by `d`: (A i + 1) ≤ A j / d
  have hquot_ge : A i + 1 ≤ A j / d := by
    exact (Nat.le_div_iff_mul_le hdpos).2 hlower

  -- But we assumed A j / d = A i
  have : A i + 1 ≤ A i := by simp [hdiv, A, d] at hquot_ge
  exact Nat.not_succ_le_self _ this

/-- Helper: turn the invariant + `< 1` into the numeric bound `A n < D^(lNat n)`. -/
lemma kraft_numerator_lt_pow_of_sum_range_lt_one
    (D : ℕ) (hD : 1 < D) (lNat : ℕ → ℕ) (hmono : Monotone lNat)
    {n : ℕ}
    (h_sum_lt1 : (∑ t ∈ Finset.range n, (1 / D : ℝ) ^ lNat t) < 1) :
    kraft_numerator D lNat n < D ^ lNat n := by
  have hD_pos : 0 < D := Nat.zero_lt_of_lt hD
  have hD_pos_real : (0 : ℝ) < D := by exact_mod_cast hD_pos
  have hD_ne : (D : ℝ) ≠ 0 := ne_of_gt hD_pos_real

  have h_eq :
      (kraft_numerator D lNat n : ℝ) / (D : ℝ) ^ lNat n
        = ∑ t ∈ Finset.range n, (1 / D : ℝ) ^ lNat t :=
    kraft_numerator_div_pow_eq_sum (D := D) hD lNat hmono n

  have hden : 0 < (D : ℝ) ^ lNat n := by positivity
  have hdivlt : (kraft_numerator D lNat n : ℝ) / (D : ℝ) ^ lNat n < 1 := by
    simpa [h_eq] using h_sum_lt1

  have hlt_real : (kraft_numerator D lNat n : ℝ) < (D : ℝ) ^ lNat n := by
    -- `a/b < 1` with `0<b` gives `a < b`
    exact (div_lt_one hden).1 hdivlt

  -- cast back to `ℕ`
  exact_mod_cast hlt_real

lemma range_eq_Iio (n : ℕ) : (Finset.range n : Finset ℕ) = Finset.Iio n := by
  ext k
  simp [Finset.mem_Iio]  -- gives: k ∈ Iio n ↔ k < n, same as mem_range

lemma kraft_numerator_bound {D : ℕ} {l : ℕ → ℕ} (h_mono : Monotone l) (hD : 1 < D)
  (h_prefix_lt_one : ∀ n, (∑ k < n, (1 / D : ℝ) ^ l k) < 1) :
    ∀ n, kraft_numerator D l n < D ^ l n := by
  intro n
  have h_range : (∑ k ∈ Finset.range n, (1 / (D : ℝ)) ^ l k) < 1 := by
    simpa [range_eq_Iio] using h_prefix_lt_one n
  exact kraft_numerator_lt_pow_of_sum_range_lt_one _ hD _ h_mono h_range

/-- `kraft_numerator D l` is strictly increasing as soon as `D > 0`.

In particular it is `StrictMono` under the standing assumption `1 < D`. -/
lemma strictMono_kraft_numerator {D : ℕ} {l : ℕ → ℕ} (hD : 1 < D) :
    StrictMono (kraft_numerator D l) := by
  -- it suffices to show `A n < A (n+1)` for all `n`
  refine strictMono_nat_of_lt_succ (fun n => ?_)
  -- unfold the successor clause
  simp [kraft_numerator]
  -- let `p = D^(...)`, which is positive since `D>0`
  have hDpos : 0 < D := Nat.zero_lt_of_lt hD
  have hp : 0 < D ^ (l (n + 1) - l n) := Nat.pow_pos hDpos
  -- `A n < A n + 1 ≤ (A n + 1) * p`
  exact lt_of_lt_of_le (Nat.lt_add_one _) (Nat.le_mul_of_pos_right _ hp)

end Numerator

section KraftOrder
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
    · intro _ _
      apply h_finite
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
    · exact absurd hij (Nat.ne_of_lt (kraftRank_lt_of_KraftOrder l e h_finite h))
    · rfl
    · exact absurd hij (Nat.ne_of_gt (kraftRank_lt_of_KraftOrder l e h_finite h))
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
        simp_all only [kraftRank, le_refl]
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
  · exact absurd hij (Nat.ne_of_lt (kraftRank_lt_of_KraftOrder l e h_finite h))
  · rfl
  · exact absurd hij (Nat.ne_of_gt (kraftRank_lt_of_KraftOrder l e h_finite h))

/-- An infinite index type with summable Kraft sum can be reordered to make lengths monotone.

This reduces the infinite case to the monotone case by using `kraftRank` to enumerate
elements in increasing order of length.

Generalized to any base D > 1. -/
lemma exists_equiv_nat_monotone_of_infinite {I : Type _} [Infinite I] (D : ℕ) (hD : 1 < D) (l : I → ℕ)
    (h_summable : Summable (fun i => (1 / D : ℝ) ^ l i)) :
    ∃ e : ℕ ≃ I, Monotone (l ∘ e) := by
      have hD_pos : 0 < D := Nat.zero_lt_of_lt hD
      have h_countable : Countable I := by
        have := h_summable.countable_support
        simp only [one_div, Function.support, ne_eq, inv_eq_zero, pow_eq_zero_iff',
                   Nat.cast_eq_zero, Nat.pos_iff_ne_zero.mp hD_pos, false_and, not_false_eq_true] at this
        exact Set.countable_univ_iff.mp this
      -- Let `e = Encodable.encode`.
      obtain ⟨e, he⟩ : ∃ e : I ↪ ℕ, True := by
        simp
        exact countable_iff_nonempty_embedding.mp h_countable
      have h_finite : ∀ k, {i : I | l i = k}.Finite := by
        intro k
        -- f i := (1/D)^l i tends to 0 along cofinite, so eventually f i < (1/D)^k
        have hEv : ∀ᶠ i in Filter.cofinite, (1 / D : ℝ) ^ l i < (1 / D : ℝ) ^ k := by
          have hT := h_summable.tendsto_cofinite_zero
          have hnhds : Set.Iio ((1 / D : ℝ) ^ k) ∈ nhds (0 : ℝ) := by
            exact Iio_mem_nhds (by positivity)
          exact hT.eventually hnhds

        -- hence the “bad set” where ¬(f i < (1/D)^k) is finite
        have hbad :
            {i : I | ¬ ((1 / D : ℝ) ^ l i < (1 / D : ℝ) ^ k)}.Finite := by
          -- depending on imports, this is either `.1` or `mp`
          exact (Filter.eventually_cofinite.1 hEv)

        -- and {i | l i = k} ⊆ bad-set, because it would be ¬(a < a)
        refine hbad.subset ?_
        intro x hx
        -- goal: ¬ ((1/D)^l x < (1/D)^k)
        -- rewrite hx : l x = k, then use lt_irrefl
        simp_all only [not_lt, Set.mem_setOf_eq, le_refl]

      -- By definition of `kraftRank`, we know that `kraftRank` is a bijection between `I` and `ℕ`.
      have h_bij : Function.Bijective (kraftRank l e h_finite) := by
        exact ⟨ kraftRank_injective l e h_finite, kraftRank_surjective l e h_finite ⟩
      obtain ⟨e_iso, he_iso⟩ : ∃ e_iso : ℕ ≃ I, ∀ n, kraftRank l e h_finite (e_iso n) = n := by
        exact ⟨ Equiv.symm (Equiv.ofBijective _ h_bij), fun n => Equiv.apply_symm_apply (Equiv.ofBijective _ h_bij) n ⟩
      refine ⟨e_iso, fun n m hnm => ?_⟩
      contrapose! hnm
      have := kraftRank_lt_of_KraftOrder l e h_finite (KraftOrder_iff.mpr (Or.inl hnm))
      simp_all only

/-- Any finite type can be sorted by a function to ℕ.

Given a fintype `I` and a function `l : I → ℕ`, produces an equivalence
`e : Fin (card I) ≃ I` such that `l ∘ e` is monotone (i.e., maps increasing
indices to non-decreasing length values). Uses insertion sort internally. -/
lemma exists_equiv_fin_monotone {I : Type _} [Fintype I] (l : I → ℕ) :
    ∃ e : Fin (Fintype.card I) ≃ I, Monotone (l ∘ e) := by
  -- sort relation by length
  let r : I → I → Prop := fun x y => l x ≤ l y
  have r_total : IsTotal I r := ⟨fun x y => le_total _ _⟩
  have r_trans : IsTrans I r := ⟨fun _ _ _ => le_trans⟩

  -- start from the canonical list of all elements
  let xs : List I := (Finset.univ : Finset I).toList
  have xs_nodup : xs.Nodup := Finset.nodup_toList (Finset.univ : Finset I)
  have xs_len : xs.length = Fintype.card I := by simp [xs]

  -- insertionSort it
  let ys : List I := xs.insertionSort r
  have ys_pairwise : ys.Pairwise r := by
    -- `pairwise_insertionSort` needs total+trans packaged as instances
    convert (List.pairwise_insertionSort r xs)
  have ys_len : ys.length = Fintype.card I := by simp [ys, xs_len]
  have ys_nodup : ys.Nodup := by
    -- perm preserves nodup
    exact (List.Perm.nodup_iff (List.perm_insertionSort r (l := xs))).2 xs_nodup

  -- the "indexing function" into the sorted list
  let f : Fin ys.length → I := fun i => ys.get i
  have hf_inj : Function.Injective f := by
    -- nodup ↔ get is injective
    exact (List.nodup_iff_injective_get).1 ys_nodup

  -- injective + same finite card ⇒ bijective
  have hf_bij : Function.Bijective f := by
    refine (Fintype.bijective_iff_injective_and_card f).2 ?_
    refine ⟨hf_inj, ?_⟩
    -- card (Fin ys.length) = ys.length = card I
    simp [Fintype.card_fin, ys_len]

  let e0 : Fin ys.length ≃ I := Equiv.ofBijective f hf_bij
  -- cast domain from `Fin (card I)` to `Fin ys.length`
  have hcast : Fintype.card I = ys.length := by simp [ys_len]
  let cast : Fin (Fintype.card I) ≃ Fin ys.length := Fin.castOrderIso hcast

  let e : Fin (Fintype.card I) ≃ I := cast.trans e0
  refine ⟨e, ?_⟩

  -- monotone: i ≤ j ⇒ l(e i) ≤ l(e j)
  intro i j hij
  have hij' : (cast i) ≤ (cast j) := by simpa [cast] using hij
  rcases lt_or_eq_of_le hij' with hlt | heq
  · -- strict case: use pairwise_iff_get
    have hget :
        l (ys.get (cast i)) ≤ l (ys.get (cast j)) := by
      have hPW := List.pairwise_iff_get.1 ys_pairwise
      exact hPW (cast i) (cast j) hlt
    -- unfold e = cast.trans e0, and e0 is built from `f = get`
    simpa [e, cast, e0, Equiv.ofBijective, f] using hget
  · -- equal indices
    simp [e, heq]

/-- Helper: if a nonnegative series of length `k` sums to `≤ 1`,
then every proper prefix sum is `< 1`. -/
lemma sum_range_lt_one_of_sum_range_le_one
    {r : ℝ} (hr : 0 < r) {k n : ℕ} (hnk : n < k)
    (lNat : ℕ → ℕ)
    (h_le : (∑ t ∈ Finset.range k, r ^ lNat t) ≤ 1) :
    (∑ t ∈ Finset.range n, r ^ lNat t) < 1 := by
  -- `S(n) < S(n+1) ≤ S(k) ≤ 1`
  refine lt_of_lt_of_le ?_ h_le

  have hlt_succ : (∑ t ∈ Finset.range n, r ^ lNat t)
      < (∑ t ∈ Finset.range (n+1), r ^ lNat t) := by
    simp [Finset.sum_range_succ]
    have : 0 < r ^ lNat n := by
      exact pow_pos hr _
    linarith

  apply lt_of_lt_of_le hlt_succ

  refine le_trans ?_ le_rfl

  have hsub : Finset.range (n+1) ⊆ Finset.range k :=
    Finset.range_mono (Nat.succ_le_of_lt hnk)
  refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
  intro _ _ _
  exact le_of_lt (pow_pos hr _)

/--
The main consistency theorem for the Kraft construction.
If an infinite sequence of lengths satisfies Kraft's inequality (sum ≤ 1),
then the `kraft_numerator` construction stays strictly bounded by `D ^ l n`.
-/
lemma kraft_numerator_bound_of_tsum_le_one
    {D : ℕ} (hD : 1 < D)
    {l : ℕ → ℕ} (h_mono : Monotone l)
    (h_summable : Summable (fun n => (1 / D : ℝ) ^ l n))
    (h_sum_le_one : ∑' n, (1 / D : ℝ) ^ l n ≤ 1) :
    ∀ n, kraft_numerator D l n < D ^ l n := by
  -- This is exactly your snippet, adapted to call your existing bound lemma
  have h_pos : (0 : ℝ) < 1 / D := one_div_pos.mpr (by exact_mod_cast Nat.zero_lt_of_lt hD)

  apply kraft_numerator_bound h_mono hD
  intro n
  have h_le_tsum : ∑ k ∈ Finset.range (n + 1), (1 / D : ℝ) ^ l k ≤ ∑' k, (1 / D : ℝ) ^ l k :=
    Summable.sum_le_tsum _ (fun _ _ => by positivity) h_summable
  have h_prefix_le_one : ∑ k ∈ Finset.range (n + 1), (1 / D : ℝ) ^ l k ≤ 1 :=
    le_trans h_le_tsum h_sum_le_one
  -- Use your helper from the end of the file
  simpa [range_eq_Iio] using sum_range_lt_one_of_sum_range_le_one h_pos (Nat.lt_succ_self n) l h_prefix_le_one

end KraftOrder

end Kraft
