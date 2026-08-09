/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Northcott
public import Mathlib.Topology.Algebra.InfiniteSum.Defs

import Mathlib.Data.Fin.Tuple.Sort

/-!
# Reordering by a Finite-Fiber Function

Given a function `l : I → ℕ`, this file produces an equivalence `e` (from `ℕ` or
`Fin (card I)`, depending on whether `I` is infinite or finite) such that `l ∘ e` is monotone.
In the infinite case this is possible when every fiber of `l` is finite. A private
lexicographic order and rank implement the enumeration.

## Main results

* `exists_equiv_nat_monotone_of_finite_fibers`: Enumerates an infinite type monotonically for
  any `ℕ`-valued function with finite fibers.
* `exists_equiv_nat_monotone_of_northcott`: The same result in terms of mathlib's `Northcott`
  abstraction for functions with finite sublevel sets.
* `exists_equiv_nat_monotone_of_summable`: Uses summability of a Kraft series to show that the
  length fibers are finite, then applies the general enumeration theorem.
* `exists_equiv_fin_monotone`: Reorders a finite type to make lengths monotone, via `Tuple.sort`.
-/

@[expose] public section

namespace InformationTheory

/-- A strict total order on indices: first by length, then by an auxiliary embedding.

This is used to enumerate elements in an order that makes the length function monotone. -/
private def KraftOrder {I : Type*} (l : I → ℕ) (e : I ↪ ℕ) (i j : I) : Prop :=
  Prod.Lex (· < ·) (· < ·) (l i, e i) (l j, e j)

/-- `KraftOrder` is equivalent to: `l i < l j` or (`l i = l j` and `e i < e j`). -/
private lemma KraftOrder_iff {I : Type*} {l : I → ℕ} {e : I ↪ ℕ} {i j : I} :
    KraftOrder l e i j ↔ l i < l j ∨ (l i = l j ∧ e i < e j) :=
  Prod.lex_iff

/-- `KraftOrder` is a strict total order. -/
private lemma KraftOrder_isStrictTotalOrder {I : Type*} (l : I → ℕ) (e : I ↪ ℕ) :
    IsStrictTotalOrder I (KraftOrder l e) := by
  let f : I ↪ ℕ × ℕ :=
    ⟨fun i => (l i, e i), fun _ _ h => e.injective (congrArg Prod.snd h)⟩
  exact (show KraftOrder l e ↪r Prod.Lex (fun a b : ℕ => a < b) (fun a b : ℕ => a < b) from
    { toEmbedding := f
      map_rel_iff' := Iff.rfl }).isStrictTotalOrder

/-- Initial segments of `KraftOrder` are finite when length fibers are finite.

Since each length has only finitely many indices (by summability), the set of
indices smaller than any given index is finite. -/
private lemma KraftOrder_finite_initial_segment {I : Type*} (l : I → ℕ) (e : I ↪ ℕ)
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
private noncomputable def kraftRank {I : Type*} (l : I → ℕ) (e : I ↪ ℕ)
    (h_finite : ∀ k, {i | l i = k}.Finite) (i : I) : ℕ :=
  (KraftOrder_finite_initial_segment l e h_finite i).toFinset.card

/-- `kraftRank` is strictly monotone with respect to `KraftOrder`. -/
private lemma kraftRank_lt_of_KraftOrder {I : Type*} (l : I → ℕ) (e : I ↪ ℕ)
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
private lemma kraftRank_surjective {I : Type*} [Infinite I] (l : I → ℕ) (e : I ↪ ℕ)
    (h_finite : ∀ k, {i | l i = k}.Finite) :
    Function.Surjective (kraftRank l e h_finite) := by
  have hsto := KraftOrder_isStrictTotalOrder l e
  -- kraftRank is injective (distinct elements have distinct ranks)
  have h_inj : Function.Injective (kraftRank l e h_finite) := by
    intro i j hij
    rcases (hsto.toTrichotomous.rel_or_eq_or_rel_swap (a := i) (b := j)) with h | rfl | h
    · exact absurd hij (Nat.ne_of_lt (kraftRank_lt_of_KraftOrder l e h_finite h))
    · rfl
    · exact absurd hij (Nat.ne_of_gt (kraftRank_lt_of_KraftOrder l e h_finite h))
  -- The range is an initial segment: if n is in range, so is every m < n
  have h_initial :
      ∀ n, (∃ i, kraftRank l e h_finite i = n) → ∀ m < n, ∃ i, kraftRank l e h_finite i = m := by
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
private lemma kraftRank_injective {I : Type*} (l : I → ℕ) (e : I ↪ ℕ)
    (h_finite : ∀ k, {i | l i = k}.Finite) :
    Function.Injective (kraftRank l e h_finite) := by
  intro i j hij
  rcases ((KraftOrder_isStrictTotalOrder l e).toTrichotomous.rel_or_eq_or_rel_swap
      (a := i) (b := j)) with h | rfl | h
  · exact absurd hij (Nat.ne_of_lt (kraftRank_lt_of_KraftOrder l e h_finite h))
  · rfl
  · exact absurd hij (Nat.ne_of_gt (kraftRank_lt_of_KraftOrder l e h_finite h))

/-- An infinite type can be enumerated in monotone order by an `ℕ`-valued function whose
fibers are finite. -/
lemma exists_equiv_nat_monotone_of_finite_fibers {I : Type*} [Infinite I] (l : I → ℕ)
    (h_finite : ∀ k, {i | l i = k}.Finite) : ∃ e : ℕ ≃ I, Monotone (l ∘ e) := by
  have h_countable : Countable I := by
    rw [← Set.countable_univ_iff]
    rw [show (Set.univ : Set I) = ⋃ k, {i | l i = k} by ext; simp]
    exact Set.countable_iUnion fun k => (h_finite k).countable
  obtain ⟨e⟩ := countable_iff_nonempty_embedding.mp h_countable
  have h_bij : Function.Bijective (kraftRank l e h_finite) :=
    ⟨kraftRank_injective l e h_finite, kraftRank_surjective l e h_finite⟩
  let rankEquiv : I ≃ ℕ := Equiv.ofBijective _ h_bij
  let e' : ℕ ≃ I := rankEquiv.symm
  refine ⟨e', fun n m hnm => ?_⟩
  contrapose! hnm
  have h := kraftRank_lt_of_KraftOrder l e h_finite (KraftOrder_iff.mpr (Or.inl hnm))
  calc
    m = kraftRank l e h_finite (e' m) := (rankEquiv.apply_symm_apply m).symm
    _ < kraftRank l e h_finite (e' n) := h
    _ = n := rankEquiv.apply_symm_apply n

/-- An infinite type can be enumerated monotonically by a Northcott function to `ℕ`. -/
lemma exists_equiv_nat_monotone_of_northcott {I : Type*} [Infinite I] (l : I → ℕ)
    [Northcott l] : ∃ e : ℕ ≃ I, Monotone (l ∘ e) :=
  exists_equiv_nat_monotone_of_finite_fibers l fun k =>
    (Northcott.finite_le (h := l) k).subset (by grind)

/-- An infinite index type with summable Kraft sum can be reordered to make lengths monotone. -/
lemma exists_equiv_nat_monotone_of_summable {I : Type*} [Infinite I] {D : ℕ} (hD : 1 < D)
    {l : I → ℕ} (h_summable : Summable (fun i => (1 / D : ℝ) ^ l i)) :
    ∃ e : ℕ ≃ I, Monotone (l ∘ e) := by
  have h_finite : ∀ k, {i : I | l i = k}.Finite := by
    intro k
    have hEv : ∀ᶠ i in Filter.cofinite, (1 / D : ℝ) ^ l i < (1 / D : ℝ) ^ k :=
      h_summable.tendsto_cofinite_zero.eventually <| Iio_mem_nhds (by positivity)
    refine Filter.eventually_cofinite.mp hEv |>.subset ?_
    simp +contextual
  exact exists_equiv_nat_monotone_of_finite_fibers l h_finite

/-- Any finite type can be sorted by a function to ℕ.

Given a fintype `I` and a function `l : I → ℕ`, produces an equivalence
`e : Fin (card I) ≃ I` such that `l ∘ e` is monotone (i.e., maps increasing
indices to non-decreasing length values), via `Tuple.sort`. -/
lemma exists_equiv_fin_monotone {I : Type*} [Fintype I] (l : I → ℕ) :
    ∃ e : Fin (Fintype.card I) ≃ I, Monotone (l ∘ e) := by
  -- Sort `l`, read through the canonical `Fin (card I) ≃ I` equivalence, via `Tuple.sort`.
  let e₀ : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  refine ⟨(Tuple.sort (l ∘ e₀)).trans e₀, ?_⟩
  simpa [Function.comp_assoc] using Tuple.monotone_sort (l ∘ e₀)

end InformationTheory
