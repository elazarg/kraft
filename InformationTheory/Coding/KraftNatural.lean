import Mathlib.Data.List.OfFn
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Order.BigOperators.Group.Finset

import Mathlib.Tactic.NormNum

namespace InformationTheory

open scoped BigOperators

variable {M : Type*} [Monoid M]

/-- Growth axiom: in any finite `T`, the number of elements of cost exactly `s` is ≤ D^s. -/
def costGrowth (cost : M → ℕ) (D : ℕ) : Prop :=
  ∀ (T : Finset M) (s : ℕ), (T.filter (fun x => cost x = s)).card ≤ D ^ s

/-- The r-fold product of elements from a finite set, defined via Lists. -/
def tupleProduct {S : Finset M} {r : ℕ} (w : Fin r → S) : M :=
  (List.ofFn (fun i => (w i).1)).prod

private lemma len_one {ℓ : M → ℕ} (h_add : ∀ a b : M, ℓ (a * b) = ℓ a + ℓ b) :
    ℓ 1 = 0 := by
  have h : ℓ 1 + ℓ 1 = ℓ 1 := by simpa using (h_add 1 1)
  exact (Nat.add_left_cancel h)

private lemma len_list_prod {ℓ : M → ℕ}
    (h_add : ∀ a b : M, ℓ (a * b) = ℓ a + ℓ b) :
    ∀ xs : List M, ℓ xs.prod = (xs.map ℓ).sum := by
  intro xs
  induction xs with
  | nil => simp [len_one h_add]
  | cons a xs ih => simp [h_add, ih]

/-- Cost additivity for `tupleProduct`. -/
lemma tupleProduct_cost
    {cost : M → ℕ} {S : Finset M} {r : ℕ}
    (cost_mul : ∀ a b, cost (a * b) = cost a + cost b)
    (w : Fin r → S) :
    cost (tupleProduct w) = ∑ i, cost (w i) := by
  simp [tupleProduct, len_list_prod cost_mul, Fin.sum_ofFn]

/--
**McMillan counting bound (unnormalized, ℕ-valued).**

Assume:
* `costGrowth cost D` (capacity-by-level),
* cost additivity,
* injectivity of `tupleProduct` on `r`-tuples from `S`.

Let `s := S.sup cost` and `N := r * s`. Then
\[
\sum_{w : Fin r → S} D^{N - cost(tupleProduct w)} ≤ (N+1) D^N.
\]
-/
theorem mcmillan_counting_of_inj
    {S : Finset M} {D : ℕ}
    {cost : M → ℕ}
    (cost_mul : ∀ a b, cost (a * b) = cost a + cost b)
    (hgrowth : costGrowth cost D)
    (hinj : ∀ r, Function.Injective (tupleProduct (S := S) (r := r)))
    (r : ℕ) :
    (∑ w : Fin r → S, D ^ ((r * S.sup cost) - cost (tupleProduct w)))
      ≤ (r * S.sup cost + 1) * D ^( r * S.sup cost) := by
  classical
  let s := S.sup cost
  let N := r * S.sup cost

  -- Image of all r-tuples under tupleProduct
  let T : Finset M :=
    Finset.image (tupleProduct (S := S) (r := r)) (Finset.univ : Finset (Fin r → S))

  -- Step 1: bound all costs in `T` by `N = r*s`
  have h_cost_le_N : ∀ x ∈ T, cost x ≤ N := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨w, hw, rfl⟩
    have hsum := tupleProduct_cost cost_mul w
    have hterm (i : Fin r) : cost (w i) ≤ s :=
      Finset.le_sup (f := cost) (w i).prop
    have : (∑ i, cost (w i)) ≤ ∑ _ : Fin r, s :=
      Finset.sum_le_sum (fun i _ => hterm i)
    simpa [N, hsum] using (le_trans this (by simp [s]))

  -- Step 2: rewrite the sum over tuples as a sum over `T` (injectivity gives bijection)
  have h_sum_over_T :
      (∑ w : Fin r → S, D ^ (N - cost (tupleProduct w)))
        = ∑ x ∈ T, D ^ (N - cost x) := by
    -- `tupleProduct` is injective on univ, so sum over domain equals sum over image
    refine (Finset.sum_bij (fun w _ => tupleProduct w) ?inj ?map ?surj) ?_
    · simp [T]
    · simp
      intro h ha w
      exact hinj r w
    · intro x hx
      rcases Finset.mem_image.mp hx with ⟨w, hw, rfl⟩
      refine ⟨w, by simp, by simp⟩
    · simp

  -- Step 3: group `T` by cost-levels `s ∈ Icc 0 N`
  -- and use `hgrowth` + constant-sum estimate
  calc
    (∑ w : Fin r → S, D ^ (N - cost (tupleProduct w)))
        = ∑ x ∈ T, D ^ (N - cost x) := h_sum_over_T
    _ = ∑ s ∈ Finset.Icc 0 N, ∑ x ∈ T.filter (fun x => cost x = s), D ^ (N - cost x) := by
        -- define the partitioning union
        have hU : (Finset.Icc 0 N).biUnion (fun s => T.filter (fun x => cost x = s)) = T := by
          ext x
          constructor
          · intro hx
            rcases Finset.mem_biUnion.mp hx with ⟨s, hs, hx⟩
            exact (Finset.mem_filter.mp hx).1
          · intro hx
            have hx_le : cost x ≤ N := h_cost_le_N x hx
            have hs : cost x ∈ Finset.Icc 0 N :=
              Finset.mem_Icc.mpr ⟨Nat.zero_le _, hx_le⟩
            exact Finset.mem_biUnion.mpr ⟨cost x, hs, Finset.mem_filter.mpr ⟨hx, rfl⟩⟩
        have hdisj :
            Set.PairwiseDisjoint (Finset.Icc 0 N)
              (fun s => T.filter (fun x => cost x = s)) := by
          intro a ha b hb hab
          refine Finset.disjoint_left.mpr ?_
          intro x hxa hxb
          have : cost x = a := (Finset.mem_filter.mp hxa).right
          have : cost x = b := (Finset.mem_filter.mp hxb).right
          omega
        simpa [hU] using
          (Finset.sum_biUnion (s := Finset.Icc 0 N)
            (t := fun s => T.filter (fun x => cost x = s))
            (f := fun x => D ^ (N - cost x)) hdisj)
    _ ≤ ∑ s ∈ Finset.Icc 0 N, D ^ N := by
        refine Finset.sum_le_sum (fun s hs => ?_)
        calc
              ∑ x ∈ T.filter (fun x => cost x = s), D ^ (N - cost x)
            = ∑ x ∈ T.filter (fun x => cost x = s), D ^ (N - s) := by
                refine Finset.sum_congr rfl ?_
                intro x hx
                simp [Finset.mem_filter.mp hx]
          _ = (T.filter (fun x => cost x = s)).card * D ^ (N - s) := by
                simp [Finset.sum_const]
          _ ≤ (D ^ s) * D ^ (N - s) :=  Nat.mul_le_mul_right _ (hgrowth T s)
          _ = D ^ (s + (N - s)) := by
                simp [Nat.pow_add]
          _ = D ^ N := by
                simp [Nat.add_sub_of_le (Finset.mem_Icc.mp hs).right]
    _ = (N + 1) * D ^ N := by
        simp [Nat.mul_comm]

/-- (Nat-only) Key algebraic identity turning the tuple-sum into a power of a single sum,
using the *scaled* weight `D^(s - cost x)`. -/
lemma scaled_sum_pow_eq_sum_tupleProduct
    {S : Finset M} {D : ℕ} {cost : M → ℕ} {r : ℕ}
    (cost_mul : ∀ a b, cost (a * b) = cost a + cost b) :
    (∑ x ∈ S, D ^ (S.sup cost - cost x)) ^ r =
    ∑ w : Fin r → S, D ^ (r * S.sup cost - cost (tupleProduct w)) := by
  classical
  let s := S.sup cost
  calc
          (∑ x ∈ S, D ^ (s - cost x)) ^ r
        = (∑ x : S, D ^ (s - cost x)) ^ r := by
            simp [(Finset.sum_coe_sort S (fun x => D ^ (s - cost x))).symm]
    _   = ∑ w : Fin r → S, ∏ i : Fin r, D ^ (s - cost (w i)) :=
            (Fintype.sum_pow (f := fun x : S => D ^ (s - cost x)) r)
    _   = ∑ w : Fin r → S, D ^ (r * s - cost (tupleProduct w)) := by
            apply Fintype.sum_congr
            intro w
            -- show: ∏ i, D^(s - cost(w i)) = D^(r*s - cost(tupleProduct w))
            have hterm (i : Fin r) : cost (w i) ≤ s :=
              Finset.le_sup (f := cost) (w i).prop
            have hprod :
                (∏ i, D ^ (s - cost (w i))) =
                D ^ (∑ i, (s - cost (w i))) := by
                  simpa using
                    (Finset.prod_pow_eq_pow_sum D (s := (Finset.univ : Finset (Fin r)))
                      (f := fun i => (s - cost (w i))))
            have hexp := calc
                   (∑ i, (s - cost (w i))) + (∑ i, cost (w i))
                  = ∑ i, ((s - cost (w i)) + cost (w i)) := by
                        simp [Finset.sum_add_distrib]
                _ = ∑ _ : Fin r, s := by grind
                _ = r * s := by simp
            have : (∏ i, D ^ (s - cost (w i)))
                    =
                  D ^ (r * s - ∑ i, cost (w i)) := by
              simpa using hprod.trans (by grind)
            simpa [tupleProduct_cost cost_mul w] using this

/-- Nat-only corollary: the scaled-sum power is linearly bounded. -/
theorem scaled_sum_pow_le_linear
    {S : Finset M} {D : ℕ} {cost : M → ℕ}
    (cost_mul : ∀ a b, cost (a * b) = cost a + cost b)
    (hgrowth : costGrowth cost D)
    (hinj : ∀ r, Function.Injective (tupleProduct (S := S) (r := r)))
    (r : ℕ) :
    (∑ x ∈ S, D ^ (S.sup cost - cost x)) ^ r
      ≤ (r * S.sup cost + 1) * D ^ (r * S.sup cost) := by
  simpa using (le_trans
    ((scaled_sum_pow_eq_sum_tupleProduct cost_mul).le)
    (mcmillan_counting_of_inj cost_mul hgrowth hinj r))

end InformationTheory
