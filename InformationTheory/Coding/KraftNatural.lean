import Mathlib.Data.List.OfFn
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

import Mathlib.Tactic.NormNum

namespace InformationTheory

open scoped BigOperators

private lemma sum_sub_eq_card_mul_sub_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {sup : ℕ} {f : ι → ℕ} (hf : ∀ i, f i ≤ sup) :
    (∑ i : ι, (sup - f i)) = (Fintype.card ι) * sup - ∑ i : ι, f i := by
  have h :
      (∑ i : ι, (sup - f i)) + (∑ i : ι, f i) = (Fintype.card ι) * sup := by
    calc
      (∑ i : ι, (sup - f i)) + (∑ i : ι, f i)
          = ∑ i : ι, ((sup - f i) + f i) := by
              simp [Finset.sum_add_distrib]
      _ = ∑ _i : ι, sup := Finset.sum_congr rfl (fun i hi => Nat.sub_add_cancel (hf i))
      _ = (Fintype.card ι) * sup := by simp
  have := congrArg (fun t => t - (∑ i : ι, f i)) h
  simpa [Nat.add_sub_cancel_right] using this

private lemma scaled_prod_pow_eq_pow_sum {T : Type*}
    {S : Finset T} {base : ℕ} {len : T → ℕ} {r : ℕ}
    (w : Fin r → S) :
    (∏ i, base ^ (S.sup len - len (w i))) =
      base ^ (r * S.sup len - ∑ i, len (w i)) := by
  simpa [sum_sub_eq_card_mul_sub_sum (fun i => Finset.le_sup (w i).prop)] using
    Finset.prod_pow_eq_pow_sum base (s := Finset.univ)
        (f := fun i => (S.sup len - len (w i)))

private lemma sum_filter_pow_sub_eq_card_mul {M : Type*}
    {T : Finset M} {base N s : ℕ} {len : M → ℕ} :
    (∑ x ∈ T.filter (fun x => len x = s), base ^ (N - len x))
      = (T.filter (fun x => len x = s)).card * base ^ (N - s) := by
  calc
    (∑ x ∈ T.filter (fun x => len x = s), base ^ (N - len x))
        = ∑ x ∈ T.filter (fun x => len x = s), base ^ (N - s) := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            have hx' : len x = s := (Finset.mem_filter.mp hx).2
            simp [hx']
    _ = (T.filter (fun x => len x = s)).card * base ^ (N - s) := by
          simp [Finset.sum_const]

private lemma card_mul_pow_sub_le_pow {M : Type*}
    {T : Finset M} {base N s : ℕ} {len : M → ℕ}
    (hs : s ≤ N)
    (hcard : (T.filter (fun x => len x = s)).card ≤ base ^ s) :
    (T.filter (fun x => len x = s)).card * base ^ (N - s) ≤ base ^ N := by
  calc
    (T.filter (fun x => len x = s)).card * base ^ (N - s)
        ≤ (base ^ s) * base ^ (N - s) := by
            exact Nat.mul_le_mul_right _ hcard
    _ = base ^ (s + (N - s)) := by simp [Nat.pow_add]
    _ = base ^ N := by simp [Nat.add_sub_of_le hs]

private lemma sum_eq_sum_Icc_filter_len {M : Type*}
    {T : Finset M} {N : ℕ} {len : M → ℕ} {F : M → ℕ}
    (h_len_le_N : ∀ x ∈ T, len x ≤ N) :
    (∑ x ∈ T, F x)
      = ∑ s ∈ Finset.Icc 0 N, ∑ x ∈ T.filter (fun x => len x = s), F x := by
  classical
  let levels : ℕ → Finset M := fun s => T.filter (fun x => len x = s)

  -- union of all level-sets (for s ∈ [0,N]) is exactly T
  have hU : (Finset.Icc 0 N).biUnion levels = T := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_biUnion.mp hx with ⟨s, hs, hx⟩
      exact (Finset.mem_filter.mp hx).1
    · intro hx
      have hx_le : len x ≤ N := h_len_le_N x hx
      have hs : len x ∈ Finset.Icc 0 N :=
        Finset.mem_Icc.mpr ⟨Nat.zero_le _, hx_le⟩
      exact Finset.mem_biUnion.mpr ⟨len x, hs, Finset.mem_filter.mpr ⟨hx, rfl⟩⟩

  -- different levels are disjoint
  have hdisj :
      Set.PairwiseDisjoint (Finset.Icc 0 N) levels := by
    intro a ha b hb hab
    refine Finset.disjoint_left.mpr ?_
    intro x hxa hxb
    have h1 : len x = a := (Finset.mem_filter.mp hxa).right
    have h2 : len x = b := (Finset.mem_filter.mp hxb).right
    exact hab (h1.symm.trans h2)

  -- now sum over T equals sum over the disjoint union of levels
  simpa [hU, levels] using Finset.sum_biUnion hdisj


variable {M : Type*} [Monoid M]

/-- Growth axiom: in any finite `T`, the number of elements of len exactly `s` is ≤ base^s. -/
def ExpBounded (len : M → ℕ) (base : ℕ) : Prop :=
  ∀ (T : Finset M) (s : ℕ), (T.filter (fun x => len x = s)).card ≤ base ^ s

/-- The r-fold product of elements from a finite set, defined via Lists. -/
def prodTuple {S : Finset M} {r : ℕ} (w : Fin r → S) : M :=
  (List.ofFn (fun i => (w i).1)).prod

private lemma len_one {len : M → ℕ} (hmap_mul : ∀ a b : M, len (a * b) = len a + len b) :
    len 1 = 0 := by
  have h : len 1 + len 1 = len 1 := by simpa using (hmap_mul 1 1)
  exact Nat.add_left_cancel h

private lemma len_list_prod {len : M → ℕ}
    (hmap_mul : ∀ a b : M, len (a * b) = len a + len b) :
    ∀ xs : List M, len xs.prod = (xs.map len).sum := by
  intro xs
  induction xs with
  | nil => simp [len_one hmap_mul]
  | cons a xs ih => simp [hmap_mul, ih]

/-- len additivity for `prodTuple`. -/
lemma prodTuple_len
    {len : M → ℕ} {S : Finset M} {r : ℕ}
    (hmap_mul : ∀ a b, len (a * b) = len a + len b)
    (w : Fin r → S) :
    len (prodTuple w) = ∑ i, len (w i) := by
  simp [prodTuple, len_list_prod hmap_mul, Fin.sum_ofFn]

lemma len_prodTuple_le_mul_sup
    {S : Finset M} {len : M → ℕ} {r : ℕ}
    (hprod : ∀ w : Fin r → S, len (prodTuple w) = ∑ i, len (w i))
    (w : Fin r → S) :
    len (prodTuple w) ≤ r * S.sup len := by
  have hterm (i : Fin r) : len (w i) ≤ S.sup len :=
    Finset.le_sup (f := len) (w i).prop
  have : (∑ i, len (w i)) ≤ ∑ _ : Fin r, S.sup len :=
    Finset.sum_le_sum (fun i _ => hterm i)
  simpa [hprod w] using le_trans this (by simp)

/-- Summing a function over a domain equals summing over the image, if the map is injective. -/
private lemma sum_eq_sum_image_of_inj
    {α β : Type*} [DecidableEq β]
    {A : Finset α} {g : α → β}
    (hg : Set.InjOn g A)
    {f : β → ℕ} :
    (∑ a ∈ A, f (g a)) = ∑ b ∈ A.image g, f b := by
  have hinj : ∀ a ∈ A, ∀ a' ∈ A, g a = g a' → a = a' := by
    intro a ha a' ha' h
    exact hg ha ha' h
  simpa using (Finset.sum_image hinj).symm

/--
**McMillan counting bound (unnormalized, ℕ-valued).**

Assume:
* `ExpBounded len base` (capacity-by-level),
* len additivity,
* injectivity of `prodTuple` on `r`-tuples from `S`.

Let `s := S.sup len` and `N := r * s`. Then
\[
\sum_{w : Fin r → S} base^{N - len(prodTuple w)} ≤ (N+1) base^N.
\]
-/
theorem mcmillan_counting_of_inj
    {S : Finset M} {base : ℕ}
    {len : M → ℕ}
    (hmap_mul : ∀ a b, len (a * b) = len a + len b)
    (hbound : ExpBounded len base)
    {r : ℕ}
    (hinj : Function.Injective (prodTuple (S := S) (r := r))) :
    (∑ w : Fin r → S, base ^ ((r * S.sup len) - len (prodTuple w)))
      ≤ (r * S.sup len + 1) * base ^( r * S.sup len) := by
  classical
  let N := r * S.sup len

  -- Image of all r-tuples under prodTuple
  let T : Finset M :=
    Finset.image (prodTuple (S := S) (r := r)) (Finset.univ : Finset (Fin r → S))

  -- group `T` by len-levels `s ∈ Icc 0 N`
  -- and use `hbound` + constant-sum estimate
  calc
    (∑ w : Fin r → S, base ^ (N - len (prodTuple w)))
        = ∑ x ∈ T, base ^ (N - len x) := by
        simpa [T] using
          (sum_eq_sum_image_of_inj
            (f := fun x => base ^ (N - len x)) (fun _ _ _ _ h => hinj h))
    _ = ∑ s ∈ Finset.Icc 0 N, ∑ x ∈ T.filter (fun x => len x = s), base ^ (N - len x) := by
        apply sum_eq_sum_Icc_filter_len
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨w, hw, rfl⟩
        simpa [N] using len_prodTuple_le_mul_sup (prodTuple_len hmap_mul) w
    _ ≤ ∑ s ∈ Finset.Icc 0 N, base ^ N := by
        refine Finset.sum_le_sum (fun s hs => ?_)
        have hs_le : s ≤ N := (Finset.mem_Icc.mp hs).2
        calc
          ∑ x ∈ T.filter (fun x => len x = s), base ^ (N - len x)
              = (T.filter (fun x => len x = s)).card * base ^ (N - s) := by
                  simpa using sum_filter_pow_sub_eq_card_mul
          _ ≤ base ^ N := card_mul_pow_sub_le_pow hs_le (hbound T s)
    _ = (N + 1) * base ^ N := by
        simp [Nat.mul_comm]

/-- (Nat-only) Key algebraic identity turning the tuple-sum into a power of a single sum,
using the *scaled* weight `base^(s - len x)`. -/
lemma scaled_sum_pow_eq_sum_prodTuple
    {S : Finset M} {base : ℕ} {len : M → ℕ} {r : ℕ}
    (hmap_mul : ∀ a b, len (a * b) = len a + len b) :
    (∑ x ∈ S, base ^ (S.sup len - len x)) ^ r =
    ∑ w : Fin r → S, base ^ (r * S.sup len - len (prodTuple w)) := by
  let s := S.sup len
  calc    (∑ x ∈ S, base ^ (s - len x)) ^ r
        = (∑ x : S, base ^ (s - len x)) ^ r := by
            simp [(Finset.sum_coe_sort S (fun x => base ^ (s - len x))).symm]
    _   = ∑ w : Fin r → S, ∏ i : Fin r, base ^ (s - len (w i)) :=
            (Fintype.sum_pow (f := fun x : S => base ^ (s - len x)) r)
    _   = ∑ w : Fin r → S, base ^ (r * s - len (prodTuple w)) := by
            apply Fintype.sum_congr
            intro w
            simp [s, scaled_prod_pow_eq_pow_sum, prodTuple_len hmap_mul w]

/-- Nat-only corollary: the scaled-sum power is linearly bounded. -/
theorem scaled_sum_pow_le_linear
    {S : Finset M} {base : ℕ} {len : M → ℕ}
    (hmap_mul : ∀ a b, len (a * b) = len a + len b)
    (hbound : ExpBounded len base)
    {r : ℕ}
    (hinj : Function.Injective (prodTuple (S := S) (r := r))) :
    (∑ x ∈ S, base ^ (S.sup len - len x)) ^ r
      ≤ (r * S.sup len + 1) * base ^ (r * S.sup len) := by
  simpa using (le_trans
    ((scaled_sum_pow_eq_sum_prodTuple hmap_mul).le)
    (mcmillan_counting_of_inj hmap_mul hbound hinj))

end InformationTheory
