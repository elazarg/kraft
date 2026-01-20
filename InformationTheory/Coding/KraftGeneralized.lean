/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Order.Filter.Tendsto
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Abstract Kraft-McMillan Inequality

This file proves a generalized Kraft-McMillan inequality for abstract monoids with a length
function. The key insight is that the classical proof only requires that `r`-fold products have
bounded "ambiguity" (fiber sizes), not strict injectivity.

## Main definitions

* `lengthGrowth`: The growth axiom stating that elements of length `s` number at most `D^s`.
* `tupleProduct`: The `r`-fold product of elements from a finite set.
* `fiber`, `fiberCard`, `BoundedFibers`: General fiber machinery for functions.
* `tupleProductBoundedFibers`: Bounded ambiguity for `r`-fold products.
* `tupleProductFiberBoundSeq`: A sequence `K(r)` bounding fiber sizes for all `r`.

## Main results

* `kraft_inequality_of_fiberBound_exponential`: If fiber sizes grow at most exponentially
  (`K(r) ≤ C^r`), then `∑ D^{-ℓ(x)} ≤ C`.
* `kraft_inequality_of_injective`: The classical case where `r`-fold products are injective,
  yielding `∑ D^{-ℓ(x)} ≤ 1`.

## References

* McMillan, B. (1956), "Two inequalities implied by unique decipherability"
-/

namespace InformationTheory

variable {M : Type*}
variable (ℓ : M → ℕ)

private lemma sum_weight_filter_le_one_of_card_le
    {T : Finset M} {s : ℕ} {D_nat : ℕ} (dPos: D_nat > 0)
    (h_card : (T.filter (fun x => ℓ x = s)).card ≤ D_nat ^ s) :
    (∑ x ∈ T.filter (fun x => ℓ x = s), (1 / (D_nat : ℝ)) ^ ℓ x) ≤ 1 := by
  let D : ℝ := (D_nat : ℝ)
  have hD0 : (D : ℝ) ≠ 0 := by positivity
  calc
    (∑ x ∈ T.filter (fun x => ℓ x = s), (1 / D) ^ ℓ x)
      = ∑ x ∈ T.filter (fun x => ℓ x = s), (1 / D) ^ s := by
            apply Finset.sum_congr rfl
            intro x hx
            have : ℓ x = s := (Finset.mem_filter.mp hx).right
            simp [this]
    _ = (T.filter (fun x => ℓ x = s)).card * (1 / D) ^ s := by
            simp_all only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (D_nat ^ s : ℝ) * (1 / D) ^ s := by
            gcongr
            exact_mod_cast h_card
    _ = 1 := by simp [D, hD0]

variable [Monoid M]

/-- Growth axiom: in any finite `T`, the number of elements of length `s` is ≤ (D_nat)^s. -/
def lengthGrowth (D_nat : ℕ) : Prop :=
  ∀ (T : Finset M) (s : ℕ), (T.filter (fun x => ℓ x = s)).card ≤ D_nat ^ s

-- recursive r-fold product
def tupleProduct {S : Finset M} : ∀ {r : ℕ}, (Fin r → S) → M
  | 0,     _ => 1
  | r + 1, w => (w 0).1 * tupleProduct (fun i : Fin r => w i.succ)

private lemma len_one (hlen_mul : ∀ a b : M, ℓ (a * b) = ℓ a + ℓ b) :
    ℓ (1 : M) = 0 := by
  apply Nat.add_left_cancel
  calc
    ℓ (1 : M) + ℓ (1 : M) = ℓ (1 : M) := by simpa using hlen_mul (1 : M) (1 : M)
    _ = ℓ (1 : M) + 0 := by simp

private lemma tupleProduct_len {S : Finset M} {r : ℕ}
    (hlen_mul : ∀ a b : M, ℓ (a * b) = ℓ a + ℓ b) (w : Fin r → S) :
    ℓ (tupleProduct w) = ∑ i : Fin r, ℓ ((w i).val) := by
  induction r with
  | zero => simp [tupleProduct, len_one (ℓ := ℓ) hlen_mul]
  | succ r ih => simp [tupleProduct, hlen_mul, ih, Fin.sum_univ_succ]

private lemma kraft_sum_pow_eq_sum_tupleProduct
    {S : Finset M} {r : ℕ} (μ : M → ℝ)
    (μ_one : μ 1 = 1)
    (μ_mul : ∀ a b, μ (a*b) = μ a * μ b) :
    (∑ x ∈ S, μ x) ^ r = ∑ w : Fin r → S, μ (tupleProduct w) := by
  have h_expand :
      (∏ _i : Fin r, (∑ x ∈ S, μ x)) =
        ∑ w : Fin r → S, ∏ i : Fin r, μ ((w i).1) := by
    rw [Finset.prod_sum, Finset.sum_bij]
    · intro a ha i
      exact ⟨a i (Finset.mem_univ i), (Finset.mem_pi.mp ha i (Finset.mem_univ i))⟩
    · simp
    · intro a₁ ha₁ a₂ ha₂
      simp [funext_iff]
    · intro b hb
      refine ⟨(fun i _ => (b i).1), ?_, ?_⟩
      · exact Finset.mem_pi.mpr (by simp)
      · rfl
    · simp
  have h_mu_tupleProduct :
      ∀ {r : ℕ} (w : Fin r → S),
        (∏ i : Fin r, μ ((w i).1)) = μ (tupleProduct w) := by
    intro r
    induction r with
    | zero =>
        intro w
        simp [tupleProduct, μ_one]
    | succ r ih =>
        intro w
        simp [Fin.prod_univ_succ, tupleProduct, μ_mul, ih]
  calc
    (∑ x ∈ S, μ x) ^ r
        = ∏ _i : Fin r, (∑ x ∈ S, μ x) := by simp
    _ = ∑ w : Fin r → S, ∏ i : Fin r, μ ((w i).1) := h_expand
    _ = ∑ w : Fin r → S, μ (tupleProduct w) := Finset.sum_congr rfl (fun w _ => h_mu_tupleProduct w)

section Fiber

open Finset

/-- Fiber of `f : A → B` over `y : B`, as a `Finset A` (domain is `univ`). -/
def fiber {A B : Type*} [Fintype A] [DecidableEq B]
    (f : A → B) (y : B) : Finset A :=
  Finset.univ.filter (fun a => f a = y)

/-- Cardinality of the fiber of `f` over `y`. -/
def fiberCard {A B : Type*} [Fintype A] [DecidableEq B]
    (f : A → B) (y : B) : ℕ :=
  (fiber (f := f) y).card

/-- Uniform bound on all fiber sizes of `f`. -/
def BoundedFibers {A B : Type*} [Fintype A] [DecidableEq B]
    (f : A → B) (K : ℕ) : Prop :=
  ∀ y, fiberCard (f := f) y ≤ K

variable [DecidableEq M]

/-- "Bounded ambiguity" for r-fold products from `S^r` into `M`. -/
def tupleProductBoundedFibers (S : Finset M) (r : ℕ) (K : ℕ) : Prop :=
  BoundedFibers (f := tupleProduct (S := S) (r := r)) K

/-- A sequence bound `K r` controlling all r-fold fiber sizes. -/
def tupleProductFiberBoundSeq (S : Finset M) (K : ℕ → ℕ) : Prop :=
  ∀ r, tupleProductBoundedFibers S r (K r)

/-- Main fiber-count inequality (nonnegative weights). -/
lemma sum_comp_le_mul_sum_image_of_boundedFibers
    {A B : Type*} [Fintype A] [DecidableEq B]
    {f : A → B} {g : B → ℝ} (K : ℕ)
    (hg : ∀ b, 0 ≤ g b)
    (hK : BoundedFibers (f := f) K) :
    (∑ a : A, g (f a))
      ≤ (K : ℝ) * (∑ b ∈ (Finset.univ.image f), g b) := by
  classical
  -- abbreviations
  let I : Finset B := (Finset.univ.image f)

  -- fibers over distinct outputs are disjoint
  have hdisj :
      ∀ b1 (hb1 : b1 ∈ I) b2 (hb2 : b2 ∈ I), b1 ≠ b2 →
        Disjoint (fiber (f := f) b1) (fiber (f := f) b2) := by
    intro b1 hb1 b2 hb2 hne
    refine Finset.disjoint_left.2 ?_
    intro a ha1 ha2
    have : f a = b1 := (Finset.mem_filter.mp ha1).right
    have : f a = b2 := (Finset.mem_filter.mp ha2).right
    subst b1 b2
    contradiction

  -- the union of all fibers over the image is the whole domain
  have hunion : I.biUnion (fun b => fiber (f := f) b) = (Finset.univ : Finset A) := by
    ext a
    constructor
    · intro _
      simp
    · intro _
      have hb : f a ∈ I := by
        simp [I]
      have ha : a ∈ fiber (f := f) (f a) := by
        simp [fiber]
      exact Finset.mem_biUnion.2 ⟨f a, hb, ha⟩

  -- rewrite the LHS as a sum over the disjoint union of fibers
  calc
    (∑ a : A, g (f a))
        = ∑ a ∈ (Finset.univ : Finset A), g (f a) := by
            simp
    _ = ∑ a ∈ I.biUnion (fun b => fiber (f := f) b), g (f a) := by
            simp [hunion]
    _ = ∑ b ∈ I, ∑ a ∈ fiber (f := f) b, g (f a) := by
            simpa [I] using (Finset.sum_biUnion hdisj (f := fun a => g (f a)))
    _ = ∑ b ∈ I, (fiberCard (f := f) b : ℝ) * g b := by
            refine Finset.sum_congr rfl ?_
            intro b hb
            -- on a fiber, `f a = b`, so the weight is constant
            calc
              (∑ a ∈ fiber (f := f) b, g (f a))
                  = ∑ a ∈ fiber (f := f) b, g b := by
                      refine Finset.sum_congr rfl ?_
                      intro a ha
                      have : f a = b := by
                        simpa [fiber] using (Finset.mem_filter.mp ha).2
                      simp [this]
              _ = ((fiber (f := f) b).card : ℝ) * g b := by
                      simp
              _ = (fiberCard (f := f) b : ℝ) * g b := by
                      simp [fiberCard]
    _ ≤ ∑ b ∈ I, (K : ℝ) * g b := by
            refine Finset.sum_le_sum ?_
            intro b hb
            -- `fiberCard f b ≤ K` and `0 ≤ g b`
            have hfb : (fiberCard (f := f) b : ℝ) ≤ (K : ℝ) := by
              exact_mod_cast hK b
            exact mul_le_mul_of_nonneg_right hfb (hg b)
    _ = (K : ℝ) * (∑ b ∈ I, g b) := by
            -- pull out the constant factor
            simpa using (Finset.mul_sum (a := (K : ℝ)) (s := I) (f := g)).symm
    _ = (K : ℝ) * (∑ b ∈ (Finset.univ.image f), g b) := by
            simp [I]

/-- Convenience: injective implies `BoundedFibers f 1`. -/
lemma boundedFibers_of_injective
    {A B : Type*} [Fintype A] [DecidableEq B]
    (f : A → B) (hf : Function.Injective f) :
    BoundedFibers (f := f) 1 := by
  classical
  intro y
  -- show `fiberCard f y ≤ 1`
  by_contra hgt
  -- Use the standard `Finset.one_lt_card`/`Finset.exists_ne_of_one_lt_card` route
  have hone_lt : 1 < (fiber (f := f) y).card := by
    -- `2 ≤ n` implies `1 < n`
    exact Nat.lt_of_lt_of_le (by decide : 1 < 2) (by simpa [fiberCard] using Nat.lt_of_not_ge hgt)
  rcases Finset.card_pos.mp (lt_trans (Nat.zero_lt_one) hone_lt) with ⟨a, ha⟩
  -- get a distinct `b ∈ fiber` using the replacement lemma
  rcases Finset.exists_mem_ne hone_lt a with ⟨b, hb, hba⟩
  -- both are in the fiber, so `f a = y` and `f b = y`
  have hfa : f a = y := (Finset.mem_filter.mp ha).2
  have hfb : f b = y := (Finset.mem_filter.mp hb).2
  -- injectivity forces a=b, contradiction with b ≠ a
  exact hba (hf (hfb.trans hfa.symm))

/-- Auxiliary bound with r-fold bounded fibers (injective case is `K_r = 1`). -/
lemma pow_sum_le_linear_bound_of_boundedFibers
    {S : Finset M} {D_nat : ℕ} (dPos : D_nat > 0)
    (hlen_mul : ∀ a b, ℓ (a * b) = ℓ a + ℓ b)
    (hpos : ∀ x ∈ S, 1 ≤ ℓ x)
    (hgrowth : lengthGrowth ℓ D_nat)
    (r : ℕ) (hr : 1 ≤ r)
    (K_r : ℕ)
    (hFib : tupleProductBoundedFibers S r K_r) :
    (∑ x ∈ S, (1 / (D_nat : ℝ)) ^ (ℓ x)) ^ r
      ≤ (K_r : ℝ) * (r * (S.sup ℓ)) := by
  classical
  -- Notation
  set maxLen := S.sup ℓ with hmaxLen_def
  let D : ℝ := (D_nat : ℝ)

  -- Define μ(x) = (1/D)^(ℓ x)
  have μ_mul :
      ∀ a b : M, ((1 / D) ^ (ℓ (a * b))) = ((1 / D) ^ (ℓ a)) * ((1 / D) ^ (ℓ b)) := by
    intro a b
    simp [hlen_mul a b, pow_add]

  have μ_one : (fun x : M => (1 / D) ^ ℓ x) 1 = 1 := by
    have hℓ1 : ℓ (1 : M) = 0 := len_one (ℓ := ℓ) hlen_mul
    simp [hℓ1]

  have h_pow :
      (∑ x ∈ S, (1 / D) ^ ℓ x) ^ r
        = ∑ w : Fin r → S, (1 / D) ^ ℓ (tupleProduct w) :=
    kraft_sum_pow_eq_sum_tupleProduct (M := M) (S := S) (r := r)
      (μ := fun x => (1 / D) ^ ℓ x) μ_one μ_mul

  -- First: bounded fibers gives multiplicity factor K_r:
  -- ∑_w μ(tupleProduct w) ≤ K_r * ∑_{y in image} μ(y)
  let T : Finset M := Finset.univ.image (tupleProduct (S := S) (r := r))

  have h_nonneg : ∀ x : M, 0 ≤ (1 / D) ^ (ℓ x) := by
    intro x
    -- `pow_nonneg` is robust and doesn't need `D ≠ 0`.
    exact pow_nonneg (by positivity : 0 ≤ (1 / D)) _

  have h_mulK :
      (∑ w : Fin r → S, (1 / D) ^ (ℓ (tupleProduct (S := S) (r := r) w)))
        ≤ (K_r : ℝ) * (∑ x ∈ T, (1 / D) ^ (ℓ x)) := by
    -- apply the general lemma with A := (Fin r → S), B := M, f := tupleProduct, g := μ
    have := sum_comp_le_mul_sum_image_of_boundedFibers
      (A := (Fin r → S)) (B := M)
      (f := tupleProduct (S := S) (r := r))
      (g := fun x : M => (1 / D) ^ (ℓ x))
      (K := K_r)
      h_nonneg
      (by
        -- `hFib` is exactly `BoundedFibers` for this `f`
        simpa [tupleProductBoundedFibers, T] using hFib
      )
    -- reconcile `univ.image` with our `T`
    simpa [T] using this

  -- Next: bin T by lengths; show every x ∈ T has length in [r, r*maxLen]
  have h_len_bounds :
      ∀ x ∈ T, r ≤ ℓ x ∧ ℓ x ≤ r * maxLen := by
    intro x hxT
    rcases Finset.mem_image.mp hxT with ⟨w, hw, rfl⟩
    have hlen := tupleProduct_len (ℓ := ℓ) (r := r) hlen_mul w
    constructor
    · -- lower bound: r ≤ sum lengths
      have hsum : (∑ _ : Fin r, 1) ≤ ∑ i : Fin r, ℓ ((w i).val) := by
        refine Finset.sum_le_sum ?_
        intro i hi
        -- each term has length ≥ 1
        exact hpos _ (w i).prop
      simpa [hlen] using hsum
    · -- upper bound: sum lengths ≤ r * maxLen
      -- termwise: ℓ(w i) ≤ maxLen by definition of sup
      have hterm : ∀ i : Fin r, ℓ ((w i).val) ≤ maxLen := by
        intro i
        exact Finset.le_sup (w i).prop
      have hsum_le :
          (∑ i : Fin r, ℓ ((w i).val)) ≤ ∑ _ : Fin r, maxLen := by
        refine Finset.sum_le_sum ?_
        intro i hi
        exact hterm i
      -- `∑ _ : Fin r, maxLen = r * maxLen`
      simpa [hlen] using (le_trans hsum_le (by simp))

  -- partition of T by length values in Icc r (r*maxLen)
  have h_union :
      (Finset.Icc r (r * maxLen)).biUnion (fun s =>
        T.filter (fun x => ℓ x = s)) = T := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_biUnion.mp hx with ⟨s, hs, hx⟩
      exact (Finset.mem_filter.mp hx).1
    · intro hxT
      have hb := h_len_bounds x hxT
      refine Finset.mem_biUnion.mpr ?_
      refine ⟨ℓ x, ?_, ?_⟩
      · exact Finset.mem_Icc.mpr hb
      · exact Finset.mem_filter.mpr ⟨hxT, rfl⟩

  have h_disj :
      ∀ s₁ (hs₁ : s₁ ∈ Finset.Icc r (r * maxLen))
        s₂ (hs₂ : s₂ ∈ Finset.Icc r (r * maxLen)),
        s₁ ≠ s₂ →
          Disjoint (T.filter (fun x => ℓ x = s₁)) (T.filter (fun x => ℓ x = s₂)) := by
    intro s₁ hs₁ s₂ hs₂ hne
    refine Finset.disjoint_left.mpr ?_
    intro x hx1 hx2
    have h1 : ℓ x = s₁ := (Finset.mem_filter.mp hx1).2
    have h2 : ℓ x = s₂ := (Finset.mem_filter.mp hx2).2
    subst s₁ s₂
    contradiction

  have h_sum_over_T :
      (∑ x ∈ T, (1 / D) ^ (ℓ x))
        = ∑ s ∈ Finset.Icc r (r * maxLen),
            ∑ x ∈ T.filter (fun x => ℓ x = s), (1 / D) ^ (ℓ x) := by
    -- use the disjoint union partition
    calc
      (∑ x ∈ T, (1 / D) ^ (ℓ x))
          = ∑ x ∈ (Finset.Icc r (r * maxLen)).biUnion (fun s => T.filter (fun x => ℓ x = s)),
                (1 / D) ^ (ℓ x) := by
                simp [h_union]
      _ = ∑ s ∈ Finset.Icc r (r * maxLen),
            ∑ x ∈ T.filter (fun x => ℓ x = s), (1 / D) ^ (ℓ x) := by
            -- `sum_biUnion` gives sum over union = sum of sums
            simpa using
              (Finset.sum_biUnion (s := Finset.Icc r (r * maxLen))
                (t := fun s => T.filter (fun x => ℓ x = s))
                (f := fun x => (1 / D) ^ (ℓ x))
                h_disj)

  -- each length slice contributes ≤ 1, by the growth axiom
  have h_sum_one :
      ∀ s ∈ Finset.Icc r (r * maxLen),
        (∑ x ∈ T.filter (fun x => ℓ x = s), (1 / D) ^ (ℓ x)) ≤ 1 := by
    intro s hs
    exact sum_weight_filter_le_one_of_card_le (ℓ := ℓ) dPos (by
      simpa using hgrowth (T := T) s)

  -- now combine everything
  have h_T_le :
      (∑ x ∈ T, (1 / D) ^ (ℓ x)) ≤ (r * maxLen : ℝ) := by
    -- first reduce to the binned sum
    rw [h_sum_over_T]
    have :
        (∑ s ∈ Finset.Icc r (r * maxLen),
            ∑ x ∈ T.filter (fun x => ℓ x = s), (1 / D) ^ (ℓ x))
          ≤ ∑ s ∈ Finset.Icc r (r * maxLen), (1 : ℝ) := by
      exact Finset.sum_le_sum h_sum_one
    have hcard :
        (∑ s ∈ Finset.Icc r (r * maxLen), (1 : ℝ))
          ≤ (r * maxLen : ℝ) := by
      simp [D] at *
      rcases r with (_ | _ | r) <;> rcases maxLen with (_ | _ | maxLen) <;> norm_num at *
      · positivity
      · rw [Nat.cast_sub] <;> push_cast <;> nlinarith only
    -- finish
    exact this.trans hcard

  -- final chain
  calc
    (∑ x ∈ S, (1 / (D_nat : ℝ)) ^ (ℓ x)) ^ r
        = ∑ w : Fin r → S, (1 / D) ^ (ℓ (tupleProduct w)) := by
            simpa [D] using h_pow
    _ ≤ (K_r : ℝ) * (∑ x ∈ T, (1 / D) ^ (ℓ x)) := by
            exact h_mulK
    _ ≤ (K_r : ℝ) * (r * maxLen : ℝ) := by
            gcongr
    _ = (K_r : ℝ) * (r * (S.sup ℓ)) := by
            simp [maxLen]

/-- Exponential fiber growth ⇒ Kraft sum bounded by the exponential base. -/
theorem kraft_inequality_of_fiberBound_exponential
    {S : Finset M} {D_nat : ℕ} (D_pos : 0 < D_nat)
    (h_add : ∀ a b, ℓ (a * b) = ℓ a + ℓ b)
    (h_pos : ∀ x ∈ S, 1 ≤ ℓ x)
    (h_count : lengthGrowth ℓ D_nat)
    {K : ℕ → ℕ}
    (hFibSeq : tupleProductFiberBoundSeq S K)
    {C : ℝ}
    (hC : 0 < C)
    (hKexp : ∀ r : ℕ, (K r : ℝ) ≤ C ^ r) :
    (∑ x ∈ S, (1 / (D_nat : ℝ)) ^ (ℓ x)) ≤ C := by
  classical
  by_cases hS : S = ∅
  · subst hS
    simp [hC.le]  -- sum = 0
  -- denote Kraft sum
  set A : ℝ := ∑ x ∈ S, (1 / (D_nat : ℝ)) ^ (ℓ x)
  -- maxLen
  let maxLen : ℕ := S.sup ℓ

  -- A is nonnegative
  have hA_nonneg : 0 ≤ A := by
    refine Finset.sum_nonneg ?_
    intro x hx
    exact pow_nonneg (by positivity : 0 ≤ (1 / (D_nat : ℝ))) _

  -- Goal A ≤ C. Contradict A > C.
  by_contra hA_leC
  have hA_gtC : C < A := by
    simpa [not_le] using hA_leC
  have hA_pos : 0 < A := lt_trans hC hA_gtC

  -- define q = A / C > 1
  let q : ℝ := A / C
  have hq_gt_one : 1 < q := by
    -- since C>0, A>C implies A/C > 1
    have : A / C > 1 := (one_lt_div (show 0 < C from hC)).2 hA_gtC
    simpa [q] using this

  -- we will use the auxiliary bound with K r:
  have h_bound (r : ℕ) (hr : 1 ≤ r) :
      A ^ r ≤ (K r : ℝ) * (r * maxLen) := by
    have hFib_r : tupleProductBoundedFibers (M := M) S r (K r) :=
      hFibSeq r
    simpa [A, maxLen] using
      pow_sum_le_linear_bound_of_boundedFibers (M := M) (ℓ := ℓ)
        (S := S) (D_nat := D_nat)
        (dPos := D_pos) (hlen_mul := h_add) (hpos := h_pos) (hgrowth := h_count)
        (r := r) (hr := hr) (K_r := K r) hFib_r

  -- strengthen using hKexp:  A^r ≤ C^r * (r*maxLen)
  have h_bound' (r : ℕ) (hr : 1 ≤ r) :
      A ^ r ≤ C ^ r * (r * maxLen) := by
    have h1 : A ^ r ≤ (K r : ℝ) * (r * maxLen) := h_bound r hr
    have h2 : (K r : ℝ) * (r * maxLen : ℝ) ≤ (C ^ r) * (r * maxLen) := by
      -- multiply hKexp by the nonnegative factor (r*maxLen)
      have hx : 0 ≤ (r * maxLen : ℝ) := by positivity
      exact mul_le_mul_of_nonneg_right (hKexp r) hx
    -- rearrange RHS so it matches h2
    -- (K r : ℝ) * (r*maxLen) ≤ C^r * (r*maxLen)
    exact le_trans h1 (by
      simpa [mul_assoc, mul_left_comm, mul_comm] using h2)

  -- derive: q^r ≤ r*maxLen for all r≥1
  have hq_pow_le (r : ℕ) (hr : 1 ≤ r) :
      q ^ r ≤ (r * maxLen : ℝ) := by
    have hCr_pos : 0 < C ^ r := pow_pos hC _
    have hA_le : A ^ r / (C ^ r) ≤ (r * maxLen : ℝ) := by
      -- from A^r ≤ C^r * X, divide by C^r>0
      have h' : A ^ r ≤ (r * maxLen : ℝ) * (C ^ r) := by
        -- h_bound' gives A^r ≤ C^r * X; commute to X * C^r
        have := h_bound' r hr
        simpa [mul_assoc, mul_left_comm, mul_comm] using this
      -- now rewrite as division
      exact (div_le_iff₀ hCr_pos).2 h'
    -- rewrite A^r / C^r = (A/C)^r = q^r
    simpa [q, div_pow] using hA_le

  -- Now: (maxLen * r) / q^r → 0 because |1/q|<1
  have hAbs : |1 / q| < 1 := by
    have hq_pos : 0 < q := by
      -- A>0 and C>0
      exact div_pos hA_pos hC
    -- 1/q is positive, so abs is just itself
    rw [abs_of_pos (by positivity)]
    -- |1/q| < 1 ↔ 1/q < 1 ↔ 1 < q
    have : 0 < q := div_pos hA_pos hC
    have : (1 / q) < 1 := (div_lt_one this).2 hq_gt_one
    simpa using this

  have h_tendsto :
      Filter.Tendsto (fun r : ℕ => (maxLen : ℝ) * r / q ^ r) Filter.atTop (nhds 0) := by
    simpa [mul_comm, mul_left_comm, mul_assoc, mul_div_assoc] using
      ((tendsto_self_mul_const_pow_of_abs_lt_one hAbs).const_mul (maxLen : ℝ))

  -- pick r where (maxLen*r)/q^r < 1
  obtain ⟨r0, hr0⟩ :=
    Filter.eventually_atTop.1 <|
      h_tendsto.eventually <| gt_mem_nhds (show (0:ℝ) < 1 by norm_num)

  let r_large := max r0 1
  have hr_ge_1 : 1 ≤ r_large := le_max_right _ _
  have h_strict :
      (maxLen : ℝ) * r_large / q ^ r_large < 1 := by
    exact hr0 r_large (le_max_left _ _)

  have h_strict' : (maxLen : ℝ) * r_large < q ^ r_large := by
    have hqpow_pos : 0 < q ^ r_large := pow_pos (lt_trans (by norm_num) hq_gt_one) _
    -- clear denominators
    simpa [div_lt_iff₀ hqpow_pos, mul_assoc] using h_strict

  -- contradict q^r ≤ r*maxLen (from bounded-fiber inequality)
  have h_le := hq_pow_le r_large hr_ge_1
  -- q^r ≤ r*maxLen but r*maxLen < q^r
  -- need to align multiplication order
  have : q ^ r_large ≤ (maxLen : ℝ) * r_large := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using h_le
  exact (not_lt_of_ge this) h_strict'

end Fiber

/--
**Abstract Kraft-McMillan Inequality**

If a finite set `S` in a monoid `M` satisfies:
1. Elements have additive lengths (logarithmic weight).
2. `S` contains no "empty" (length 0) elements.
3. The ambient space satisfies the counting bound `D^s`.
4. The product map from `S^r` to `M` is injective for all `r`.

Then `∑ D^{-ℓ(x)} ≤ 1`.
-/
theorem kraft_inequality_of_injective
    {S : Finset M} {D_nat : ℕ}
    (D_pos : 0 < D_nat)
    (h_add : ∀ a b, ℓ (a * b) = ℓ a + ℓ b)
    (h_pos : ∀ x ∈ S, 1 ≤ ℓ x)
    (h_count : lengthGrowth ℓ D_nat)
    (h_inj : ∀ r, Function.Injective (tupleProduct (S := S) (r := r))) :
    ∑ x ∈ S, (1 / (D_nat : ℝ)) ^ (ℓ x) ≤ 1 := by
  classical
  exact kraft_inequality_of_fiberBound_exponential (ℓ := ℓ)
      D_pos h_add h_pos h_count
      (K := fun _ => 1)
      (fun r => boundedFibers_of_injective
        (f := tupleProduct (S := S) (r := r))
        (h_inj r))
      (by norm_num)
      (by simp)

end InformationTheory
