/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Order.Filter.Tendsto
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.FreeMonoid.Basic

import InformationTheory.Coding.UniquelyDecodable

/-!
# Kraft-McMillan Inequality

This file proves the Kraft-McMillan inequality for uniquely decodable codes.

## Main definitions

* `concatFn`: Concatenation of `r` codewords into a single string.

## Main results

* `kraft_mcmillan_inequality`: For a uniquely decodable code `S` over an alphabet of size
  `D`, `∑_{w ∈ S} D^{-|w|} ≤ 1`.

The proof uses a counting argument: the `r`-th power of the Kraft sum counts concatenations of
`r` codewords, weighted by length. Since the code is uniquely decodable, these concatenations are
distinct, and the count is bounded by the number of strings of each length.

## References

* McMillan, B. (1956), "Two inequalities implied by unique decipherability"
-/

namespace InformationTheory

variable {α : Type*}

section AbstractEngine

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
private def LengthGrowth (D_nat : ℕ) : Prop :=
  ∀ (T : Finset M) (s : ℕ), (T.filter (fun x => ℓ x = s)).card ≤ D_nat ^ s

-- recursive r-fold product
private def tupleProduct {S : Finset M} : ∀ {r : ℕ}, (Fin r → S) → M
| 0,     _ => 1
| r + 1, w => (w 0).1 * tupleProduct (r := r) (fun i : Fin r => w i.succ)

private lemma tupleProduct_len {S : Finset M} {r : ℕ}
    (hlen_mul : ∀ a b : M, ℓ (a * b) = ℓ a + ℓ b) (w : Fin r → S) :
    ℓ (tupleProduct w) = ∑ i : Fin r, ℓ ((w i).val) := by
  induction r with
  | zero =>
      -- goal: ℓ 1 = 0 (since RHS is empty sum)
      have h1 : ℓ (1 : M) = ℓ (1 : M) + ℓ (1 : M) := by
        -- hlen_mul 1 1 : ℓ (1*1)=ℓ1+ℓ1, and 1*1=1
        simpa using (hlen_mul (1 : M) (1 : M))
      -- turn it into ℓ1 + ℓ1 = ℓ1 + 0 and cancel
      have : ℓ (1 : M) + ℓ (1 : M) = ℓ (1 : M) + 0 := by
        calc
          ℓ (1 : M) + ℓ (1 : M) = ℓ (1 : M) := by simpa using h1.symm
          _ = ℓ (1 : M) + 0 := by simp
      have hℓ1 : ℓ (1 : M) = 0 := by
        exact Nat.add_left_cancel this
      simp [tupleProduct, hℓ1]
  | succ r ih =>
      -- unfold tupleProduct at succ, use hlen_mul, and the IH on the tail
      -- tail: i ↦ w i.succ
      simp [tupleProduct, hlen_mul, ih, Fin.sum_univ_succ]

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

private lemma len_one
    (hlen_mul : ∀ a b : M, ℓ (a * b) = ℓ a + ℓ b) :
    ℓ (1 : M) = 0 := by
  apply Nat.add_left_cancel
  calc
    ℓ (1 : M) + ℓ (1 : M) = ℓ (1 : M) := by simpa using hlen_mul (1 : M) (1 : M)
    _ = ℓ (1 : M) + 0 := by simp

private theorem pow_sum_le_linear_bound_of_inj
    {S : Finset M} {D_nat : ℕ} (dPos: D_nat > 0)
    (hlen_mul : ∀ a b, ℓ (a * b) = ℓ a + ℓ b)
    (hpos : ∀ x ∈ S, 1 ≤ ℓ x)
    (hgrowth : LengthGrowth ℓ D_nat)
    (hinj : ∀ r, Function.Injective (tupleProduct (S := S) (r := r)))
    (r : ℕ) (hr : 1 ≤ r) :
    (∑ x ∈ S, (1 / (D_nat : ℝ)) ^ (ℓ x)) ^ r ≤ r * (S.sup ℓ) := by
  classical
  -- Let $maxLen = \max_{w \in S} |w|$.
  set maxLen := S.sup ℓ with hmaxLen_def
  let D : ℝ := (D_nat : ℝ)
  let T := Finset.image tupleProduct (Finset.univ : Finset (Fin r → S))
  have h_injective :
    ∑ w : Fin r → S, (1 / D) ^ (ℓ (tupleProduct w))
      ≤ ∑ s ∈ Finset.Icc r (r * maxLen),
          ∑ x ∈ T.filter (fun x => ℓ x = s), (1 / D) ^ ℓ x := by
    rw [← Finset.sum_biUnion]
    · apply le_of_eq
      refine Finset.sum_bij (fun w _ => tupleProduct w) ?_ ?_ (by
        intro b hb
        rcases Finset.mem_biUnion.mp hb with ⟨s, -, hb⟩
        rcases Finset.mem_filter.mp hb with ⟨hb, -⟩
        rcases Finset.mem_image.mp hb with ⟨a, ha, rfl⟩
        exact ⟨a, ha, rfl⟩
      ) (by simp)
      · intro a _
        have hlen := tupleProduct_len ℓ hlen_mul a
        simp only [T, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_filter, Finset.mem_image,
                   Finset.mem_univ, true_and]
        use ℓ (tupleProduct a)
        refine ⟨⟨?_, ?_⟩, ⟨a, rfl⟩, rfl⟩
        · -- r ≤ (tupleProduct a).length
          -- Each selected codeword has positive length (since [] ∉ S).
          -- Sum of r ones ≤ sum of the lengths.
          have hsum : (∑ _ : Fin r, 1) ≤ ∑ i, ℓ ((a i).val) := by
            refine Finset.sum_le_sum fun i _ ↦ ?_
            refine Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero fun h' ↦ ?_)
            have hi_pos : 1 ≤ ℓ ((a i).val) := hpos _ (a i).prop
            exact Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hi_pos) h'
          simpa [hlen] using hsum
        · -- Upper bound: |w| ≤ r * maxLen
          -- length of r-fold product
          rw [hlen]
          -- rewrite r*maxLen as a sum and compare termwise
          -- (either of the next two styles)
          · -- style 1 (closest to your old code)
            grw [show r * maxLen = ∑ _ : Fin r, maxLen by simp]
            exact Finset.sum_le_sum (fun i _ => Finset.le_sup (a i).2)
      · intro a₁ _ a₂ _ h_eq
        exact hinj r h_eq
    · exact fun _ _ _ _ _ => Finset.disjoint_left.mpr (by grind)
  -- Since $\sum_{x \in \{0,1\}^s} 2^{-|x|} = 1$ for any $s$, we have
  -- $\sum_{s=r}^{r\ell} \sum_{x \in \{0,1\}^s} 2^{-|x|}
  --   = \sum_{s=r}^{r\ell} 1 = r\ell - r + 1 \le r\ell$.
  have h_sum_one :
      ∀ s ∈ Finset.Icc r (r * maxLen),
        ∑ x ∈ T.filter (fun x => ℓ x = s), (1 / D) ^ (ℓ x) ≤ 1 := by
    intro s _
    exact sum_weight_filter_le_one_of_card_le (ℓ := ℓ) dPos (by simpa using hgrowth (T := T) (s := s))
  have μ_mul : ∀ a b, ((1 / D) ^ (ℓ (a * b))) = ((1 / D) ^ (ℓ a)) * ((1 / D) ^ (ℓ b)) := by
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
  refine le_trans h_pow.le
    <| h_injective.trans
    <| le_trans (Finset.sum_le_sum h_sum_one) ?_
  simp [D] at *
  rcases r with (_ | _ | r) <;> rcases maxLen with (_ | _ | maxLen) <;> norm_num at *
  · positivity
  · rw [Nat.cast_sub] <;> push_cast <;> nlinarith only

open Filter
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
    (h_count : LengthGrowth ℓ D_nat)
    (h_inj : ∀ r, Function.Injective (tupleProduct (S := S) (r := r))) :
    ∑ x ∈ S, (1 / (D_nat : ℝ)) ^ (ℓ x) ≤ 1 := by
  -- 1. Setup contradiction
  set K := ∑ x ∈ S, (1 / (D_nat : ℝ)) ^ (ℓ x)
  by_contra hK_gt_one
  rw [not_le] at hK_gt_one

  -- 2. Use the auxiliary bound: K^r ≤ r * maxLen
  let maxLen := S.sup ℓ
  have h_bound (r: ℕ) (hr: 1 ≤ r) : K ^ r ≤ r * maxLen :=
    pow_sum_le_linear_bound_of_inj ℓ D_pos h_add h_pos h_count h_inj r hr

  -- 3. Algebraic limit argument
  -- If K > 1, then K^r grows exponentially, while r * maxLen grows linearly.
  -- We prove (r * maxLen) / K^r tends to 0, implying eventually (r * maxLen) < K^r.
  have hAbs : |1 / K| < 1 := by
    rw [abs_of_pos (by positivity)]
    exact (div_lt_one (by linarith)).mpr hK_gt_one

  have h_tendsto : Filter.Tendsto (fun r : ℕ => (maxLen : ℝ) * r / K ^ r) Filter.atTop (nhds 0) := by
    simpa [mul_comm, mul_left_comm, mul_assoc, mul_div_assoc] using
      ((tendsto_self_mul_const_pow_of_abs_lt_one hAbs).const_mul (maxLen : ℝ))

  -- 4. Derive contradiction
  obtain ⟨r, hr_tendsto⟩ := Filter.eventually_atTop.mp (h_tendsto.eventually (gt_mem_nhds zero_lt_one))

  -- Pick a large enough r (must be ≥ 1)
  let r_large := max r 1
  have hr_ge_1 : 1 ≤ r_large := le_max_right _ _

  have h_strict : (maxLen : ℝ) * r_large / K ^ r_large < 1 := hr_tendsto r_large (le_max_left _ _)
  rw [div_lt_iff₀ (pow_pos (by linarith) _)] at h_strict

  -- But our bound says K^r ≤ r * maxLen
  have h_le := h_bound r_large hr_ge_1

  -- K^r ≤ r * maxLen < K^r  =>  Contradiction
  linarith

end AbstractEngine


section concatFn

variable {S : Finset (List α)} {r : ℕ}

private def concatFn (w : Fin r → S) : List α :=
  (List.ofFn (fun i => (w i).val)).flatten

private lemma concatFn.length (w : Fin r → S) :
    (concatFn w).length = ∑ i : Fin r, ((w i).val).length := by
  simp [List.sum_ofFn, concatFn]

end concatFn

/-- For uniquely decodable codes, the concatenation map is injective.

This is the key property: distinct tuples of codewords produce distinct concatenations. -/
private lemma uniquely_decodable_concatFn_injective {S : Finset (List α)}
    (h : UniquelyDecodable (S : Set (List α))) (r : ℕ) :
    Function.Injective (concatFn (S := S) (r := r)) := by
  intro w₁ w₂ hflat
  have : (fun i : Fin r => (w₁ i).val) = fun i => (w₂ i).val :=
    List.ofFn_injective (h _ _ (by simp) (by simp) (by simpa using hflat))
  funext i
  exact Subtype.ext (by simpa using congrArg (fun f => f i) this)

/-- The number of strings of length `s` in any set is at most `D^s`
(the total number of such strings). -/
private lemma card_filter_length_eq_le [Fintype α] (T : Finset (List α)) (s : ℕ) :
    (T.filter (fun x => x.length = s)).card ≤ (Fintype.card α) ^ s := by
  classical
  let all_words : Finset (List α) := (Finset.univ : Finset (Fin s → α)).image List.ofFn
  have hsub : T.filter (fun x => x.length = s) ⊆ all_words := by
    intro a ha
    have halen : a.length = s := (Finset.mem_filter.mp ha).right
    apply Finset.mem_image.mpr
    refine ⟨(fun j : Fin s => a.get ⟨j.val, by simp [halen]⟩), ?_, ?_⟩
    · exact Finset.mem_univ _
    · exact List.ext_get (by simp [halen]) (by simp)
  have hcard_all : all_words.card = Fintype.card α ^ s := by
    -- `List.ofFn` is injective, so the image has the same cardinality as the domain.
    simpa using
      (Finset.card_image_of_injective
        (s := (Finset.univ : Finset (Fin s → α)))
        (f := (List.ofFn : (Fin s → α) → List α))
        List.ofFn_injective)
  calc
    (T.filter (fun x => x.length = s)).card
        ≤ all_words.card := Finset.card_le_card hsub
    _ = Fintype.card α ^ s := hcard_all

/-- `S` has no empty word. -/
private def NoEpsilon (S : Finset (List α)) : Prop :=
  ([] : List α) ∉ (S : Set (List α))

/-- For every `r`, concatenation on `r`-tuples from `S` is injective. -/
private def ConcatInj (S : Finset (List α)) : Prop :=
  ∀ r : ℕ, Function.Injective (concatFn (S := S) (r := r))

private lemma one_le_length_of_mem {S : Finset (List α)} (hε : NoEpsilon S) :
    ∀ x ∈ S, 1 ≤ x.length := by
  intro x hx
  have : x.length ≠ 0 := by
    intro hx0
    have : x = [] := by simpa [List.length_eq_zero_iff] using hx0
    exact hε (by simpa [this] using hx)
  exact Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero this)

instance : Monoid (List α) := {
  mul := List.append
  one := List.nil
  mul_assoc := List.append_assoc
  mul_one := List.append_nil
  one_mul := by
    intro a
    change ([] ++ a) = a
    simp
}

-- Adapter: growth axiom packaged for lists (use your existing lemma)
private lemma lengthGrowth_list [Fintype α]:
    LengthGrowth (M := List α) (ℓ := List.length) (D_nat := Fintype.card α) := by
  intro T s
  simpa using card_filter_length_eq_le (T := T) (s := s)

private lemma concatFn_succ_mul {S : Finset (List α)} {r : ℕ}
    (w : Fin (r + 1) → S) :
    concatFn (S := S) (r := r + 1) w
      = (w 0).val * concatFn (S := S) (r := r) (fun i : Fin r => w i.succ) := by
  -- reduce `*` to `++` just once, inside the proof
  change (List.ofFn (fun i : Fin (r + 1) => (w i).val)).flatten
      = (w 0).val ++ (List.ofFn (fun i : Fin r => (w i.succ).val)).flatten
  simp

-- Adapter: tupleProduct = concatFn for lists (monoid product = concatenation)
private lemma tupleProduct_eq_concatFn {S : Finset (List α)} {r : ℕ} {w : Fin r → S} :
    tupleProduct w = concatFn w := by
  induction r with
  | zero => rfl
  | succ r ih => simp [tupleProduct, concatFn_succ_mul, ih]

private lemma injective_tupleProduct_of_injective_concatFn
    {S : Finset (List α)} {r : ℕ}
    (hinj : Function.Injective (concatFn (S := S) (r := r))) :
    Function.Injective (tupleProduct (S := S) (r := r)) := by
  have hfc : tupleProduct (S := S) (r := r)
        = concatFn (S := S) (r := r) := by
    funext w
    simpa using tupleProduct_eq_concatFn
  simpa [hfc]

private lemma pow_sum_le_linear_bound_of_concatInj
    {S : Finset (List α)} [Fintype α] [Nonempty α]
    (hε : NoEpsilon S) (hinj : ConcatInj S)
    (r : ℕ) (hr : r ≥ 1) :
    (∑ w ∈ S, (1 / (Fintype.card α : ℝ)) ^ w.length) ^ r ≤
      r * (Finset.sup S List.length) := by
  have hlen_mul : ∀ a b : List α, List.length (a ++ b) = List.length a + List.length b := by
    simp only [List.length_append, implies_true]
  exact pow_sum_le_linear_bound_of_inj
    (ℓ := List.length)
    (dPos := Fintype.card_pos)
    (hlen_mul := hlen_mul)
    (hpos := one_le_length_of_mem hε)
    (hgrowth := lengthGrowth_list)
    (hinj := fun r => injective_tupleProduct_of_injective_concatFn (hinj r))
    (hr := hr)
    (r := r)

open Filter

public theorem kraft_mcmillan_inequality_of_concatInj
    {S : Finset (List α)} [Fintype α] [Nonempty α]
    (hε : NoEpsilon (α := α) S) (hinj : ConcatInj (α := α) S) :
    ∑ w ∈ S, (1 / Fintype.card α : ℝ) ^ w.length ≤ 1 := by
  have h_kraft := pow_sum_le_linear_bound_of_concatInj hε hinj
  contrapose! h_kraft
  let K := ∑ w ∈ S, (1 / (Fintype.card α : ℝ)) ^ w.length
  let maxLen : ℕ := S.sup List.length
  have hAbs : |1 / K| < 1 := by
    grw [abs_of_pos (by positivity), div_lt_one] <;> grind
  have : Tendsto (fun r : ℕ => r * maxLen / K ^ r) atTop (nhds 0) := by
    simpa [mul_comm, mul_left_comm, mul_assoc, mul_div_assoc] using
      ((tendsto_self_mul_const_pow_of_abs_lt_one hAbs).const_mul (maxLen : ℝ))
  obtain ⟨r, hr⟩ := eventually_atTop.mp <| this.eventually <| gt_mem_nhds zero_lt_one
  refine ⟨r + 1, by linarith, ?_⟩
  have := hr (r + 1) (by linarith)
  rw [div_lt_iff₀ (by positivity)] at this
  linarith

public theorem kraft_mcmillan_inequality {S : Finset (List α)} [Fintype α] [Nonempty α]
    (h : UniquelyDecodable (S : Set (List α))) :
    ∑ w ∈ S, (1 / Fintype.card α : ℝ) ^ w.length ≤ 1 := by
  exact kraft_mcmillan_inequality_of_concatInj
    (by simpa using h.epsilon_not_mem)
    (uniquely_decodable_concatFn_injective h)

end InformationTheory
