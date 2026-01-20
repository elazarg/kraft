/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Order.Filter.Tendsto
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

import InformationTheory.Coding.UniquelyDecodable

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

lemma pow_sum_le_linear_bound_of_inj
    {S : Finset M} {D_nat : ℕ} (dPos: D_nat > 0)
    (hlen_mul : ∀ a b, ℓ (a * b) = ℓ a + ℓ b)
    (hpos : ∀ x ∈ S, 1 ≤ ℓ x)
    (hgrowth : lengthGrowth ℓ D_nat)
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
    (h_count : lengthGrowth ℓ D_nat)
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
  obtain ⟨r, hr_tendsto⟩ := Filter.eventually_atTop.mp <| h_tendsto.eventually <| gt_mem_nhds zero_lt_one
  -- Pick a large enough r (must be ≥ 1)
  let r_large := max r 1
  have hr_ge_1 : 1 ≤ r_large := le_max_right _ _
  have h_strict : (maxLen : ℝ) * r_large / K ^ r_large < 1 := hr_tendsto r_large (le_max_left _ _)
  rw [div_lt_iff₀ (pow_pos (by linarith) _)] at h_strict
  -- But our bound says K^r ≤ r * maxLen
  have h_le := h_bound r_large hr_ge_1
  -- K^r ≤ r * maxLen < K^r => Contradiction
  linarith

end InformationTheory
