import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.List.OfFn
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace InformationTheory

private lemma sum_weight_filter_le_one_of_card_le {M : Type*} {ℓ : M → ℕ}
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
            simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (D_nat ^ s : ℝ) * (1 / D) ^ s := by
            gcongr
            exact_mod_cast h_card
    _ = 1 := by simp [D, hD0]

variable {M : Type*}

/-- Growth axiom: in any finite `T`, the number of elements of length `s` is ≤ D^s. -/
def lengthGrowth (ℓ : M → ℕ) (D_nat : ℕ) : Prop :=
  ∀ (T : Finset M) (s : ℕ), (T.filter (fun x => ℓ x = s)).card ≤ D_nat ^ s

variable [Monoid M]

/-- The r-fold product of elements from a finite set, defined via Lists. -/
def tupleProduct {S : Finset M} {r : ℕ} (w : Fin r → S) : M :=
  (List.ofFn (fun i => (w i).1)).prod

/-- The "weight" function (1/D)^ℓ(x) is a Monoid Homomorphism to (ℝ, *). -/
noncomputable def weightHom {ℓ : M → ℕ} {D : ℝ} (h_add : ∀ a b, ℓ (a * b) = ℓ a + ℓ b) :
    M →* ℝ where
  toFun x := (1 / D) ^ (ℓ x)
  map_one' := by
    have := by simpa using h_add 1 1
    simp [this]
  map_mul' x y := by simp [h_add, pow_add]

variable {ℓ : M → ℕ}

lemma tupleProduct_map {S : Finset M} {r : ℕ} {μ : M →* ℝ} {w : Fin r → S} :
    μ (tupleProduct w) = ∏ i : Fin r, μ (w i) := by
  simp [tupleProduct, MonoidHom.map_list_prod, List.prod_ofFn]

private lemma len_one (h_add : ∀ a b : M, ℓ (a * b) = ℓ a + ℓ b) :
    ℓ 1 = 0 := by
  have h : ℓ 1 + ℓ 1 = ℓ 1 := by simpa using (h_add 1 1)
  exact (Nat.add_left_cancel h)

private lemma len_list_prod
    (h_add : ∀ a b : M, ℓ (a * b) = ℓ a + ℓ b) :
    ∀ xs : List M, ℓ xs.prod = (xs.map ℓ).sum := by
  intro xs
  induction xs with
  | nil => simp [len_one h_add]
  | cons a xs ih => simp [h_add, ih]

lemma tupleProduct_len {S : Finset M} {r : ℕ}
    (h_add : ∀ a b, ℓ (a * b) = ℓ a + ℓ b) (w : Fin r → S) :
    ℓ (tupleProduct w) = ∑ i : Fin r, ℓ ((w i).val) := by
  simp [tupleProduct, len_list_prod h_add, List.sum_ofFn]

private lemma kraft_sum_pow_eq_sum_tupleProduct
    {S : Finset M} {r : ℕ} (μ : M →* ℝ) :
    (∑ x ∈ S, μ x) ^ r = ∑ w : Fin r → S, μ (tupleProduct w) := by
  have hS : (∑ x ∈ S, μ x) = ∑ x : S, μ x := (Finset.sum_coe_sort S μ).symm
  calc
    (∑ x ∈ S, μ x) ^ r
        = (∑ x : S, μ x) ^ r := by simp [hS]
    _ = ∑ w : Fin r → S, ∏ i : Fin r, μ (w i) := Fintype.sum_pow (f := fun x : S => μ x) r
    _ = ∑ w : Fin r → S, μ (tupleProduct w) := by
          rw [Fintype.sum_congr]
          exact fun _ => tupleProduct_map.symm

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
        have hlen := tupleProduct_len hlen_mul a
        simp only [T, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_filter, Finset.mem_image,
                   Finset.mem_univ, true_and]
        use ℓ (tupleProduct a)
        refine ⟨⟨?_, ?_⟩, ⟨a, rfl⟩, rfl⟩
        · -- r ≤ (tupleProduct a).length
          -- Each selected codeword has positive length (since [] ∉ S).
          -- Sum of r ones ≤ sum of the lengths.
          have hsum : (∑ _ : Fin r, 1) ≤ ∑ i, ℓ ((a i).val) :=
            Finset.sum_le_sum (fun i _ => hpos _ (a i).prop)
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
    exact sum_weight_filter_le_one_of_card_le dPos (by simpa using hgrowth (T := T) (s := s))
  have h_pow :
      (∑ x ∈ S, (1 / D) ^ ℓ x) ^ r
        = ∑ w : Fin r → S, (1 / D) ^ ℓ (tupleProduct w) := by
    simpa [weightHom] using
      (kraft_sum_pow_eq_sum_tupleProduct (μ := weightHom hlen_mul))
  refine le_trans h_pow.le
    <| h_injective.trans
    <| le_trans (Finset.sum_le_sum h_sum_one) ?_
  simp [D] at *
  rcases r with (_ | _ | r) <;> rcases maxLen with (_ | _ | maxLen) <;> norm_num at *
  · positivity
  · rw [Nat.cast_sub] <;> push_cast <;> nlinarith only

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
    pow_sum_le_linear_bound_of_inj D_pos h_add h_pos h_count h_inj r hr
  -- 3. Algebraic limit argument
  -- If K > 1, then K^r grows exponentially, while r * maxLen grows linearly.
  -- We prove (r * maxLen) / K^r tends to 0, implying eventually (r * maxLen) < K^r.
  have hAbs : |1 / K| < 1 := by
    rw [abs_of_pos (by positivity)]
    exact (div_lt_one (by linarith)).mpr hK_gt_one
  have h_tendsto : Filter.Tendsto (fun r : ℕ => (maxLen : ℝ) * r / K ^ r) Filter.atTop (nhds 0) := by
    simpa [mul_comm, mul_left_comm, mul_div_assoc] using
      ((tendsto_self_mul_const_pow_of_abs_lt_one hAbs).const_mul (maxLen : ℝ))
  -- 4. Derive contradiction
  obtain ⟨r, hr_tendsto⟩ := Filter.eventually_atTop.mp <| h_tendsto.eventually <| gt_mem_nhds zero_lt_one
  -- Pick a large enough r (must be ≥ 1)
  let r_large := max r 1
  have h_strict : (maxLen : ℝ) * r_large / K ^ r_large < 1 := hr_tendsto r_large (le_max_left _ _)
  rw [div_lt_iff₀ (pow_pos (by linarith) _)] at h_strict
  -- But our bound says K^r ≤ r * maxLen
  have h_le := h_bound r_large (le_max_right _ _)
  -- K^r ≤ r * maxLen < K^r => Contradiction
  linarith

end InformationTheory
