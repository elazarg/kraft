import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

import Mathlib.Order.Filter.Tendsto
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

import Kraft.Basic

namespace Kraft

variable {α : Type _}
variable {S : Finset (List α)}

/-- If a code is uniquely decodable, it does not contain the empty string.

The empty string ε can be "decoded" as either zero or two copies of itself,
violating unique decodability. -/
lemma epsilon_not_mem_of_uniquely_decodable (h : UniquelyDecodable (S: Set (List α))):
    [] ∉ S := by
  have h_empty : ∀ x ∈ S, x ≠ [] := by
    intro x hx
    have := h
    specialize this [x] [x, x]
    simp_all only [List.mem_cons, List.not_mem_nil, or_false, SetLike.mem_coe,  or_self, List.flatten_cons, List.self_eq_append_left, List.ne_cons_self, imp_false, forall_const, ne_eq, not_false_eq_true]
  exact fun h => h_empty _ h rfl

/-- If `S` is uniquely decodable, then the concatenation map from `S^r` to strings is injective.

This is the key property that makes the Kraft-McMillan proof work: when we expand
`C^r = (Σ 2^{-|w|})^r`, each term corresponds to a unique concatenation. -/
lemma uniquely_decodable_extension_injective (h : UniquelyDecodable (S: Set (List α))) (r : ℕ) :
    Function.Injective (fun (w : Fin r → S) => (List.ofFn (fun i => (w i).val)).flatten) := by
  -- Assume two functions w1 and w2 map to the same flattened list. We need to show w1 = w2.
  intro w1 w2 h_eq
  -- 1. Use Unique Decodability to show the lists of words are equal
  have h_lists : List.ofFn (fun i => (w1 i).val) = List.ofFn (fun i => (w2 i).val) := by
    apply h
    · simp only [List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff]
      intro i
      exact (w1 i).2
    · simp only [List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff]
      intro i
      exact (w2 i).2
    · exact h_eq

  -- 2. List equality implies pointwise equality of values
  have h_vals : (fun i => (w1 i).val) = (fun i => (w2 i).val) :=
    List.ofFn_injective h_lists
  -- 3. Pointwise equality of values implies equality of functions
  funext i
  apply Subtype.ext
  simpa using congrArg (fun f => f i) h_vals


/-- If `S` is uniquely decodable, then `(Σ 2^{-|w|})^r ≤ r·ℓ` where `ℓ` is the maximum codeword length.

This auxiliary bound is the heart of the Kraft-McMillan proof. The r-th power of the Kraft sum
counts concatenations of r codewords, which by unique decodability are distinct. Since these
concatenations have lengths between r and r·ℓ, we get at most r·ℓ - r + 1 ≤ r·ℓ terms. -/
lemma kraft_mcmillan_inequality_aux [DecidableEq α] [Fintype α] (h : UniquelyDecodable (S: Set (List α))) (r : ℕ) (hr : r ≥ 1) :
    (∑ w ∈ S, (1 / (Fintype.card α) : ℝ) ^ w.length) ^ r ≤ r * (Finset.sup S List.length) := by
  -- Let $\ell = \max_{w \in S} |w|$.
  set ℓ := (S.sup List.length) with hℓ_def
  let D := Fintype.card α
  -- By definition of $C$, we have $C^r = \sum_{w_1,\dots,w_r \in S} 2^{-|w_1 \cdots w_r|}$.
  have h_sum : (∑ w ∈ S, (1 / D : ℝ) ^ w.length) ^ r = ∑ w : Fin r → S, (1 / D : ℝ) ^ ((List.ofFn (fun i => (w i).val)).flatten.length) := by
    rw [show (∑ w ∈ S, (1 / D : ℝ) ^ w.length) ^ r = ∑ w : Fin r → S, ∏ i : Fin r, (1 / D : ℝ) ^ (w i |> Subtype.val |> List.length) from ?_]
    · norm_num [List.length_flatten, Finset.prod_pow_eq_pow_sum]
      norm_num [List.sum_ofFn]
    · rw [← Fin.prod_const, Finset.prod_sum]
      refine' Finset.sum_bij _ _ _ _ _
      · use fun a ha i => ⟨ a i (Finset.mem_univ i), Finset.mem_pi.mp ha i (Finset.mem_univ i) ⟩
      · simp
      · simp [funext_iff]
      · exact fun b _ => ⟨ fun i _ => b i |>.1, Finset.mem_pi.mpr fun i _ => b i |>.2, rfl ⟩
      · simp_all only [Finset.prod_attach_univ, implies_true]
  -- Since the map $(w_1,\dots,w_r) \mapsto w_1 \cdots w_r$ is injective, the sum $\sum_{w_1,\dots,w_r \in S} 2^{-|w_1 \cdots w_r|}$ is at most $\sum_{s=r}^{r\ell} \sum_{x \in \{0,1\}^s} 2^{-|x|}$.
  have h_injective : ∑ w : Fin r → S, (1 / D : ℝ) ^ ((List.ofFn (fun i => (w i).val)).flatten.length) ≤ ∑ s ∈ Finset.Icc r (r * ℓ), ∑ x ∈ Finset.filter (fun x => x.length = s) (Finset.image (fun w : Fin r → S => (List.ofFn (fun i => (w i).val)).flatten) (Finset.univ : Finset (Fin r → S))), (1 / D : ℝ) ^ x.length := by
    rw [← Finset.sum_biUnion]
    · refine le_of_eq ?_
      refine Finset.sum_bij (fun w _ => (List.ofFn fun i => (w i : List α)).flatten) ?_ ?_ ?_ ?_
      -- Membership: flattened length is in [r, r*ℓ]
      · intro a _
        simp only [Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_filter, Finset.mem_image,
                   Finset.mem_univ, true_and]
        use (List.ofFn fun i => (a i : List α)).flatten.length
        refine ⟨⟨?_, ?_⟩, ⟨a, rfl⟩, rfl⟩
        -- Lower bound: r ≤ length (each codeword has length ≥ 1)
        · rw [List.length_flatten, List.map_ofFn, List.sum_ofFn]
          refine le_trans (by simp) (Finset.sum_le_sum fun i _ => Nat.one_le_iff_ne_zero.mpr ?_)
          exact ne_of_gt (List.length_pos_iff.mpr (ne_of_mem_of_not_mem (a i).2 (epsilon_not_mem_of_uniquely_decodable h)))
        -- Upper bound: length ≤ r * ℓ (each codeword has length ≤ ℓ)
        · rw [List.length_flatten, List.map_ofFn, List.sum_ofFn]
          exact le_trans (Finset.sum_le_sum fun i _ => Finset.le_sup (f := List.length) (a i).2) (by
            simp_all only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, le_refl]
         )
      -- Injectivity: follows from unique decodability
      · intro a₁ _ a₂ _ h_eq
        exact uniquely_decodable_extension_injective h r h_eq
      -- Image property
      · simp
      -- Surjectivity onto image
      · simp
    · intro _ _ _ _ hxy
      exact Finset.disjoint_left.mpr fun z hz1 hz2 => hxy (by
        simp_all only [ne_eq, Finset.mem_filter]
     )
  -- Since $\sum_{x \in \{0,1\}^s} 2^{-|x|} = 1$ for any $s$, we have $\sum_{s=r}^{r\ell} \sum_{x \in \{0,1\}^s} 2^{-|x|} = \sum_{s=r}^{r\ell} 1 = r\ell - r + 1 \le r\ell$.
  have h_sum_one : ∀ s ∈ Finset.Icc r (r * ℓ), ∑ x ∈ Finset.filter (fun x => x.length = s) (Finset.image (fun w : Fin r → S => (List.ofFn (fun i => (w i).val)).flatten) (Finset.univ : Finset (Fin r → S))), (1 / D : ℝ) ^ x.length ≤ 1 := by
    intros s hs
    have h_card : Finset.card (Finset.filter (fun x => x.length = s) (Finset.image (fun w : Fin r → S => (List.ofFn (fun i => (w i).val)).flatten) (Finset.univ : Finset (Fin r → S)))) ≤ D ^ s := by
      have h_card : Finset.card (Finset.filter (fun x => x.length = s) (Finset.image (fun w : Fin r → S => (List.ofFn (fun i => (w i).val)).flatten) (Finset.univ : Finset (Fin r → S)))) ≤ Finset.card (Finset.image (fun x : Fin s → α => List.ofFn x) (Finset.univ : Finset (Fin s → α))) := by
        refine Finset.card_le_card ?_
        simp [Finset.subset_iff]
        intro a ha
        -- goal: ∃ a_1, List.ofFn a_1 = (List.ofFn fun i ↦ ↑(a i)).flatten
        -- here `a : Fin r → ↥S`

        -- let x be the flattened concatenation
        let x : List α := (List.ofFn (fun i : Fin r => ((a i : List α)))).flatten

        have hxlen : x.length = s := by
          -- `List.length_flatten` turns length(flatten) into a sum of lengths
          -- and `List.map_ofFn` rewrites that sum to `ha`
          -- (`ha` is exactly the length-sum constraint coming from the filter)
          simpa [x, List.length_flatten, List.map_ofFn, Function.comp] using ha

        -- build the function f : Fin s → α by indexing into x
        refine ⟨(fun j : Fin s => x.get ⟨j.1, by simp [hxlen]⟩), ?_⟩

        -- prove List.ofFn f = x
        apply List.ext_get <;> (subst s; simp [x])
      unfold D at *
      exact h_card.trans (Finset.card_image_le.trans (by norm_num [Finset.card_univ]))
    refine' le_trans (Finset.sum_le_sum fun x hx => _) _
    · use fun x => (1 / D) ^ s
    · simp only [Finset.mem_filter] at hx
      simp [hx.2]
    ·
      -- We need D^s * (1/D)^s ≤ 1.
      simp only [Finset.sum_const, nsmul_eq_mul]
      -- Use monotonicity to multiply the bounds: card ≤ D^s AND (1/D)^s is nonneg
      refine le_trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr h_card) (by positivity)) ?_

      -- Handle the algebra manually
      rw [one_div]
      simp
      rw [←inv_pow, ←mul_pow]
      by_cases hD : (D : ℝ) = 0
      · -- If D=0, then 0 ≤ 1
        simp [hD]
        rw [zero_pow]
        · simp
        · intro szero
          subst s
          simp_all
      · -- If D≠0, then D * D⁻¹ = 1, and 1^s = 1
        simp [hD]
  refine le_trans h_sum.le <| h_injective.trans <| le_trans (Finset.sum_le_sum h_sum_one) ?_
  rcases r with (_ | _ | r) <;> rcases ℓ with (_ | _ | ℓ) <;> norm_num at *
  · positivity
  · rw [Nat.cast_sub] <;> push_cast <;> nlinarith only [hℓ_def]

/-- **Kraft-McMillan Inequality**: If `S` is a finite uniquely decodable code,
then `Σ D^{-|w|} ≤ 1`. -/
theorem kraft_mcmillan_inequality [DecidableEq α] [Fintype α] [Nonempty α] (h : UniquelyDecodable (S: Set (List α))) :
    ∑ w ∈ S, (1 / Fintype.card α : ℝ) ^ w.length ≤ 1 := by
  let D_nat := Fintype.card α
  let D : ℝ := D_nat

  have h_kraft : ∀ r : ℕ, r ≥ 1 → (∑ w ∈ S, (1 / D : ℝ) ^ w.length) ^ r ≤ r * (Finset.sup S List.length) := by
     exact fun r a ↦ kraft_mcmillan_inequality_aux h r a

  contrapose! h_kraft
  let K := ∑ w ∈ S, (1 / D : ℝ) ^ w.length

  have hK1 : 1 < K := by
    simpa [K, D, one_div] using h_kraft

  have h_K_pos : 0 < K := zero_lt_one.trans hK1
  have h_log_pos : 0 < Real.log K := Real.log_pos hK1
  have hr_exists : Filter.Tendsto (fun r : ℕ => (r * (Finset.sup S List.length) : ℝ) / K ^ r) Filter.atTop (nhds 0) := by
    have hr_factor : Filter.Tendsto (fun r : ℕ => (r : ℝ) / K ^ r) Filter.atTop (nhds 0) := by
      -- Substitute y = r * log K. Since log K > 0, r -> infty implies y -> infty.
      let y (r : ℕ) := r * Real.log K
      have h_lim_y : Filter.Tendsto y Filter.atTop Filter.atTop :=
        tendsto_natCast_atTop_atTop.atTop_mul_const h_log_pos

      -- We know y / exp(y) -> 0 as y -> infty
      have h_lim_exp : Filter.Tendsto (fun z => z / Real.exp z) Filter.atTop (nhds 0) := by
        simpa [div_eq_mul_inv, Real.exp_neg, pow_one] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1

      -- Therefore (r * log K) / exp(r * log K) -> 0
      have h_comp := h_lim_exp.comp h_lim_y

      -- Rewrite the target limit (r / K^r) in terms of the substituted limit
      have h_eq : ∀ r : ℕ, (r : ℝ) / K ^ r = (1 / Real.log K) * (y r / Real.exp (y r)) := by
        intro r
        dsimp [y]
        rw [Real.exp_nat_mul, Real.exp_log h_K_pos]
        field_simp [ne_of_gt h_log_pos, pow_ne_zero r (ne_of_gt h_K_pos)]

      -- Apply the equality and the limit properties
      simp only [h_eq]
      -- Simplify (c * 0) to 0
      simpa using Filter.Tendsto.const_mul (1 / Real.log K) h_comp

    simpa [mul_div_right_comm] using hr_factor.mul_const _

  obtain ⟨r, hr⟩ := Filter.eventually_atTop.mp (hr_exists.eventually (gt_mem_nhds zero_lt_one))
  refine ⟨r + 1, by linarith, ?_⟩
  have := hr (r + 1) (by linarith)
  rw [div_lt_iff₀ (by positivity)] at this
  linarith
