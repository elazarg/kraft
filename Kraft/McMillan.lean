import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

import Mathlib.Order.Filter.Tendsto
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

import Kraft.Basic

namespace Kraft

variable {α : Type _}

lemma uniquelyDecodable_flatten_injective
  {S : Set (List α)} (h : UniquelyDecodable S) (r : ℕ) :
  Function.Injective (fun (w : Fin r → S) =>
    (List.ofFn (fun i => (w i).val)).flatten) := by
  intro w1 w2 hflat
  -- Turn the tuples into lists of codewords
  let f1 : Fin r → List α := fun i => (w1 i).val
  let f2 : Fin r → List α := fun i => (w2 i).val
  let L1 : List (List α) := List.ofFn f1
  let L2 : List (List α) := List.ofFn f2

  have hL : L1 = L2 := by
    apply h L1 L2
    · intro x hx
      rcases List.mem_ofFn.mp hx with ⟨i, rfl⟩
      exact (w1 i).property
    · intro x hx
      rcases List.mem_ofFn.mp hx with ⟨i, rfl⟩
      exact (w2 i).property
    · simpa [L1, L2, f1, f2] using hflat

  -- From list equality, recover pointwise equality, hence function equality
  funext i
  apply Subtype.ext
  rcases i with ⟨n, hn⟩

  -- equality of nth entries
  have hn1 : n < L1.length := by simpa [L1] using hn
  have hn2 : n < L2.length := by simpa [L2] using hn
  have hget : L1.get ⟨n, hn1⟩ = L2.get ⟨n, hn2⟩ := by simp [hL]
  simpa [L1, L2, f1, f2] using hget

lemma flatten_length_le_mul_sup  {S : Finset (List α)} (r : ℕ) (w : Fin r → S):
    (List.ofFn (fun i : Fin r => (w i).val)).flatten.length
      ≤ r * (S.sup List.length) := by
  -- Rewrite the LHS as a finite sum of lengths.
  have hlen :
      (List.ofFn (fun i : Fin r => (w i).val)).flatten.length
        = ∑ i : Fin r, (w i).val.length := by
    -- `length(flatten L) = sum (map length L)`, then for `ofFn` turn list-sum into `∑ i`
    simp [List.length_flatten, Function.comp, List.sum_ofFn]

  -- Each codeword length is ≤ the supremum.
  have h_each : ∀ i : Fin r, (w i).val.length ≤ S.sup List.length := by
    intro i
    -- `w i` is an element of `S`, so its length is ≤ sup of lengths in `S`
    exact Finset.le_sup (f := List.length) (w i).property

  -- Sum the pointwise bound.
  calc
    (List.ofFn (fun i : Fin r => (w i).val)).flatten.length
        = ∑ i : Fin r, (w i).val.length := hlen
    _ ≤ ∑ i : Fin r, S.sup List.length := by
        -- monotonicity of summation over `Fin r`
        -- (internally this is over `Finset.univ`)
        simpa using (Finset.sum_le_sum (s := (Finset.univ : Finset (Fin r)))
          (fun i _ => h_each i))
    _ = r * (S.sup List.length) := by
        -- sum of a constant over `Fin r` is `r * const`
        simp [Finset.sum_const, Fintype.card_fin]

lemma r_le_flatten_length_of_no_empty
    {S : Set (List α)}
    (hε : ([] : List α) ∉ S) (r : ℕ) (w : Fin r → S) :
    r ≤ (List.ofFn (fun i : Fin r => (w i).val)).flatten.length := by
  -- Rewrite the length of the concatenation as a sum of lengths.
  have hlen :
      (List.ofFn (fun i : Fin r => (w i).val)).flatten.length
        = ∑ i : Fin r, (w i).val.length := by
    simp [List.length_flatten, Function.comp, List.sum_ofFn]

  -- Each codeword is nonempty, hence has length ≥ 1.
  have h_each : ∀ i : Fin r, 1 ≤ (w i).val.length := by
    intro i
    have hiS : (w i).val ∈ S := (w i).property
    have hne : (w i).val ≠ ([] : List α) := by
      intro h0
      apply hε
      simpa [h0] using hiS
    -- `length_pos` gives 0 < length, turn it into 1 ≤ length for naturals
    exact Nat.succ_le_iff.mp (Nat.succ_le_iff.mpr (List.length_pos_iff.mpr hne))
    -- If the above line is annoying in your version, replace it by:
    -- exact Nat.succ_le_iff.mpr (List.length_pos_iff.mpr hne)

  -- Sum of the lower bounds: ∑ 1 ≤ ∑ length
  have hsum : (∑ i : Fin r, (1 : ℕ)) ≤ ∑ i : Fin r, (w i).val.length := by
    simpa using (Finset.sum_le_sum (s := (Finset.univ : Finset (Fin r)))
      (fun i _ => h_each i))

  -- Convert `∑ i : Fin r, 1` to `r`.
  have hone : (∑ i : Fin r, (1 : ℕ)) = r := by
    simp [Finset.sum_const, Fintype.card_fin]

  -- Finish.
  -- From hsum and hlen: r ≤ flatten.length
  calc
    r = ∑ i : Fin r, (1 : ℕ) := by simp [hone]
    _ ≤ ∑ i : Fin r, (w i).val.length := hsum
    _ = (List.ofFn (fun i : Fin r => (w i).val)).flatten.length := by simp [hlen]

lemma disjoint_filter_length {S : Finset (List α)} {s t : ℕ} (hst : s ≠ t) :
  Disjoint (S.filter (fun x => x.length = s)) (S.filter (fun x => x.length = t)) := by
  refine Finset.disjoint_left.2 ?_
  intro x hs hx
  have hslen : x.length = s := (Finset.mem_filter.1 hs).2
  have htlen : x.length = t := (Finset.mem_filter.1 hx).2
  exact hst (hslen.symm.trans htlen)

/-- If a code is uniquely decodable, it does not contain the empty string.

The empty string ε can be "decoded" as either zero or two copies of itself,
violating unique decodability. -/
lemma epsilon_not_mem_of_uniquely_decodable
    {S : Set (List α)}
    (h : UniquelyDecodable (S: Set (List α))) :
    [] ∉ S := by
  intro h_in
  -- UniquelyDecodable implies [] cannot be decomposed in two ways.
  -- But if [] ∈ S, then [] = [] (1 part) and [] = [] ++ [] (2 parts).
  unfold UniquelyDecodable at h
  specialize h (L1 := [[]]) (L2 := [[], []]) (by simp [h_in]) (by simp [h_in]) (by simp)
  simp at h

/-- If `S` is uniquely decodable, then `(Σ 2^{-|w|})^r ≤ r·ℓ` where `ℓ` is the maximum codeword length.

This auxiliary bound is the heart of the Kraft-McMillan proof. The r-th power of the Kraft sum
counts concatenations of r codewords, which by unique decodability are distinct. Since these
concatenations have lengths between r and r·ℓ, we get at most r·ℓ - r + 1 ≤ r·ℓ terms. -/
lemma kraft_mcmillan_inequality_aux {S : Finset (List α)} [DecidableEq α] [Fintype α] [Nonempty α] (h : UniquelyDecodable (S: Set (List α))) (r : ℕ) (hr : r ≥ 1) :
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
  have hε : ([] : List α) ∉ S := epsilon_not_mem_of_uniquely_decodable h

  let T : Finset (List α) :=
    Finset.image (fun w : Fin r → S => (List.ofFn (fun i => (w i).val)).flatten)
      (Finset.univ : Finset (Fin r → S))

  have h_injective :
    ∑ w : Fin r → S, (1 / D : ℝ) ^ ((List.ofFn (fun i => (w i).val)).flatten.length)
      ≤ ∑ s ∈ Finset.Icc r (r * ℓ),
          ∑ x ∈ T.filter (fun x => x.length = s), (1 / D : ℝ) ^ x.length := by
    rw [← Finset.sum_biUnion]
    · refine le_of_eq ?_
      refine Finset.sum_bij
        (fun w _ => (List.ofFn (fun i : Fin r => (w i).val)).flatten) ?_ ?_ (by simp [T]) (by simp)
      · intro a _
        simp only [T, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_filter,
          Finset.mem_image, Finset.mem_univ, true_and]
        refine ⟨(List.ofFn (fun i : Fin r => (a i).val)).flatten.length, ?_⟩
        refine ⟨⟨?_, ?_⟩, ⟨a, rfl⟩, rfl⟩
        · simpa using (r_le_flatten_length_of_no_empty hε r a)
        · simpa [ℓ] using (flatten_length_le_mul_sup r a)
      · intro a₁ _ a₂ _ h_eq
        exact uniquelyDecodable_flatten_injective h r h_eq
    · intro s hs t ht hst
      exact disjoint_filter_length hst

  -- Since $\sum_{x \in \{0,1\}^s} 2^{-|x|} = 1$ for any $s$, we have $\sum_{s=r}^{r\ell} \sum_{x \in \{0,1\}^s} 2^{-|x|} = \sum_{s=r}^{r\ell} 1 = r\ell - r + 1 \le r\ell$.
  have h_sum_one :
      ∀ s ∈ Finset.Icc r (r * ℓ),
        ∑ x ∈ T.filter (fun x => x.length = s), (1 / D : ℝ) ^ x.length ≤ 1 := by
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
  refine le_trans h_sum.le <| h_injective.trans <| le_trans (Finset.sum_le_sum h_sum_one) ?_
  rcases r with (_ | _ | r) <;> rcases ℓ with (_ | _ | ℓ) <;> norm_num at *
  · positivity
  · rw [Nat.cast_sub] <;> push_cast <;> nlinarith only [hℓ_def]

/-- **Kraft-McMillan Inequality**: If `S` is a finite uniquely decodable code,
then `Σ D^{-|w|} ≤ 1`. -/
theorem kraft_mcmillan_inequality {S : Finset (List α)} [DecidableEq α] [Fintype α] [Nonempty α] (h : UniquelyDecodable (S: Set (List α))) :
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
