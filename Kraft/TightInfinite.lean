import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.RelIso.Basic

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Defs.Filter
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed

import Kraft.Basic
import Kraft.Digits
import Kraft.Helpers
import Kraft.InequalityFinite

namespace Kraft

open scoped BigOperators Real
open Nat

/-- Prefix-freeness transfers through injective maps. -/
lemma PrefixFree.map_injective {α β : Type _} {f : α → β} (hf : Function.Injective f)
    {S : Set (List α)} (hS : Kraft.PrefixFree S) :
    Kraft.PrefixFree ((List.map f) '' S) := by
  intro a ⟨x, hxS, q⟩ b ⟨y, hyS, q⟩ hpre
  subst a b
  rw [List.IsPrefix.map_iff hf] at hpre
  exact congrArg (List.map f) (hS x hxS y hyS hpre)

/-- The "address" function for constructing prefix-free codes.

For a monotone length sequence `l`, `kraft_A l n` is chosen so that `kraft_A l n / 2^{l n}`
equals the partial Kraft sum `Σ_{k<n} 2^{-l k}`. The codeword for index `n` is then
`natToBits (kraft_A l n) (l n)`. -/
def kraft_A (l : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => (kraft_A l n + 1) * 2 ^ (l (n + 1) - l n)

/-- `kraft_A l n / 2^{l n}` equals the partial Kraft sum `Σ_{k<n} 2^{-l k}`.

This is the key invariant that ensures non-overlapping dyadic intervals. -/
lemma kraft_A_div_pow_eq_sum (l : ℕ → ℕ) (h_mono : Monotone l) (n : ℕ) :
    (kraft_A l n : ℝ) / 2 ^ l n = ∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ l k := by
      induction n
      · simp_all only [CharP.cast_eq_zero, zero_div, Finset.range_zero, Finset.sum_empty]
      · -- Substitute the definition of `kraft_A` into the left-hand side.
        simp_all only [one_div, inv_pow, Finset.sum_range_succ]
        have h_sub : (Kraft.kraft_A l (Nat.succ ‹_›) : ℝ) = (Kraft.kraft_A l ‹_› + 1) * 2 ^ (l (Nat.succ ‹_›) - l ‹_›) := by
          norm_cast
        rw [← ‹ (Kraft.kraft_A l _ : ℝ) / 2 ^ l _ = ∑ x ∈ Finset.range _, (2 ^ l x) ⁻¹ ›, h_sub]
        rw [show l (_ + 1) = l _ + (l (_ + 1) - l _) by rw [Nat.add_sub_of_le (h_mono (Nat.le_succ _))]]
        ring_nf
        -- Combine like terms and simplify the expression.
        field_simp
        ring_nf
        norm_num [← mul_pow]

/-- Generalized "address" function for constructing prefix-free codes over alphabet of size D.

For a monotone length sequence `l`, `kraft_A_gen D l n` is chosen so that
`kraft_A_gen D l n / D^{l n}` equals the partial Kraft sum `Σ_{k<n} D^{-l k}`. -/
def kraft_A_gen (D : ℕ) (l : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => (kraft_A_gen D l n + 1) * D ^ (l (n + 1) - l n)

/-- `kraft_A` is `kraft_A_gen` specialized to base 2. -/
lemma kraft_A_eq_kraft_A_gen_two (l : ℕ → ℕ) : kraft_A l = kraft_A_gen 2 l := by
  ext n
  induction n with
  | zero => rfl
  | succ n ih => simp only [kraft_A, kraft_A_gen, ih]

/-- `kraft_A_gen D l n / D^{l n}` equals the partial Kraft sum `Σ_{k<n} (1/D)^{l k}`.

This is the key invariant that ensures non-overlapping D-adic intervals. -/
lemma kraft_A_gen_div_pow_eq_sum (D : ℕ) (hD : 1 < D) (l : ℕ → ℕ) (h_mono : Monotone l) (n : ℕ) :
    (kraft_A_gen D l n : ℝ) / D ^ l n = ∑ k ∈ Finset.range n, (1 / D : ℝ) ^ l k := by
  have hD_pos : (0 : ℝ) < D := by exact_mod_cast Nat.zero_lt_of_lt hD
  have hD_ne : (D : ℝ) ≠ 0 := ne_of_gt hD_pos
  induction n with
  | zero => simp only [kraft_A_gen, CharP.cast_eq_zero, zero_div, Finset.range_zero, Finset.sum_empty]
  | succ n ih =>
    simp only [one_div, inv_pow, Finset.sum_range_succ]
    have h_sub : (kraft_A_gen D l (n + 1) : ℝ) = (kraft_A_gen D l n + 1) * D ^ (l (n + 1) - l n) := by
      simp only [kraft_A_gen, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow]
    rw [h_sub]
    simp_all only [one_div, inv_pow]
    rw [← ih]
    rw [show l (n + 1) = l n + (l (n + 1) - l n) by rw [Nat.add_sub_of_le (h_mono (Nat.le_succ n))]]
    rw [pow_add]
    field_simp
    simp only [add_tsub_cancel_left]

/-- Generalized converse of Kraft's inequality for monotone length sequences indexed by ℕ.

Given a monotone `l : ℕ → ℕ` with summable Kraft sum ≤ 1 over alphabet of size D,
we construct a prefix-free code by assigning to index `n` the codeword
`natToDigitsBE D (kraft_A_gen D l n) (l n)`. -/
theorem kraft_inequality_tight_nat_mono_gen (D : ℕ) (hD : 1 < D) (l : ℕ → ℕ) (h_mono : Monotone l)
    (h_summable : Summable (fun i => (1 / D : ℝ) ^ l i))
    (h_sum : ∑' i, (1 / D : ℝ) ^ l i ≤ 1) :
    ∃ w : ℕ → List ℕ,
      Function.Injective w ∧
      Kraft.PrefixFree (Set.range w) ∧
      (∀ i, (w i).length = l i) ∧
      (∀ i, ∀ d ∈ w i, d < D) := by
  have hD_pos : 0 < D := Nat.zero_lt_of_lt hD
  have hD_pos_real : (0 : ℝ) < D := by exact_mod_cast hD_pos
  have hD_ne : (D : ℝ) ≠ 0 := ne_of_gt hD_pos_real
  -- By definition of kraft_A_gen, we know that kraft_A_gen D l n < D^{l n} for all n.
  have h_kraft_A_lt : ∀ n, kraft_A_gen D l n < D ^ l n := by
    intro n
    have h_eq : (kraft_A_gen D l n : ℝ) / D ^ l n = ∑ k ∈ Finset.range n, (1 / D : ℝ) ^ l k :=
      kraft_A_gen_div_pow_eq_sum D hD l h_mono n
    have h_lt_succ : ∑ k ∈ Finset.range n, (1 / D : ℝ) ^ l k < ∑ k ∈ Finset.range (n + 1), (1 / D : ℝ) ^ l k := by
      simp only [Finset.sum_range_succ]
      linarith [pow_pos (one_div_pos.mpr hD_pos_real) (l n)]
    have h_le_tsum : ∑ k ∈ Finset.range (n + 1), (1 / D : ℝ) ^ l k ≤ ∑' k, (1 / D : ℝ) ^ l k :=
      Summable.sum_le_tsum _ (fun _ _ => by positivity) h_summable
    have h_lt_one : ∑ k ∈ Finset.range n, (1 / D : ℝ) ^ l k < 1 :=
      lt_of_lt_of_le (lt_of_lt_of_le h_lt_succ h_le_tsum) h_sum
    rw [← h_eq, div_lt_one (by positivity)] at h_lt_one
    exact_mod_cast h_lt_one
  -- kraft_A_gen D is strictly monotone
  have h_kraft_A_mono : StrictMono (kraft_A_gen D l) := by
    refine strictMono_nat_of_lt_succ ?_
    intro n
    simp only [kraft_A_gen]
    exact lt_of_lt_of_le (Nat.lt_add_one _) (Nat.le_mul_of_pos_right _ (Nat.pow_pos hD_pos))
  refine ⟨fun n => Digits.natToDigitsBE D (kraft_A_gen D l n) (l n), ?_, ?_, ?_, ?_⟩
  · -- Injectivity
    intro n m hnm
    have h_kraft_A_eq : kraft_A_gen D l n = kraft_A_gen D l m := by
      apply Digits.natToDigitsBE_inj (Nat.ne_of_gt hD_pos)
      · exact h_kraft_A_lt n
      · have := congr_arg List.length hnm
        simp only [Digits.natToDigitsBE_length] at this
        rw [this]
        exact h_kraft_A_lt m
      · have := congr_arg List.length hnm
        simp only [Digits.natToDigitsBE_length] at this
        rw [this]
        simp_all only
    exact h_kraft_A_mono.injective h_kraft_A_eq
  · -- Prefix-freeness
    rintro _ ⟨n, rfl⟩ _ ⟨m, rfl⟩ hpre
    by_cases hnm : n = m
    · subst n
      rfl
    · -- Use natToDigitsBE_prefix_iff_div
      rw [Digits.natToDigitsBE_prefix_iff_div hD_pos (h_kraft_A_lt n) (h_kraft_A_lt m)] at hpre
      obtain ⟨hwv, hdiv⟩ := hpre
      -- From hdiv: kraft_A_gen D l m / D^(l m - l n) = kraft_A_gen D l n
      -- This means kraft_A_gen D l m lies in the interval [kraft_A_gen D l n * D^(l m - l n), (kraft_A_gen D l n + 1) * D^(l m - l n))
      have h_lb : kraft_A_gen D l n * D ^ (l m - l n) ≤ kraft_A_gen D l m := by
        rw [← hdiv]
        exact Nat.div_mul_le_self _ _
      have h_ub : kraft_A_gen D l m < (kraft_A_gen D l n + 1) * D ^ (l m - l n) := by
        rw [← hdiv, add_mul, one_mul]
        exact Nat.lt_div_mul_add (Nat.pow_pos hD_pos)
      -- Now derive contradiction using Kraft sum bounds
      have h_sum_bounds : (∑ k ∈ Finset.range n, (1 / D : ℝ) ^ l k) ≤ (∑ k ∈ Finset.range m, (1 / D : ℝ) ^ l k) ∧
                          (∑ k ∈ Finset.range m, (1 / D : ℝ) ^ l k) < (∑ k ∈ Finset.range n, (1 / D : ℝ) ^ l k) + (1 / D : ℝ) ^ l n := by
        constructor
        · -- Lower bound from h_lb
          rw [← kraft_A_gen_div_pow_eq_sum D hD l h_mono n, ← kraft_A_gen_div_pow_eq_sum D hD l h_mono m]
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have h_eq : (kraft_A_gen D l n : ℝ) * D ^ l m = kraft_A_gen D l n * D ^ (l m - l n) * D ^ l n := by
            rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hwv]
          rw [h_eq]
          have h_cast : (kraft_A_gen D l n : ℝ) * D ^ (l m - l n) = (kraft_A_gen D l n * D ^ (l m - l n) : ℕ) := by
            simp only [Nat.cast_mul, Nat.cast_pow]
          rw [h_cast]
          calc ((kraft_A_gen D l n * D ^ (l m - l n) : ℕ) : ℝ) * D ^ l n
              ≤ (kraft_A_gen D l m : ℕ) * D ^ l n := by
                apply mul_le_mul_of_nonneg_right _ (by positivity)
                exact_mod_cast h_lb
            _ = (kraft_A_gen D l m : ℝ) * D ^ l n := by norm_cast
        · -- Upper bound from h_ub
          -- abbreviations
          set An : ℕ := kraft_A_gen D l n
          set Am : ℕ := kraft_A_gen D l m
          set ln : ℕ := l n
          set lm : ℕ := l m
          set f : ℕ → ℝ := fun k => (1 / (D : ℝ)) ^ l k

          have hsum_n :
              (An : ℝ) / (D : ℝ) ^ ln = ∑ k ∈ Finset.range n, f k := by
            simpa [An, ln, f] using (kraft_A_gen_div_pow_eq_sum D hD l h_mono n)

          have hsum_m :
              (Am : ℝ) / (D : ℝ) ^ lm = ∑ k ∈ Finset.range m, f k := by
            simpa [Am, lm, f] using (kraft_A_gen_div_pow_eq_sum D hD l h_mono m)

          -- Nat upper bound from division equality (Am / D^(lm-ln) = An)
          have h_ub_nat : Am < (An + 1) * D ^ (lm - ln) := by
            let d := D ^ (lm - ln)
            have hdpos : 0 < d := Nat.pow_pos hD_pos
            have hmod : Am % d < d := Nat.mod_lt _ hdpos
            calc
              Am = (Am / d) * d + Am % d := by exact Eq.symm (div_add_mod' Am d)
              _  < (Am / d) * d + d      := by exact Nat.add_lt_add_left hmod _
              _  = (Am / d + 1) * d      := by simp [Nat.succ_mul]
              _  = (An + 1) * d          := by simp [d, hdiv, An, Am]  -- hdiv is your div-equality

          have hDm_pos : (0 : ℝ) < (D : ℝ) ^ lm := by positivity
          have hcast : (Am : ℝ) < ((An + 1) * D ^ (lm - ln) : ℕ) := by
            exact_mod_cast h_ub_nat

          have hdivlt :
              (Am : ℝ) / (D : ℝ) ^ lm
                < (( (An + 1) * D ^ (lm - ln) : ℕ) : ℝ) / (D : ℝ) ^ lm :=
            (div_lt_div_of_pos_right hcast hDm_pos)

          -- simplify RHS to (An+1)/D^ln using ln ≤ lm (your hwv)
          have hwv' : ln ≤ lm := hwv
          have hpow :
              (D : ℝ) ^ lm = (D : ℝ) ^ (lm - ln) * (D : ℝ) ^ ln := by
            -- lm = (lm-ln)+ln
            nth_rewrite 1 [show lm = (lm - ln) + ln by exact (Nat.sub_add_cancel hwv').symm]
            simp [pow_add]

          have hrhs :
              (( (An + 1) * D ^ (lm - ln) : ℕ) : ℝ) / (D : ℝ) ^ lm
                = (An + 1 : ℝ) / (D : ℝ) ^ ln := by
            -- expand casts + cancel the (D^(lm-ln)) factor
            simp [Nat.cast_mul, Nat.cast_pow, hpow, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
            have ha : ( (D : ℝ) ^ (lm - ln)) ≠ 0 := pow_ne_zero _ hD_ne
            calc
              ( (D : ℝ) ^ (lm - ln)) * (((D : ℝ) ^ ln)⁻¹ * (((D : ℝ) ^ (lm - ln))⁻¹ * ((An : ℝ) + 1)))
                  =
                (((D : ℝ) ^ ln)⁻¹) * (( (D : ℝ) ^ (lm - ln)) * (((D : ℝ) ^ (lm - ln))⁻¹ * ((An : ℝ) + 1))) := by
                    ac_rfl
              _ = (((D : ℝ) ^ ln)⁻¹) * ((An : ℝ) + 1) := by
                    -- cancels (D^(lm-ln))*(D^(lm-ln))⁻¹
                    simp [ha]

          have hdivlt' :
              (Am : ℝ) / (D : ℝ) ^ lm < (An + 1 : ℝ) / (D : ℝ) ^ ln := by
            exact lt_of_lt_of_eq hdivlt hrhs

          -- (An+1)/D^ln = An/D^ln + 1/D^ln, and 1/D^ln = f n
          have hf : f n = 1 / (D : ℝ) ^ ln := by
            simp [f, ln, one_div, inv_pow]

          have hf' : (1 / (D : ℝ) ^ ln) = f n := hf.symm

          have hrhs2 :
              ((An : ℝ) + 1) / (D : ℝ) ^ ln
                = (∑ k ∈ Finset.range n, f k) + f n := by
            calc
              ((An : ℝ) + 1) / (D : ℝ) ^ ln
                  = (An : ℝ) / (D : ℝ) ^ ln + (1 : ℝ) / (D : ℝ) ^ ln := by
                      simp [add_div]
              _   = (∑ k ∈ Finset.range n, f k) + (1 : ℝ) / (D : ℝ) ^ ln := by
                      simp [hsum_n]
              _   = (∑ k ∈ Finset.range n, f k) + f n := by
                      simp [hf']

          -- first normalize the RHS of hdivlt' into ((An:ℝ)+1)/...
          refine (lt_of_lt_of_eq ?_ hrhs2)
          simpa [hsum_m, Nat.cast_add, Nat.cast_one] using hdivlt'
      cases lt_or_gt_of_ne hnm with
      | inl h_lt =>
        have h_sum_ge : ∑ k ∈ Finset.Ico n m, (1 / D : ℝ) ^ l k ≥ (1 / D : ℝ) ^ l n := by
          have hmem : n ∈ Finset.Ico n m := Finset.left_mem_Ico.mpr h_lt
          exact Finset.single_le_sum (f := fun k => (1 / D : ℝ) ^ l k) (fun x _ => by positivity) hmem
        simp only [Finset.sum_Ico_eq_sub _ (le_of_lt h_lt)] at h_sum_ge
        linarith [h_sum_bounds.1, h_sum_bounds.2]
      | inr h_gt =>
        have hlmn : l m ≤ l n := h_mono (le_of_lt h_gt)
        have hlen : l n = l m := le_antisymm hwv hlmn
        have hAeq : kraft_A_gen D l m = kraft_A_gen D l n := by
          -- exponent is 0 now
          simpa [hlen] using hdiv
        have : n = m := h_kraft_A_mono.injective hAeq.symm
        exact (hnm this).elim
  · -- Length preservation
    intro i
    simp only [Digits.natToDigitsBE_length]
  · -- Digits are < D
    intro i d hd
    simp only [Digits.natToDigitsBE, List.mem_ofFn] at hd
    obtain ⟨j, rfl⟩ := hd
    exact Nat.mod_lt _ hD_pos

lemma map_val_pmap_mk (D : ℕ) (xs : List ℕ) (h : ∀ d ∈ xs, d < D) :
    (xs.pmap (fun d hd => (⟨d, hd⟩ : Fin D)) h).map (fun x : Fin D => x.val) = xs := by
  induction xs with
  | nil =>
      simp [List.pmap]
  | cons a tl ih =>
      have htl : ∀ d ∈ tl, d < D := by
        intro d hd
        exact h d (by simp [hd])
      -- unfold pmap on cons, map on cons, then use IH
      simp [List.pmap, ih]

/-- Converse of Kraft's inequality for monotone length sequences, returning `List (Fin D)`. -/
theorem kraft_inequality_tight_nat_mono_fin
    (D : ℕ) (hD : 1 < D) (l : ℕ → ℕ) (h_mono : Monotone l)
    (h_summable : Summable (fun i => (1 / D : ℝ) ^ l i))
    (h_sum : ∑' i, (1 / D : ℝ) ^ l i ≤ 1) :
    ∃ w : ℕ → List (Fin D),
      Function.Injective w ∧
      Kraft.PrefixFree (Set.range w) ∧
      (∀ i, (w i).length = l i) := by
  -- 1) get the nat-valued code with digit bounds
  obtain ⟨wNat, hwNat_inj, hwNat_pf, hwNat_len, hwNat_bound⟩ :=
    kraft_inequality_tight_nat_mono_gen
      (D := D) (hD := hD) (l := l) (h_mono := h_mono)
      (h_summable := h_summable) (h_sum := h_sum)

  -- 2) retype digits to `Fin D` using the bound proof
  let w : ℕ → List (Fin D) := fun i =>
    (wNat i).pmap (fun d hd => (⟨d, hd⟩ : Fin D))
      (by
        intro d hd
        exact hwNat_bound i d hd)

  -- helpful simp fact: mapping `Fin.val` back yields the original nat list
  have map_val_w (i : ℕ) : (w i).map (fun x : Fin D => x.val) = wNat i := by
    -- unfold w
    dsimp [w]
    -- apply the general lemma
    simpa using
      (map_val_pmap_mk (D := D) (xs := wNat i)
        (h := by
          intro d hd
          exact hwNat_bound i d hd))

  refine ⟨w, ?_, ?_, ?_⟩

  · -- 3) Injectivity: reduce to injectivity of wNat by mapping `Fin.val`
    intro n m hnm
    apply hwNat_inj
    have : (w n).map (fun x : Fin D => x.val) = (w m).map (fun x : Fin D => x.val) :=
      congrArg (List.map (fun x : Fin D => x.val)) hnm
    simpa [map_val_w] using this

  · -- 4) PrefixFree: a prefix in `Fin D` maps to a prefix in `ℕ`
    intro a ha b hb hpre
    rcases ha with ⟨n, rfl⟩
    rcases hb with ⟨m, rfl⟩
    have hpreNat :
        wNat n <+: wNat m := by
      have : ((w n).map (fun x : Fin D => x.val))
                <+: ((w m).map (fun x : Fin D => x.val)) :=
        List.IsPrefix.map (fun x : Fin D => x.val) hpre
      simpa [map_val_w] using this
    have hEqNat : wNat n = wNat m :=
      hwNat_pf (wNat n) ⟨n, rfl⟩ (wNat m) ⟨m, rfl⟩ hpreNat
    have : n = m := hwNat_inj hEqNat
    subst this
    rfl

  · -- lengths are preserved by pmap
    intro i
    -- usually: simp [w, hwNat_len i]
    simp [w, hwNat_len i]

lemma exists_pow_le_of_lt_one {r ε : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hε : 0 < ε) :
  ∃ N, ∀ n ≥ N, r^n < ε := by
  -- from convergence r^n → 0, we get eventually r^n ∈ Iio ε
  have hT := tendsto_pow_atTop_nhds_zero_of_lt_one (𝕜 := ℝ) hr0 hr1
  have hEv : ∀ᶠ n in Filter.atTop, r ^ n < ε := by
    have : Set.Iio ε ∈ nhds (0 : ℝ) := Iio_mem_nhds hε
    exact hT.eventually this
  rcases (Filter.eventually_atTop.1 hEv) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  exact hN n hn

lemma exists_shift_tail_lt
    (r : ℝ) (Llast : ℕ) {k : ℕ} (l : Fin k → ℕ)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (h_sum_lt : (∑ i, r ^ l i) < 1) :
    ∃ s : ℕ, (r ^ (Llast + s + 1)) / (1 - r) < (1 - (∑ i, r ^ l i)) := by
  have hden : 0 < (1 - r) := sub_pos.mpr hr1
  have hδ   : 0 < (1 - (∑ i, r ^ l i)) := sub_pos.mpr h_sum_lt

  -- r = 0 is trivial: tail = 0 and RHS > 0
  by_cases hrzero : r = 0
  · subst hrzero
    refine ⟨0, ?_⟩
    simpa using hδ

  have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hrzero)
  have hrpowpos : 0 < r ^ (Llast + 1) := pow_pos hrpos _
  have hrpowne  : (r ^ (Llast + 1)) ≠ 0 := ne_of_gt hrpowpos

  -- Choose ε so that: r^s < ε ⇒ r^(Llast+s+1) < (1-sum)*(1-r)
  let ε : ℝ := ((1 - (∑ i, r ^ l i)) * (1 - r)) / (r ^ (Llast + 1))
  have hεpos : 0 < ε := by
    have : 0 < (1 - (∑ i, r ^ l i)) * (1 - r) := mul_pos hδ hden
    exact div_pos this hrpowpos

  obtain ⟨s, hs⟩ :
      ∃ N, ∀ n ≥ N, r ^ n < ε :=
    exists_pow_le_of_lt_one (r := r) (ε := ε) hr0 hr1 hεpos
  refine ⟨s, ?_⟩
  have hs0 : r ^ s < ε := hs s (le_rfl)

  have hmul :
      (r ^ (Llast + 1)) * (r ^ s) < (r ^ (Llast + 1)) * ε :=
    mul_lt_mul_of_pos_left hs0 hrpowpos

  have hleft :
      (r ^ (Llast + 1)) * (r ^ s) = r ^ (Llast + s + 1) := by
    calc
      (r ^ (Llast + 1)) * (r ^ s) = r ^ ((Llast + 1) + s) := by
        simp [pow_add, mul_comm, mul_assoc]
      _ = r ^ (Llast + s + 1) := by
        simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

  have hrhs :
      (r ^ (Llast + 1)) * ε = (1 - (∑ i, r ^ l i)) * (1 - r) := by
    set rpow : ℝ := r ^ (Llast + 1)
    set num  : ℝ := (1 - (∑ i, r ^ l i)) * (1 - r)
    have hrpowne' : rpow ≠ 0 := by
      simpa [rpow] using hrpowne
    dsimp [ε, rpow, num]
    -- convert `rpow * (num / rpow)` into `(rpow * num) / rpow`
    calc
      (r ^ (Llast + 1)) * (num / (r ^ (Llast + 1)))
          = ((r ^ (Llast + 1)) * num) / (r ^ (Llast + 1)) := by
              simpa [mul_assoc] using (mul_div_assoc (r ^ (Llast + 1)) num (r ^ (Llast + 1))).symm
      _ = num := by simpa [mul_assoc] using (mul_div_cancel_left₀ num hrpowne')

  have hmain :
      r ^ (Llast + s + 1) < (1 - (∑ i, r ^ l i)) * (1 - r) := by
    simpa [hleft, hrhs] using hmul

  -- Divide by (1-r) > 0
  exact (div_lt_iff₀ hden).2 (by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmain)

lemma exists_shift_tail_le
    (r : ℝ) (Llast : ℕ) {k : ℕ} (l : Fin k → ℕ)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (h_sum_lt : (∑ i, r ^ l i) < 1) :
    ∃ s : ℕ, (r ^ (Llast + s + 1)) / (1 - r) ≤ (1 - (∑ i, r ^ l i)) := by
  rcases exists_shift_tail_lt (r := r) (Llast := Llast) (l := l) hr0 hr1 h_sum_lt with ⟨s, hs⟩
  exact ⟨s, le_of_lt hs⟩

lemma abs_one_div_nat_lt_one {D : ℕ} (hD : 1 < D) : |(1 / (D : ℝ))| < 1 := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (Nat.zero_lt_of_lt hD)
  have hD1 : (1 : ℝ) < D := by exact_mod_cast hD
  -- nonneg so abs = id
  have hnonneg : 0 ≤ (1 / (D : ℝ)) := by exact one_div_nonneg.mpr (le_of_lt hDpos)
  rw [abs_of_nonneg hnonneg]
  exact (div_lt_one hDpos).2 hD1

lemma tsum_geometric_tail (r : ℝ) (k : ℕ) (hr : |r| < 1) :
  (∑' n : ℕ, r^(n+k)) = r^k / (1 - r) := by
  -- rewrite r^(n+k) as r^k * r^n, then pull out the constant and use the closed form
  have hgeom : Summable (fun n : ℕ => r^n) :=
    summable_geometric_of_abs_lt_one hr
  calc
    (∑' n : ℕ, r^(n+k))
        = ∑' n : ℕ, (r^k) * (r^n) := by
            refine tsum_congr ?_
            intro n
            -- r^(n+k) = r^n * r^k, then commute
            -- (using pow_add: r^(n+k)=r^n*r^k)
            simp [pow_add, mul_comm]
    _   = (r^k) * (∑' n : ℕ, r^n) := by
            simpa using (tsum_mul_left (a := r^k) (f := fun n : ℕ => r^n))
    _   = r^k / (1 - r) := by
            -- closed form: tsum r^n = 1 / (1 - r)
            simp [tsum_geometric_of_abs_lt_one hr, div_eq_mul_inv]

lemma tsum_const_mul_geometric (r c : ℝ) (hr : |r| < 1) :
  (∑' n : ℕ, c * r^n) = c / (1 - r) := by
  simpa [<-tsum_geometric_of_abs_lt_one hr, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    (tsum_mul_left (a := c) (f := fun n : ℕ => r^n))

lemma summable_mul_geometric {r : ℝ} (hr : |r| < 1) (c : ℝ) :
  Summable (fun n : ℕ => c * r^n) := by
  -- geometric is summable, and scalar-multiplying preserves summability
  simpa [mul_assoc] using (summable_geometric_of_abs_lt_one hr).mul_left c

lemma tsum_eq_sum_range_add_tsum_add
    {α : Type _} [NormedAddCommGroup α]
    {k : ℕ}
    {f : ℕ → α} (hs : Summable f) :
    (∑' n, f n) = (Finset.sum (Finset.range k) f) + (∑' n, f (n + k)) := by
  exact (Summable.sum_add_tsum_nat_add (f := f) k hs).symm

def ext_shift {k: ℕ} (Llast s : ℕ) (l : Fin k → ℕ) (n : ℕ) : ℕ :=
  if h : n < k then l ⟨n,h⟩ else Llast + s + (n - k + 1)

lemma ext_shift_eq {k : ℕ} (l : Fin k → ℕ) (Llast s : ℕ) (i : Fin k) :
  ext_shift Llast s l i = l i := by
  -- `i.val < k` so we take the `if`-true branch, and `Fin.eta` cleans the subtype
  simp [ext_shift, i.isLt, Fin.eta]

lemma ext_shift_add_k {k : ℕ} (l : Fin k → ℕ) (Llast s : ℕ) (n : ℕ) :
  ext_shift Llast s l (n + k) = Llast + s + (n + 1) := by
  have hnk : ¬ n + k < k := by
    exact not_lt_of_ge (Nat.le_add_left k n)  -- k ≤ n+k
  -- simplify else-branch and (n+k)-k = n (via commutativity)
  simp [ext_shift, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

lemma ext_shift_monotone (k : ℕ) (l : Fin k → ℕ) (hmono : Monotone l) (hk : k ≠ 0) (s : ℕ) :
    Monotone (ext_shift (l ⟨k-1, Nat.pred_lt (by simpa using hk : k.sub 0 ≠ 0)⟩) s l) := by
  intro i j hij
  by_cases hi : i < k
  · by_cases hj : j < k
    · -- both in the Fin-part
      have hij' : (⟨i, hi⟩ : Fin k) ≤ ⟨j, hj⟩ := by exact hij
      simp [ext_shift, hi, hj]
      exact hmono hij'
    · -- i < k, j ≥ k: bound l⟨i⟩ by Llast, then Llast ≤ Llast+s+...
      have hk1lt : k - 1 < k := Nat.pred_lt (by simpa using hk : k.sub 0 ≠ 0)
      have h_le_last : l ⟨i, hi⟩ ≤ l ⟨k - 1, hk1lt⟩ := by
        exact hmono (Nat.le_pred_of_lt hi)
      simp [ext_shift, hi, hj]
      simp_all only [le_add_right_of_le]
  · -- i ≥ k implies j ≥ k (since i ≤ j)
    have hj : ¬ j < k := by
      have : k ≤ i := le_of_not_gt hi
      exact not_lt_of_ge (le_trans this hij)
    simp [ext_shift, hi, hj]
    -- reduce to monotonicity of (n - k + 1)
    have hsub : i - k ≤ j - k := Nat.sub_le_sub_right hij k
    have hsub1 : i - k + 1 ≤ j - k + 1 := Nat.add_le_add_right hsub 1
    simp_all only [tsub_le_iff_right]

lemma PrefixFree.mono {α : Type _} {S T : Set (List α)} (hS : PrefixFree S) (hST : T ⊆ S) :
  PrefixFree T := by
  intro a ha b hb hpre
  exact hS a (hST ha) b (hST hb) hpre

/-- Finite-index converse, derived from the ℕ-index theorem.
Requires strict slack; otherwise the ℕ-extension necessarily adds positive mass. -/
lemma kraft_inequality_tight_fin_lt
    (D : ℕ) (hD : 1 < D) {k : ℕ}
    (l : Fin k → ℕ) (h_mono : Monotone l)
    (h_sum : (∑ i, (1 / D : ℝ) ^ l i) < 1) :
    ∃ w : Fin k → List (Fin D),
      Function.Injective w ∧
      Kraft.PrefixFree (Set.range w) ∧
      ∀ i, (w i).length = l i := by
  by_cases hk : k = 0
  · subst hk
    refine ⟨fun i => (Fin.elim0 i), fun i => (Fin.elim0 i), ?_, fun i => (Fin.elim0 i)⟩
    · intro a ha b hb hpre
      rcases ha with ⟨i, rfl⟩
      exact (Fin.elim0 i)

  -- Let r = 1/D. We'll add a geometric tail with adjustable shift s.
  let r : ℝ := (1 / D : ℝ)

  -- pick some "last" length to anchor the tail
  let Llast : ℕ := l ⟨k-1, by omega⟩

  -- Now choose shift s so that the tail tsum ≤ (1 - finiteSum).
  -- Concretely, tail is ≤ r^(Llast+s+1) / (1-r).
  -- Use `r^s → 0` (since 0 < r < 1 from hD) to find such s.
  obtain ⟨s, hs_tail⟩ : ∃ s : ℕ,
      (r ^ (Llast + s + 1)) / (1 - r) ≤ (1 - (∑ i, r ^ l i)) := by
    refine exists_shift_tail_le (r := r) (Llast := Llast) (l := l) ?_ ?_ ?_
    · apply le_of_lt
      exact one_div_pos.mpr (by exact_mod_cast (Nat.zero_lt_of_lt hD))
    · -- r < 1
      exact (div_lt_one (by exact_mod_cast (Nat.zero_lt_of_lt hD))).2 (by exact_mod_cast hD)
    · subst r
      exact h_sum

  -- Redefine lNat with the chosen shift s:
  let lNat : ℕ → ℕ := ext_shift Llast s l
  let f : ℕ → ℝ := fun n => r ^ lNat n

  have h_monoNat : Monotone lNat := ext_shift_monotone k l h_mono hk s

  have habs : |r| < 1 := by simpa [r] using abs_one_div_nat_lt_one hD

  have h_shift_f :
      ∀ n : ℕ, f (n + k) = (r ^ (Llast + s + 1)) * (r ^ n) := by
    intro n
    dsimp [f, lNat]
    rw [ext_shift_add_k (k := k) (l := l) (Llast := Llast) (s := s)]
    simp [pow_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, mul_left_comm, mul_comm]

  -- Apply your proved ℕ theorem
  obtain ⟨wNat, hwNat_inj, hwNat_pf, hwNat_len⟩ := by
    have h_tsum_tail : (∑' n : ℕ, f (n + k)) = (r ^ (Llast + s + 1)) / (1 - r) := by
      -- use h_shift_f to rewrite into c * r^n
      calc
        (∑' n : ℕ, f (n + k))
            = ∑' n : ℕ, (r ^ (Llast + s + 1)) * (r ^ n) := by
                refine tsum_congr ?_
                intro n
                simp [h_shift_f n]
        _   = (r ^ (Llast + s + 1)) / (1 - r) := by
                simpa using (tsum_const_mul_geometric r (r^(Llast+s+1)) habs)
    -- prefix sum over range k equals the Fin-sum because lNat agrees with l on < k
    have h_prefix :
        (∑ n ∈ Finset.range k, f n) = ∑ i : Fin k, r ^ l i := by
      rw [<-Fin.sum_univ_eq_sum_range]
      -- the only simp you need is ext_shift_eq
      simp [f, lNat, ext_shift_eq]

    have h_summable_shift : Summable (fun n : ℕ => f (n + k)) := by
      -- now: constant * geometric
      -- rewrite via h_shift_f and apply your extracted summable_mul_geometric
      refine (summable_mul_geometric (r := r) habs (c := r ^ (Llast + s + 1))).congr ?_
      intro n
      simp [h_shift_f n, mul_comm]

    have h_summableNat : Summable f := by
      exact (summable_nat_add_iff k).1 h_summable_shift

    have h_tsumNat : (∑' n : ℕ, f n) ≤ 1 := by
      rw [tsum_eq_sum_range_add_tsum_add (f := f) h_summableNat, h_prefix, h_tsum_tail]
      have : (r ^ (Llast + s + 1)) / (1 - r) ≤ 1 - (∑ i : Fin k, r ^ l i) := by
        simpa using hs_tail
      linarith

    exact kraft_inequality_tight_nat_mono_fin (D := D) (hD := hD)
      (l := lNat) (h_mono := h_monoNat)
      (h_summable := h_summableNat) (h_sum := h_tsumNat)

  -- Restrict to Fin k
  let w : Fin k → List (Fin D) := fun i => wNat i.val

  refine ⟨w, ?_, ?_, ?_⟩
  · intro i j hij
    apply Fin.ext
    exact hwNat_inj hij

  · -- PrefixFree transfers to subsets: range w ⊆ range wNat
    have hsub : Set.range w ⊆ Set.range wNat := by
      intro a ha
      rcases ha with ⟨i, rfl⟩
      exact ⟨i.val, rfl⟩
    exact PrefixFree.mono hwNat_pf hsub

  · intro i
    -- lNat agrees with l on i < k
    simp [w, hwNat_len, lNat, ext_shift_eq]

/-- Converse of Kraft's inequality for monotone length sequences, for any finite alphabet.

Given a monotone `l : ℕ → ℕ` with summable Kraft sum ≤ 1 over an alphabet of size `|α| ≥ 2`,
there exists a prefix-free code with the given length function.

Note: Requires `Nontrivial α` (i.e., `|α| ≥ 2`) since prefix-free codes require at least 2 symbols. -/
theorem kraft_inequality_tight_nat_mono_alpha {α : Type _} [DecidableEq α] [Fintype α] [Nontrivial α]
    (l : ℕ → ℕ) (h_mono : Monotone l)
    (h_summable : Summable (fun i => (1 / Fintype.card α : ℝ) ^ l i))
    (h_sum : ∑' i, (1 / Fintype.card α : ℝ) ^ l i ≤ 1) :
    ∃ w : ℕ → List α,
      Function.Injective w ∧
      Kraft.PrefixFree (Set.range w) ∧
      (∀ i, (w i).length = l i) := by
  have hcard : 1 < Fintype.card α := Fintype.one_lt_card
  -- Get the Fin D version
  obtain ⟨w_fin, h_inj_fin, h_pf_fin, h_len_fin⟩ :=
    kraft_inequality_tight_nat_mono_fin (Fintype.card α) hcard l h_mono h_summable h_sum
  -- Map through the equivalence
  let e := (Fintype.equivFin α).symm
  let w : ℕ → List α := fun n => (w_fin n).map e
  have he_inj : Function.Injective e := Equiv.injective _
  refine ⟨w, ?_, ?_, ?_⟩
  · -- Injectivity
    intro n m hnm
    have : w_fin n = w_fin m := List.map_injective_iff.mpr he_inj hnm
    exact h_inj_fin this
  · -- Prefix-freeness
    intro a ⟨n, qn⟩ b ⟨m, qm⟩ hpre
    subst a b
    have h_pre_fin : w_fin n <+: w_fin m := (List.IsPrefix.map_iff he_inj).mp hpre
    have h_eq_fin : w_fin n = w_fin m :=
      h_pf_fin (w_fin n) ⟨n, rfl⟩ (w_fin m) ⟨m, rfl⟩ h_pre_fin
    simp [w, h_eq_fin]
  · -- Length preservation
    intro i
    simp [w, h_len_fin]

/-- Extends a length function on `Fin k` to all of `ℕ`, preserving monotonicity.

For `i < k`, returns `l i`. For `i ≥ k`, returns `l(k-1) + (i - k + 1)`. -/
def l_ext {k : ℕ} (l : Fin k → ℕ) (hk : k ≠ 0) (i : ℕ) : ℕ :=
  if h : i < k then l ⟨i, h⟩ else l ⟨k - 1, by omega⟩ + (i - k + 1)

/-- `l_ext` agrees with `l` on `Fin k`. -/
lemma l_ext_eq {k : ℕ} (l : Fin k → ℕ) (hk : k ≠ 0) (i : Fin k) :
    l_ext l hk i = l i := by
      unfold Kraft.l_ext
      simp_all only [Fin.is_lt, ↓reduceDIte, Fin.eta]

/-- `l_ext` is monotone when `l` is monotone. -/
lemma l_ext_monotone {k : ℕ} (l : Fin k → ℕ) (h_mono : Monotone l) (hk : k ≠ 0) :
    Monotone (l_ext l hk) := by
      -- Let's prove the monotonicity of `l_ext` by considering different cases.
      intro i j hij
      simp [Kraft.l_ext] at *
      split_ifs <;> try omega
      · exact h_mono hij
      · exact le_add_of_le_of_nonneg (h_mono (Nat.le_pred_of_lt ‹_›)) (Nat.zero_le _)

lemma kraft_inequality_tight_finite_mono_alpha
    {α : Type _} [Fintype α] [Nontrivial α]
    {k : ℕ} (l : Fin k → ℕ) (h_mono : Monotone l)
    (h_sum : ∑ i, (1 / Fintype.card α : ℝ) ^ l i < 1) :
    ∃ w : Fin k → List α,
      Function.Injective w ∧
      Kraft.PrefixFree (Set.range w) ∧
      ∀ i, (w i).length = l i := by
  let D : ℕ := Fintype.card α
  have hD' : 1 < D := by
    simpa [D] using (Fintype.one_lt_card_iff_nontrivial.mpr ‹Nontrivial α›)

  -- code over Fin D (this is your finite-index lemma, NOT the ℕ-index one)
  obtain ⟨wD, hwD_inj, hwD_pf, hwD_len⟩ :=
    kraft_inequality_tight_fin_lt
      (D := D) (hD := hD') (l := l) h_mono (by simpa [D] using h_sum)

  -- transport alphabet Fin D -> α
  let e : Fin D ≃ α := (Fintype.equivFin α).symm
  let w : Fin k → List α := fun i => (wD i).map e

  refine ⟨w, ?_, ?_, ?_⟩

  · -- injective: apply map e.symm to hij : w i = w j, then simp-cancel
    intro i j hij
    apply hwD_inj
    -- map back to Fin D on both sides
    have hij' : List.map e.symm (w i) = List.map e.symm (w j) :=
      congrArg (List.map e.symm) hij
    -- unfold w and cancel e.symm ∘ e
    -- (w i) = map e (wD i)
    simpa [w, List.map_map, Function.comp] using hij'

  · -- prefixfree: pull prefix back through map_iff, then use hwD_pf
    intro a ha b hb hpre
    rcases ha with ⟨i, rfl⟩
    rcases hb with ⟨j, rfl⟩
    have hpre' : wD i <+: wD j := by
      -- hpre : map e (wD i) <+: map e (wD j)
      -- use injectivity of e to pull it back
      simpa [w] using (List.IsPrefix.map_iff e.injective).1 hpre
    have : wD i = wD j :=
      hwD_pf (wD i) ⟨i, rfl⟩ (wD j) ⟨j, rfl⟩ hpre'
    have : i = j := hwD_inj this
    subst this
    rfl

  · -- lengths
    intro i
    simp [w, hwD_len i]

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
lemma exists_equiv_nat_monotone_of_infinite_gen {I : Type _} [Infinite I] (D : ℕ) (hD : 1 < D) (l : I → ℕ)
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

/-- An infinite index type with summable Kraft sum can be reordered to make lengths monotone.

This reduces the infinite case to the monotone case by using `kraftRank` to enumerate
elements in increasing order of length. -/
lemma exists_equiv_nat_monotone_of_infinite {I : Type _} [Infinite I] (l : I → ℕ)
    (h_summable : Summable (fun i => (1 / 2 : ℝ) ^ l i)) :
    ∃ e : ℕ ≃ I, Monotone (l ∘ e) :=
  exists_equiv_nat_monotone_of_infinite_gen 2 (by norm_num) l h_summable

/-- Any finite type can be sorted by a function to ℕ.

Given a fintype `I` and a function `l : I → ℕ`, produces an equivalence
`e : Fin (card I) ≃ I` such that `l ∘ e` is monotone (i.e., maps increasing
indices to non-decreasing length values). Uses insertion sort internally. -/
lemma exists_equiv_fin_monotone {I : Type _} [Fintype I] (l : I → ℕ) :
    ∃ e : Fin (Fintype.card I) ≃ I, Monotone (l ∘ e) := by
      have h_order_iso : ∃ (e : Fin (Fintype.card I) ≃ I), ∀ i j, i ≤ j → l (e i) ≤ l (e j) := by
        -- By definition of `Finset.sort`, we can obtain a sorted list of elements from `I` based on `l`.
        obtain ⟨sorted_list, h_sorted⟩ : ∃ sorted_list : List I, List.Pairwise (fun x y => l x ≤ l y) sorted_list ∧ List.length sorted_list = Fintype.card I ∧ List.Nodup sorted_list ∧ ∀ x ∈ sorted_list, x ∈ Finset.univ := by
          have h_insertion_sort : ∀ {xs : List I}, List.Nodup xs → ∃ sorted_list : List I, List.Pairwise (fun x y => l x ≤ l y) sorted_list ∧ List.length sorted_list = List.length xs ∧ List.Nodup sorted_list ∧ ∀ x ∈ sorted_list, x ∈ xs := by
            have h_insertion_sort : ∀ {xs : List I}, List.Nodup xs → ∃ sorted_list : List I, List.Pairwise (fun x y => l x ≤ l y) sorted_list ∧ List.length sorted_list = List.length xs ∧ List.Nodup sorted_list ∧ ∀ x ∈ sorted_list, x ∈ xs := by
              intro xs h_nodup
              exact ⟨List.insertionSort (fun x y => l x ≤ l y) xs, by
                convert List.pairwise_insertionSort _ _
                · exact ⟨ fun x y => le_total _ _ ⟩
                · exact ⟨ fun x y z hxy hyz => le_trans hxy hyz ⟩, by
                exact List.length_insertionSort (fun x y ↦ l x ≤ l y) xs, by
                exact List.Perm.nodup_iff (List.perm_insertionSort _ _) |>.2 h_nodup, by
                exact fun x hx => List.mem_insertionSort (fun x y => l x ≤ l y) |>.1 hx⟩
            assumption
          simpa using h_insertion_sort (Finset.nodup_toList Finset.univ)
        have h_equiv : ∃ e : Fin (Fintype.card I) ≃ I, ∀ i, e i = sorted_list[i] := by
          have h_equiv : Function.Bijective (fun i : Fin (Fintype.card I) => sorted_list[i]) := by
            have h_equiv : Function.Injective (fun i : Fin (Fintype.card I) => sorted_list[i]) := by
              intro i j hij
              have := List.nodup_iff_injective_get.mp h_sorted.2.2.1
              exact Fin.ext <| by simpa [h_sorted.2.1] using this hij
            have := Fintype.bijective_iff_injective_and_card (fun i : Fin (Fintype.card I) => sorted_list[i])
            simp_all only [Fin.getElem_fin, Multiset.bijective_iff_map_univ_eq_univ, Fin.univ_val_map, Fintype.card_fin, and_self, iff_true]
          exact ⟨ Equiv.ofBijective _ h_equiv, fun i => rfl ⟩
        obtain ⟨ e, he ⟩ := h_equiv
        refine' ⟨ e, fun i j hij => _ ⟩
        have := List.pairwise_iff_get.mp h_sorted.1
        cases lt_or_eq_of_le hij
        · simp_all only []
          exact this ⟨ i, by linarith [Fin.is_lt i, Fin.is_lt j] ⟩ ⟨ j, by linarith [Fin.is_lt i, Fin.is_lt j] ⟩ ‹_›
        · simp_all only [Fin.getElem_fin, le_refl]
      exact ⟨ h_order_iso.choose, fun i j hij => h_order_iso.choose_spec i j hij ⟩

/-- **Converse of Kraft's Inequality** (infinite case).

For any index set `I` (finite or infinite) and length function `l : I → ℕ`,
if `∑' i, 2^{-l(i)} ≤ 1`, then there exists an injective prefix-free code
`w : I → List Bool` with the prescribed lengths.

The proof handles two cases:
- **Finite case**: Sort indices by length and apply `kraft_inequality_tight_finite_mono`
- **Infinite case**: Use equivalence with ℕ and apply `kraft_inequality_tight_nat_mono` -/
theorem kraft_inequality_tight_infinite {I : Type _} (l : I → ℕ)
    (h_summable : Summable (fun i ↦ (1 / 2 : ℝ) ^ l i))
    (h_sum : ∑' i, (1 / 2 : ℝ) ^ l i ≤ 1) :
    ∃ w : I → List Bool,
      Function.Injective w ∧
      PrefixFree (Set.range w) ∧
      ∀ i, (w i).length = l i := by
  by_cases h_finite : Finite I
  · haveI := Fintype.ofFinite I
    -- By `exists_equiv_fin_monotone`, there exists an equivalence `e : Fin (card I) ≃ I` such that `l ∘ e` is monotone.
    obtain ⟨e, he⟩ : ∃ e : Fin (Fintype.card I) ≃ I, Monotone (l ∘ e) := by
      exact exists_equiv_fin_monotone l
    -- By `kraft_inequality_tight_finite_mono`, there exists `w' : Fin (card I) → List Bool` satisfying the conditions for `l ∘ e`.
    obtain ⟨w', hw'⟩ : ∃ w' : Fin (Fintype.card I) → List Bool, Function.Injective w' ∧ Kraft.PrefixFree (Set.range w') ∧ ∀ i, (w' i).length = l (e i) := by
      have h_sum_eq : ∑ i, (1 / 2 : ℝ) ^ (l (e i)) ≤ 1 := by
        convert h_sum using 1
        rw [tsum_fintype, ← Equiv.sum_comp e]
      exact kraft_inequality_tight_finite_mono (fun i ↦ l (e i)) he h_sum_eq
    refine' ⟨ w' ∘ e.symm, _, _, _ ⟩
    · simp_all only [Function.Injective]
      exact fun a₁ a₂ h => e.symm.injective (hw'.1 h)
    · simp_all only [Function.Injective, EquivLike.range_comp]
    · simp_all only [Function.comp_apply, Equiv.apply_symm_apply, implies_true]
  · have h_equiv : ∃ e : ℕ ≃ I, Monotone (l ∘ e) := by
      convert exists_equiv_nat_monotone_of_infinite l h_summable using 1
      simpa using h_finite
    obtain ⟨ e, he ⟩ := h_equiv
    have h_exists_w : ∃ w : ℕ → List Bool, Function.Injective w ∧ Kraft.PrefixFree (Set.range w) ∧ ∀ i, (w i).length = l (e i) := by
      have h_exists_w_1 : ∑' i : ℕ, (1 / 2 : ℝ) ^ l (e i) ≤ 1 := by
        convert h_sum using 1
        conv_rhs => rw [← Equiv.tsum_eq e]
      have h_exists_w : Summable (fun i : ℕ => (1 / 2 : ℝ) ^ l (e i)) := by
        convert h_summable.comp_injective e.injective using 1
      exact kraft_inequality_tight_nat_mono_alpha (fun i ↦ l (e i)) he h_exists_w h_exists_w_1
    obtain ⟨ w, hw₁, hw₂, hw₃ ⟩ := h_exists_w
    refine' ⟨ fun i => w (e.symm i), _, _, _ ⟩
    · exact hw₁.comp e.symm.injective
    · intro x hx y hy hxy
      simp_all only [one_div, inv_pow, not_finite_iff_infinite, Set.mem_range]
      obtain ⟨w_1, h⟩ := hx
      obtain ⟨w_2, h_1⟩ := hy
      subst h h_1
      apply hw₂
      · simp_all only [Set.mem_range, exists_apply_eq_apply]
      · simp_all only [Set.mem_range, exists_apply_eq_apply]
      · simp_all only
    · intro i
      simp_all only [one_div, inv_pow, not_finite_iff_infinite, Equiv.apply_symm_apply]

variable {α : Type _} [DecidableEq α] [Fintype α] [Nontrivial α]

/-- **Converse of Kraft's Inequality** (general alphabet, any index set).

For any index set `I` (finite or infinite), any finite alphabet `α` with `|α| ≥ 2`,
and length function `l : I → ℕ`, if `∑' i, |α|^{-l(i)} ≤ 1`, then there exists an
injective prefix-free code `w : I → List α` with the prescribed lengths.

Requires `Nontrivial α` (i.e., `|α| ≥ 2`) since prefix-free codes need at least 2 symbols. -/
theorem kraft_inequality_tight_infinite_alpha
    {I : Type _} (l : I → ℕ)
    (h_summable : Summable (fun i ↦ (1 / Fintype.card α : ℝ) ^ l i))
    (h_sum : ∑' i, (1 / Fintype.card α : ℝ) ^ l i ≤ 1) :
    ∃ w : I → List α,
      Function.Injective w ∧
      PrefixFree (Set.range w) ∧
      ∀ i, (w i).length = l i := by
  have hcard : 1 < Fintype.card α := Fintype.one_lt_card
  by_cases h_finite : Finite I
  · haveI := Fintype.ofFinite I
    -- By `exists_equiv_fin_monotone`, there exists an equivalence `e : Fin (card I) ≃ I` such that `l ∘ e` is monotone.
    obtain ⟨e, he⟩ : ∃ e : Fin (Fintype.card I) ≃ I, Monotone (l ∘ e) :=
      exists_equiv_fin_monotone l
    -- By `kraft_inequality_tight_finite_mono_alpha`, there exists `w' : Fin (card I) → List α`
    obtain ⟨w', hw'_inj, hw'_pf, hw'_len⟩ := kraft_inequality_tight_finite_mono_alpha
      (fun i ↦ l (e i)) he (by convert h_sum using 1; rw [tsum_fintype, ← Equiv.sum_comp e])
    refine ⟨w' ∘ e.symm, ?_, ?_, ?_⟩
    · exact hw'_inj.comp e.symm.injective
    · simp only [EquivLike.range_comp]
      exact hw'_pf
    · intro i
      simp [hw'_len]
  · have h_equiv : ∃ e : ℕ ≃ I, Monotone (l ∘ e) := by
      have h_inf : Infinite I := not_finite_iff_infinite.mp h_finite
      exact exists_equiv_nat_monotone_of_infinite_gen (Fintype.card α) hcard l h_summable
    obtain ⟨e, he⟩ := h_equiv
    have h_sum' : ∑' i : ℕ, (1 / Fintype.card α : ℝ) ^ l (e i) ≤ 1 := by
      convert h_sum using 1
      conv_rhs => rw [← Equiv.tsum_eq e]
    have h_summable' : Summable (fun i : ℕ => (1 / Fintype.card α : ℝ) ^ l (e i)) :=
      h_summable.comp_injective e.injective
    obtain ⟨w, hw_inj, hw_pf, hw_len⟩ :=
      kraft_inequality_tight_nat_mono_alpha (fun i ↦ l (e i)) he h_summable' h_sum'
    refine ⟨fun i => w (e.symm i), ?_, ?_, ?_⟩
    · exact hw_inj.comp e.symm.injective
    · intro x hx y hy hxy
      obtain ⟨i, rfl⟩ := hx
      obtain ⟨j, rfl⟩ := hy
      exact hw_pf (w (e.symm i)) ⟨e.symm i, rfl⟩ (w (e.symm j)) ⟨e.symm j, rfl⟩ hxy
    · intro i
      simp [hw_len]

theorem kraft_tight_of_arity
  (D : ℕ) (hD : 1 < D)
  {α : Type _} [DecidableEq α]
  (ι : Fin D ↪ α)                     -- an embedding of D symbols into α
  {I : Type _} (l : I → ℕ)
  (h_summable : Summable (fun i => (1 / D : ℝ) ^ l i))
  (h_sum : ∑' i, (1 / D : ℝ) ^ l i ≤ 1) :
  ∃ w : I → List α,
    Function.Injective w ∧
    PrefixFree (Set.range w) ∧
    ∀ i, (w i).length = l i := sorry

end Kraft
