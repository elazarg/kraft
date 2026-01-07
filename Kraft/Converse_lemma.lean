import Mathlib.Tactic.Linarith

import Kraft.PrefixFree

open BigOperators

/-!
  # Converse of Kraft's Inequality
-/

/-- Sum decomposition at a concrete successor index. -/
lemma sum_take_succ_eq (ws : List ℕ) (n : ℕ) (hn : n < ws.length) :
    (ws.take (n+1)).sum = (ws.take n).sum + ws.get ⟨n, hn⟩ := by
  -- `take (n+1)` is `take n` plus the nth element
  have ht : ws.take (n+1) = ws.take n ++ [ws.get ⟨n, hn⟩] := by simp
  -- sum both sides
  rw [ht, List.sum_append]
  simp

/--
If `0 < k` and `k ≤ ws.length`, then
`(ws.take k).sum = (ws.take (k-1)).sum + ws.get ⟨k-1, _⟩`.

This is the canonical "S_k = S_{k-1} + w_{k-1}" step.
-/
lemma sum_take_pred_add_get (ws : List ℕ) (k : ℕ)
    (hk0 : 0 < k) (hklen : k ≤ ws.length) :
    (ws.take k).sum =
      (ws.take (k-1)).sum + ws.get ⟨k-1, by
        exact Nat.lt_of_lt_of_le (Nat.pred_lt (ne_of_gt hk0)) hklen
      ⟩ := by
  cases k with
  | zero =>
      cases (Nat.lt_asymm hk0 hk0)   -- impossible
  | succ n =>
      have hn : n < ws.length :=
        Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hklen
      -- `(succ n) - 1 = n` so the goal matches `sum_take_succ_eq`
      simpa using (sum_take_succ_eq ws n hn)

lemma find_prefix_le_length (cap : ℕ) (ws : List ℕ)
    (h_ex : ∃ k, cap ≤ (ws.take k).sum) :
    Nat.find h_ex ≤ ws.length := by
  -- show P_len : cap ≤ (ws.take ws.length).sum
  have P_len : cap ≤ (ws.take ws.length).sum := by
    rcases h_ex with ⟨k0, hk0⟩
    have h_take_le_sum : (ws.take k0).sum ≤ ws.sum := by
      -- same take/drop trick
      have hsplit : (ws.take k0).sum + (ws.drop k0).sum = ws.sum := by simp
      have hle : (ws.take k0).sum ≤ (ws.take k0).sum + (ws.drop k0).sum :=
        Nat.le_add_right _ _
      simpa [hsplit] using hle
    have : cap ≤ ws.sum := le_trans hk0 h_take_le_sum
    simpa [List.take_length] using this

  by_contra h
  have hkgt : ws.length < Nat.find h_ex := Nat.lt_of_not_ge h
  exact (Nat.find_min h_ex hkgt) P_len

/--
If `cap > 0` and some prefix reaches `cap`, then the minimal prefix index is positive.
-/
lemma find_prefix_pos (cap : ℕ) (ws : List ℕ)
    (hcap : 0 < cap)
    (h_ex : ∃ k, cap ≤ (ws.take k).sum) :
    0 < Nat.find h_ex := by
  by_contra hk0
  have hk : Nat.find h_ex = 0 := Nat.eq_zero_of_not_pos hk0
  -- But `Nat.find_spec` says the found index reaches `cap`.
  have hspec : cap ≤ (ws.take (Nat.find h_ex)).sum := Nat.find_spec h_ex
  -- Rewrite with hk; `take 0` sum is 0, contradicting `cap > 0`.
  have : cap ≤ 0 := by simpa [hk] using hspec
  exact (Nat.ne_of_gt hcap) (Nat.eq_zero_of_le_zero this)

structure PrefixSplit (cap : ℕ) (ws : List ℕ) where
  k : ℕ
  hk_pos : 0 < k
  hk_len : k ≤ ws.length
  hk1_lt_len : k - 1 < ws.length
  h_decomp :
    (ws.take k).sum
      = (ws.take (k-1)).sum + ws.get ⟨k-1, hk1_lt_len⟩
  h_prev_lt : (ws.take (k-1)).sum < cap
  h_at_k :
    cap ≤ (ws.take (k-1)).sum + ws.get ⟨k-1, hk1_lt_len⟩

namespace PrefixSplit
def S_prev {cap ws} (ps : PrefixSplit cap ws) : ℕ := (ws.take (ps.k-1)).sum
def w_last {cap ws} (ps : PrefixSplit cap ws) : ℕ := ws.get ⟨ps.k-1, ps.hk1_lt_len⟩

@[simp] lemma S_prev_def {cap ws} (ps : PrefixSplit cap ws) :
  ps.S_prev = (ws.take (ps.k-1)).sum := rfl

@[simp] lemma w_last_def {cap ws} (ps : PrefixSplit cap ws) :
  ps.w_last = ws.get ⟨ps.k-1, ps.hk1_lt_len⟩ := rfl

end PrefixSplit

/--
The "One-Stop Shop" for prefix splitting.
-/
def find_prefix_split_spec (cap : ℕ) (ws : List ℕ)
    (hcap : 0 < cap) (h_ex : ∃ k, cap ≤ (ws.take k).sum) :
    PrefixSplit cap ws := by
  let k := Nat.find h_ex
  have hk_pos : 0 < k := find_prefix_pos cap ws hcap h_ex
  have hk_len : k ≤ ws.length := find_prefix_le_length cap ws h_ex
  have hk1_lt_len : k - 1 < ws.length :=
    Nat.lt_of_lt_of_le (Nat.pred_lt (ne_of_gt hk_pos)) hk_len

  have h_decomp :
      (ws.take k).sum
        = (ws.take (k-1)).sum + ws.get ⟨k-1, hk1_lt_len⟩ := by
    simpa using (sum_take_pred_add_get ws k hk_pos hk_len)

  have h_take_ge : cap ≤ (ws.take k).sum := Nat.find_spec h_ex

  have h_prev_lt : (ws.take (k-1)).sum < cap := by
    have hk1_lt : k - 1 < k := Nat.pred_lt (ne_of_gt hk_pos)
    have : ¬ cap ≤ (ws.take (k - 1)).sum := by
      -- Nat.find_min gives ¬P (k-1) with P j := cap ≤ sum (take j)
      simpa [k] using (Nat.find_min h_ex hk1_lt)
    exact Nat.lt_of_not_ge this

  have h_at_k :
      cap ≤ (ws.take (k-1)).sum + ws.get ⟨k-1, hk1_lt_len⟩ := by
    simpa [h_decomp] using h_take_ge

  exact {
    k := k
    hk_pos := hk_pos
    hk_len := hk_len
    hk1_lt_len := hk1_lt_len
    h_decomp := h_decomp
    h_prev_lt := h_prev_lt
    h_at_k := h_at_k
  }

/--
  Helper 3: The "Gap" Logic.
  If w divides S and T, and S < T ≤ S + w, then S + w = T.
  (In our case T = 2^n).
-/
lemma exact_fit_logic (S w T : ℕ)
    (h_less : S < T)
    (h_upper : T ≤ S + w)
    (h_dvd_S : w ∣ S)
    (h_dvd_T : w ∣ T) :
    S + w = T := by
  have h_dvd_diff : w ∣ (T - S) := Nat.dvd_sub h_dvd_T h_dvd_S
  have h_gap_le : w ≤ T - S :=
    Nat.le_of_dvd (Nat.sub_pos_of_lt h_less) h_dvd_diff

  apply le_antisymm
  · rw [Nat.add_comm]; exact Nat.add_le_of_le_sub (le_of_lt h_less) h_gap_le
  · exact h_upper

/--
In a non-increasing list of powers of two, later elements divide earlier ones.
If `i < k`, then `ws[k] ∣ ws[i]`.
-/
lemma pow2_chain_dvd_of_lt (ws : List ℕ)
    (h_chain : ws.IsChain (· ≥ ·))
    (h_pow2 : ∀ w ∈ ws, ∃ j, w = 2^j) :
    ∀ {i k} (hi : i < ws.length) (hk : k < ws.length),
      i < k  → ws.get ⟨k, hk⟩ ∣ ws.get ⟨i, hi⟩ := by
  intro i k hi hk hik

  have h_pairwise : ws.Pairwise (· ≥ ·) :=
    List.isChain_iff_pairwise.mp h_chain

  -- This uses `hik` in the *intended* place: i < k ⇒ ws[i] ≥ ws[k]
  have h_ge : ws.get ⟨k, hk⟩ ≤ ws.get ⟨i, hi⟩ :=
    List.pairwise_iff_getElem.mp h_pairwise i k hi hk hik

  rcases h_pow2 (ws.get ⟨k, hk⟩) (List.get_mem ws ⟨k, hk⟩) with ⟨j, hj⟩
  rcases h_pow2 (ws.get ⟨i, hi⟩) (List.get_mem ws ⟨i, hi⟩) with ⟨ji, hji⟩
  rw [hj, hji]

  -- Turn `ws[i] ≥ ws[k]` into `2^ji ≥ 2^j`, then into `j ≤ ji`
  have hj_le : j ≤ ji := by
    have : 2^j ≤ 2^ji := by omega
    -- use monotonicity in exponent
    exact (Nat.pow_le_pow_iff_right (by decide)).1 this

  have hdiv : 2^j ∣ 2^ji :=
    (Nat.pow_dvd_pow_iff_le_right (by decide)).2 hj_le

  simpa [hj, hji] using hdiv


/-- Helper: If every element in a list is divisible by k, their sum is divisible by k. -/
lemma sum_dvd_of_forall_dvd {k : ℕ} {L : List ℕ} (h : ∀ x ∈ L, k ∣ x) : k ∣ L.sum := by
  induction L with
  | nil => simp
  | cons head tail ih =>
    simp
    apply Nat.dvd_add
    · apply h; simp
    · apply ih; intro x hx; apply h; simp [hx]

/--
In a non-increasing dyadic list, `ws[k]` divides the sum of the prefix `take k`.
-/
lemma pow2_chain_dvd_prefix_sum (ws : List ℕ)
    (h_chain : ws.IsChain (· ≥ ·))
    (h_pow2 : ∀ w ∈ ws, ∃ j, w = 2^j) :
    ∀ k (hk : k < ws.length),
      ws.get ⟨k, hk⟩ ∣ (ws.take k).sum := by
  intro k hk
  apply sum_dvd_of_forall_dvd
  intro x hx
  -- x is some ws[i] with i < k (and i < length)
  rcases (List.mem_take_iff_getElem.mp hx) with ⟨i, hi, rfl⟩
  have hi_lt_k : i < k := (lt_min_iff.mp hi).1
  have hi_lt_len : i < ws.length := (lt_min_iff.mp hi).2
  -- apply lemma 1
  simpa using (pow2_chain_dvd_of_lt ws h_chain h_pow2 hi_lt_len hk hi_lt_k)

lemma find_prefix_exact_of_dyadic_pow2 (n : ℕ) (ws : List ℕ)
    (h_ex : ∃ k, 2^n ≤ (ws.take k).sum)
    (h_chain : ws.IsChain (· ≥ ·))
    (h_pow2 : ∀ w ∈ ws, ∃ j, w = 2^j)
    (h_bounded : ∀ w ∈ ws, w ≤ 2^n) :
    let k := Nat.find h_ex
    (ws.take k).sum = 2^n := by
  intro k

  have hcap : 0 < 2^n := Nat.pow_pos (by decide)

  let ps : PrefixSplit (2^n) ws := find_prefix_split_spec (2^n) ws hcap h_ex

  -- w_last ∣ S_prev
  have h_dvd_prev : ps.w_last ∣ ps.S_prev := by
    -- pow2_chain_dvd_prefix_sum returns: w_last ∣ (take (k-1)).sum
    simpa using (pow2_chain_dvd_prefix_sum ws h_chain h_pow2 (ps.k - 1) ps.hk1_lt_len)

  -- w_last ∣ 2^n
  have h_dvd_cap : ps.w_last ∣ 2^n := by
    have hw_mem : ps.w_last ∈ ws := by simp
    rcases h_pow2 ps.w_last hw_mem with ⟨j, hj⟩
    have hw_le : ps.w_last ≤ 2^n := h_bounded _ hw_mem
    have h_le : 2^j ≤ 2^n := by linarith
    have hj_le : j ≤ n := (Nat.pow_le_pow_iff_right (by decide)).1 h_le
    have : 2^j ∣ 2^n := (Nat.pow_dvd_pow_iff_le_right (by decide)).2 hj_le
    simp_all

  -- exact fit: S_prev + w_last = 2^n
  have h_gap : ps.S_prev + ps.w_last = 2^n :=
    exact_fit_logic
      ps.S_prev
      ps.w_last
      (2^n)
      ps.h_prev_lt
      ps.h_at_k
      h_dvd_prev
      h_dvd_cap

  have h_exact : (ws.take ps.k).sum = 2^n := by
    calc
      (ws.take ps.k).sum
          = ps.S_prev + ps.w_last := by
              simpa using ps.h_decomp
      _ = 2^n := h_gap

  -- `k` is the local `let k := Nat.find h_ex`, and `ps.k` is definitionaly `Nat.find h_ex`
  simpa [ps, k] using h_exact

/-! ## 1. The Splitting Logic (Arithmetic Core) -/

lemma le_foldr_max (l : List ℕ) (x : ℕ) (hx : x ∈ l) :
    x ≤ l.foldr max 0 := by
  induction l with
  | nil => contradiction
  | cons head tail ih =>
    rw [List.foldr_cons]
    simp only [List.mem_cons] at hx
    rcases hx with rfl | h_in_tail
    · exact Nat.le_max_left _ _
    · exact le_trans (ih h_in_tail) (Nat.le_max_right _ _)


lemma scale_term (h l : ℕ) (hl : l ≤ h) :
    (2^h ) * (2^l)⁻¹ = (2^(h - l) : ℚ) := by
  -- 2^h = 2^l * 2^(h-l)
  have hpow : (2^h : ℚ) = (2^l) * (2^(h - l)) := by
    -- use h = l + (h-l)
    calc
      (2^h) = (2^(l + (h - l)) : ℚ) := by simp [Nat.add_sub_of_le hl]
      _ = (2^l ) * (2^(h - l) ) := by simp [pow_add]

  have hne : (2^l) ≠ 0 := by exact pow_ne_zero l (by norm_num)
  -- cancel 2^l
  calc
    (2^h ) * (2^l)⁻¹
        = ((2^l ) * (2^(h - l))) * (2^l )⁻¹ := by simp [hpow]
    _ = (2^l) * ((2^(h - l) : ℚ) * (2^l )⁻¹) := by simp [mul_assoc]
    _ = (2^l) * ((2^l)⁻¹ * (2^(h - l))) := by simp [mul_comm]
    _ = ((2^l) * (2^l)⁻¹) * (2^(h - l) ) := by simp
    _ = (2^(h - l) ) := by simp


/--
Scaling identity on a list: if every `l` in `lengths` satisfies `l ≤ h`, then

    (2^h) * Σ (2^l)⁻¹  =  Σ 2^(h-l)
-/
lemma scale_sum_eq (h : ℕ) (lengths : List ℕ)
    (h_bound : ∀ l ∈ lengths, l ≤ h) :
    (2^h : ℚ) * (lengths.map (fun l ↦ (2^l : ℚ)⁻¹)).sum
      = (lengths.map (fun l ↦ (2^(h - l) : ℚ))).sum := by
  induction lengths with
  | nil =>
      simp
  | cons a tl ih =>
      have ha : a ≤ h := h_bound a (by simp)
      have h_bound_tl : ∀ l ∈ tl, l ≤ h := by
        intro l hl
        exact h_bound l (by simp [hl])
      -- expand sums, distribute, rewrite the head term via `scale_term`, recurse
      simp [ih h_bound_tl, scale_term h a ha, mul_add]

/-- Cast a list-sum: `((∑ f) : ℚ) = ∑ (cast ∘ f)` -/
lemma rat_cast_sum_map {α : Type _} (xs : List α) (f : α → ℕ) :
    ((xs.map f).sum : ℚ) = (xs.map (fun x => (f x : ℚ))).sum := by
  induction xs with
  | nil =>
      simp
  | cons a xs ih =>
      -- sum_cons + cast_add
      simp [ih, Nat.cast_add]

/--
The "Kraft Equivalence":
The rational sum Σ 2^{-l} ≥ 1 is equivalent to the integer mass sum Σ 2^{h-l} ≥ 2^h.
-/
lemma kraft_sum_equiv_mass_sum (h : ℕ) (lengths : List ℕ) (hl : ∀ l ∈ lengths, l ≤ h) :
    (lengths.map (fun l ↦ (2^l : ℚ)⁻¹)).sum ≥ 1 ↔
    (lengths.map (fun l ↦ 2^(h - l))).sum ≥ 2^h := by
  simp only [ge_iff_le]
  rw [← Nat.cast_le (α := ℚ)]
  rw [rat_cast_sum_map lengths (fun l ↦ 2^(h - l))]
  simp
  rw [← scale_sum_eq h lengths hl]
  have hpos : (0 : ℚ) < 2^h := pow_pos (by norm_num) h
  constructor <;> intro he <;> nlinarith

theorem list_kraft_exact (lengths : List ℕ)
    (h_sorted : lengths.IsChain (· ≤ ·))
    (h_sum_ge_1 : (lengths.map (fun l ↦ (2^l : ℚ)⁻¹)).sum ≥ 1) :
    ∃ k, ((lengths.take k).map (fun l ↦ (2^l : ℚ)⁻¹)).sum = 1 := by
  let h := lengths.foldr max 0
  let target : ℕ := 2^h
  let weights : List ℕ := lengths.map (fun l ↦ 2^(h - l))

  -- 1. Bounds
  have h_bound : ∀ l ∈ lengths, l ≤ h := fun l hl ↦ le_foldr_max lengths l hl

  -- 2. Convert rational hypothesis to integer mass hypothesis (Using Helper)
  have h_mass_ge : weights.sum ≥ target := by
    rw [← kraft_sum_equiv_mass_sum h lengths h_bound]
    exact h_sum_ge_1

  -- 3. Run the exact fit logic on the integer weights
  have h_ex : ∃ k, target ≤ (weights.take k).sum :=
    ⟨weights.length, by simpa [List.take_length] using h_mass_ge⟩

  -- 4. Get the exact split point
  let k := Nat.find h_ex
  have h_int_exact : (weights.take k).sum = target :=
    have h_bounded : ∀ w ∈ weights, w ≤ target := by
      intro w hw
      rcases List.mem_map.1 hw with ⟨l, hl, rfl⟩
      exact Nat.pow_le_pow_of_le (by decide) (Nat.sub_le _ _)

    have h_pow2 : ∀ w ∈ weights, ∃ j, w = 2^j := by
      intro w hw
      rcases List.mem_map.1 hw with ⟨l, hl, rfl⟩; exact ⟨h - l, rfl⟩

    have h_weights_chain : weights.IsChain (· ≥ ·) := by
      dsimp [weights]
      refine List.isChain_map_of_isChain (f := fun l : ℕ => 2^(h - l)) (R := (· ≤ ·)) (S := (· ≥ ·)) ?_ h_sorted
      intro a b hab
      simpa [ge_iff_le] using Nat.pow_le_pow_of_le (by decide) (Nat.sub_le_sub_left hab h)

    find_prefix_exact_of_dyadic_pow2 h weights h_ex h_weights_chain h_pow2 h_bounded

  rw [← Nat.cast_inj (R := ℚ)] at h_int_exact

  refine ⟨k, ?_⟩

  have h_bound_take : ∀ l ∈ lengths.take k, l ≤ h :=
    fun l hl ↦ h_bound l (List.mem_of_mem_take hl)

  let prefSum : ℚ :=
    ((lengths.take k).map (fun l ↦ (2^l)⁻¹)).sum

  -- bounds for elements in take k
  have h_bound : ∀ l ∈ lengths, l ≤ h := by
    intro l hl
    exact le_foldr_max lengths l hl

  have hscale_take :
      (2^h : ℚ) * prefSum
        = ((lengths.take k).map (fun l ↦ (2^(h - l)))).sum := by
    -- just apply scale_sum_eq to the prefix list
    simpa [prefSum] using (scale_sum_eq h (lengths.take k) h_bound_take)

  have h_take_cast :
      ((weights.take k).sum : ℚ)
        = ((lengths.take k).map (fun l : ℕ => (2^(h - l)))).sum := by
    -- rewrite `weights.take k` to `(lengths.take k).map ...`
    have : weights.take k = (lengths.take k).map (fun l => 2^(h - l)) := by
      simp [weights, List.map_take]
    -- now cast-sum-map on the taken list
    simpa [this] using
      (rat_cast_sum_map (xs := lengths.take k) (f := fun l => 2^(h - l)))

  have hscaled_to_weights :
      (2^h) * prefSum = (weights.take k).sum := by
    calc
      (2^h) * prefSum
          = ((lengths.take k).map (fun l ↦ (2^(h - l)))).sum := hscale_take
      _   = ((weights.take k).sum) := by simpa using h_take_cast.symm

  have hEq : 2^h * prefSum = 2^h := by
    -- target = 2^h
    simpa [target] using (hscaled_to_weights.trans h_int_exact)

  have hne : (2^h : ℚ) ≠ 0 := by
    -- 2 ≠ 0 in ℚ
    exact pow_ne_zero h (by norm_num : (2 : ℚ) ≠ 0)

  -- cancel 2^h
  have : prefSum = 1 := by simp_all
  simpa [prefSum] using this

/-- If a list has no duplicates, summing over `toFinset` equals summing over the list. -/
lemma sum_toFinset_eq_sum_of_nodup {α β : Type _} [DecidableEq α] [AddCommMonoid β]
    (L : List α) (hL : L.Nodup) (f : α → β) :
    (∑ x ∈ L.toFinset, f x) = (L.map f).sum := by
  have hperm : (L.toFinset.toList).Perm L := by
    simp [L.toFinset_toList, hL]

  -- `∑ x in s, f x = (s.toList.map f).sum`
  -- so reduce to list-sums + perm invariance
  calc
    (∑ x ∈ L.toFinset, f x)
        = ((L.toFinset.toList).map f).sum := by simp
    _ = ((L.map f).sum) := by
          have : ((L.toFinset.toList).map f).Perm (L.map f) := hperm.map f
          simpa using this.sum_eq

/--
If `L` is a Nodup list, summing `f` over the Finset created from `L.take k`
is the same as summing `f` over the list `L.take k`.
-/
lemma sum_finset_take_eq_sum_list_take {α β : Type _} [DecidableEq α] [AddCommMonoid β]
    (L : List α) (hL : L.Nodup) (k : ℕ) (f : α → β) :
    ∑ x ∈ (L.take k).toFinset, f x = ((L.take k).map f).sum := by
  rw [sum_toFinset_eq_sum_of_nodup]
  exact hL.take

lemma take_toFinset_subset_of_perm {α : Type _} [DecidableEq α]
    {L1 L2 : List α} (p : L1.Perm L2) (k : ℕ) :
    (L1.take k).toFinset ⊆ L2.toFinset := by
  intro x hx
  -- turn membership in `toFinset` into membership in the list
  have hxL1 : x ∈ L1.take k := by
    simpa using (List.mem_toFinset.mp hx)
  have hxL1' : x ∈ L1 := List.mem_of_mem_take hxL1
  have hxL2 : x ∈ L2 := p.subset hxL1'
  -- back to finset membership
  simpa using (List.mem_toFinset.mpr hxL2)

lemma isChain_insertionSort {α : Type _} (r : α → α → Prop) [DecidableRel r] [IsTotal α r] [IsTrans α r]
    (L : List α) :
    (List.insertionSort r L).IsChain r := by
  -- library gives Pairwise
  have hpw : (List.insertionSort r L).Pairwise r := by
    simpa using (List.pairwise_insertionSort (r := r) (l := L))
  -- Pairwise -> IsChain
  exact hpw.isChain

/--
Lemma 3.1: Let I be a finite set and let l : I → ℕ satisfy ∑ 2^{-l(i)} ≥ 1.
There exists a subset S ⊆ I such that ∑_{i ∈ S} 2^{-l(i)} = 1.
-/
theorem lemma_3_1 {α : _} [DecidableEq α] (I : Finset α) (l : α → ℕ) :
    ∑ i ∈ I, (2 ^ l i : ℚ)⁻¹ ≥ 1 ->
    ∃ S ⊆ I, ∑ i ∈ S, (2 ^ l i : ℚ)⁻¹ = 1 := by
  intro hI

  -- 1) pick L = I.toList sorted by key l using mergeSort
  let r : α → α → Prop := fun a b => l a ≤ l b
  let L : List α := (I.toList).insertionSort r

  have h_chain : (L.map l).IsChain (· ≤ ·) := by
    -- Make the sorting assumptions *instances* (so simp/lemma search can use them)
    haveI htotal : IsTotal α r := ⟨by
      intro a b
      dsimp [r]
      exact le_total (l a) (l b)⟩
    haveI : IsTrans α r := ⟨by
      intro a b c hab hbc
      -- hab : l a ≤ l b, hbc : l b ≤ l c
      exact le_trans hab hbc⟩

    -- Pairwise -> IsChain (no transitivity needed for this step)
    have h_chain_r : L.IsChain r := by
      simpa [L] using (isChain_insertionSort r I.toList)

    -- Map the chain through `l`
    -- (this lemma lives in Mathlib.Data.List.Chain)
    refine List.isChain_map_of_isChain (f := l) (R := r) (S := (· ≤ ·)) ?_ h_chain_r
    intro a b hab
    simpa [r] using hab

  have p : L.Perm I.toList := by simpa [L] using (List.perm_insertionSort r I.toList)

  -- 2) turn finset hypothesis into list hypothesis on `L.map l`
  let f : ℕ → ℚ := fun n => (2^n : ℚ)⁻¹
  let g : α → ℚ := fun x => f (l x)

  have h_list :
      ((L.map l).map f).sum ≥ 1 := by
    -- (L.map l).map f = L.map (fun x => f (l x)) = L.map g
    have hI_toList : (I.toList.map g).sum ≥ 1 := by simpa
    have h_perm_sum : (L.map g).sum = (I.toList.map g).sum := by simpa using (p.map g).sum_eq
    have hL_sum_ge : (L.map g).sum ≥ 1 := by simpa [hI_toList, h_perm_sum]
    simpa [g, f, List.map_map, Function.comp] using hL_sum_ge

  have hLnodup : L.Nodup := by
    have : I.toList.Nodup := I.nodup_toList
    exact (p.nodup_iff).2 this

  -- 3) apply list lemma
  rcases list_kraft_exact (lengths := L.map l) h_chain h_list with ⟨k, hk⟩

  -- 4) define S
  let S : Finset α := (L.take k).toFinset
  refine ⟨S, ?_, ?_⟩

  · -- subset
    have hsub : (L.take k).toFinset ⊆ I.toList.toFinset :=
      take_toFinset_subset_of_perm (L1 := L) (L2 := I.toList) p k
    -- then rewrite `I.toList.toFinset` to `I`
    simpa using hsub
  · -- sum over S = 1
    rw [sum_finset_take_eq_sum_list_take L hLnodup k (fun x ↦ (2^(l x) )⁻¹)]
    -- The rest is just map/comp manipulation matching `hk`
    simpa [Function.comp] using hk
