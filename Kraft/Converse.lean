import Mathlib.Data.List.Sort
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.GCD.Basic

import Batteries.Data.List.Basic

import Kraft.PrefixFree

open BigOperators

/-!
  # Converse of Kraft's Inequality
-/

/--
`Nat.find` version of "first prefix whose sum reaches capacity".

If there exists *some* prefix whose sum is ≥ cap, then there is a *least* such prefix,
and every shorter prefix is strictly below cap.
-/
lemma exists_min_prefix_sum_ge (cap : ℕ) (ws : List ℕ)
    (h_ex : ∃ k, cap ≤ (ws.take k).sum) :
    ∃ k, cap ≤ (ws.take k).sum ∧ ∀ j < k, (ws.take j).sum < cap := by
  let P : ℕ → Prop := fun k => cap ≤ (ws.take k).sum
  have hP : ∃ k, P k := h_ex
  let k : ℕ := Nat.find hP
  refine ⟨k, ?_, ?_⟩
  · exact Nat.find_spec hP
  · intro j hj
    -- `Nat.find_min'` says any smaller index fails P
    have hmin : ¬ P j := Nat.find_min hP hj
    -- goal is `¬ (sum ≥ cap)`; rewrite `≥` as `≤` and unfold P
    simpa [P, ge_iff_le] using hmin

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

-- Helper: Mass of a list of lengths at a specific height h.
def mass (h : ℕ) (lengths : List ℕ) : ℕ :=
  (lengths.map (fun l => 2^(h - l))).sum

-- General disjointness for codes starting with different bits
lemma disjoint_cons {S1 S2 : Code} :
    Disjoint (S1.image (List.cons true)) (S2.image (List.cons false)) := by
  rw [Finset.disjoint_left]
  intro w h1 h2
  rw [Finset.mem_image] at h1 h2
  rcases h1 with ⟨w1, _, rfl⟩
  rcases h2 with ⟨w2, _, heads_distinct⟩
  simp at heads_distinct -- true = false contradiction

-- Prefix-free is preserved under 'cons b'
lemma prefixFree_cons (b : Bool) {S : Code} (h : PrefixFree S) :
    PrefixFree (S.image (List.cons b)) := by
  intro x y hx hy hpre
  rw [Finset.mem_image] at hx hy
  rcases hx with ⟨wx, hwx_in, rfl⟩
  rcases hy with ⟨wy, hwy_in, rfl⟩
  simp at *; exact h hwx_in hwy_in hpre

lemma prefixFree_union_cons {S1 S2 : Code}
    (h1 : PrefixFree S1) (h2 : PrefixFree S2) :
    PrefixFree ((S1.image (List.cons true)) ∪ (S2.image (List.cons false))) := by
  intro x y hx hy hpre
  rw [Finset.mem_union] at hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · apply prefixFree_cons true h1 hx hy hpre
  · rw [Finset.mem_image] at hx hy; rcases hx with ⟨_, _, rfl⟩; rcases hy with ⟨_, _, rfl⟩; simp at hpre
  · rw [Finset.mem_image] at hx hy; rcases hx with ⟨_, _, rfl⟩; rcases hy with ⟨_, _, rfl⟩; simp at hpre
  · apply prefixFree_cons false h2 hx hy hpre

-- Mass permutation invariance
lemma mass_perm {h : ℕ} {l1 l2 : List ℕ} (p : l1.Perm l2) :
    mass h l1 = mass h l2 := by
  dsimp [mass]
  apply List.Perm.sum_eq'
  · apply List.Perm.map _ p
  · apply List.pairwise_of_forall
    intro x y
    apply add_comm

/--
If some prefix of `ws` reaches `cap`, then the *least* such prefix index
(chosen by `Nat.find`) is ≤ `ws.length`.
-/
lemma find_prefix_le_length (cap : ℕ) (ws : List ℕ)
    (h_ex : ∃ k, cap ≤ (ws.take k).sum) :
    let P : ℕ → Prop := fun k => cap ≤ (ws.take k).sum
    let k : ℕ := Nat.find (show ∃ k, P k from h_ex)
    k ≤ ws.length := by
  intro P k

  -- First show: the full list satisfies P (i.e. `cap ≤ sum ws`)
  have P_len : P ws.length := by
    rcases h_ex with ⟨k0, hk0⟩

    -- (ws.take k0).sum ≤ ws.sum via take/drop decomposition
    have h_take_le_sum : (ws.take k0).sum ≤ ws.sum := by
      have hsplit : (ws.take k0).sum + (ws.drop k0).sum = ws.sum := by simp
      have hle : (ws.take k0).sum ≤ (ws.take k0).sum + (ws.drop k0).sum := Nat.le_add_right _ _
      simpa [hsplit] using hle

    have hcap_le_sum : cap ≤ ws.sum := le_trans hk0 h_take_le_sum
    -- rewrite ws.sum as (take length).sum
    simpa [P, List.take_length] using hcap_le_sum

  -- Now use `Nat.find_min` to rule out `k > ws.length`
  have hk_not_gt : ¬ k > ws.length := by
    intro hkgt
    have hnot : ¬ P ws.length :=
      Nat.find_min (show ∃ k, P k from h_ex) (by linarith)
    exact hnot P_len

  exact Nat.le_of_not_gt hk_not_gt

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

/--
Let `k` be the least index such that the prefix sum reaches `cap`.
If `cap > 0`, then:
- `0 < k`
- the previous prefix is strictly below `cap`
- the prefix at `k` reaches `cap`
- and `(k-1)` is a valid index into `ws` (i.e. `k-1 < ws.length`)
-/
lemma find_prefix_bounds (cap : ℕ) (ws : List ℕ)
    (hcap : 0 < cap)
    (h_ex : ∃ k, cap ≤ (ws.take k).sum) :
    let k := Nat.find h_ex
    0 < k ∧
    (ws.take (k-1)).sum < cap ∧
    cap ≤ (ws.take k).sum ∧
    k - 1 < ws.length := by
  intro k

  have hk_pos : 0 < k := by simpa [k] using (find_prefix_pos cap ws hcap h_ex)

  have hk_le_len : k ≤ ws.length := by simpa [k] using (find_prefix_le_length cap ws h_ex)

  have h_at_k : cap ≤ (ws.take k).sum := by simpa [k] using (Nat.find_spec h_ex)

  have h_prev_lt : (ws.take (k-1)).sum < cap := by
    -- minimality: any j < k fails cap ≤ sum(take j)
    have hnot : ¬ cap ≤ (ws.take (k-1)).sum := by
      -- need (k-1) < k
      have hk1_lt : k - 1 < k := Nat.pred_lt (ne_of_gt hk_pos)
      -- Nat.find_min gives ¬P (k-1)
      -- P j := cap ≤ sum(take j)
      exact Nat.find_min h_ex hk1_lt
    exact Nat.lt_of_not_ge hnot

  have hk1_lt_len : k - 1 < ws.length := by
    exact Nat.lt_of_lt_of_le (Nat.pred_lt (ne_of_gt hk_pos)) hk_le_len

  exact ⟨hk_pos, h_prev_lt, h_at_k, hk1_lt_len⟩


/-! ## 1. The Splitting Logic (Arithmetic Core) -/

/-- Divisibility helper for lists -/
lemma dvd_sum_of_dvd_forall {l : List ℕ} {k : ℕ} (h : ∀ x ∈ l, k ∣ x) : k ∣ l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp; apply Nat.dvd_add
    · exact h a List.mem_cons_self
    · exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx))

def splitIndex (capacity : ℕ) (weights : List ℕ) : ℕ :=
  (List.range (weights.length + 1)).find? (fun k => (weights.take k).sum ≥ capacity)
  |>.getD weights.length

/-- Specification for splitIndex behavior -/
lemma splitIndex_spec {cap : ℕ} {ws : List ℕ}
    (h_ex : ∃ k ≤ ws.length, cap ≤ (ws.take k).sum) :
    let k := splitIndex cap ws
    cap ≤ (ws.take k).sum ∧ ∀ j < k, (ws.take j).sum < cap := by
  intro k
  dsimp [k]
  rw [splitIndex]

  let range := List.range (ws.length + 1)
  have h_some : range.find? (fun k => cap ≤ (ws.take k).sum) ≠ none := by
    intro h_none
    rw [List.find?_eq_none] at h_none
    rcases h_ex with ⟨idx, h_len, h_sum⟩
    have h_mem : idx ∈ range := List.mem_range.2 (Nat.lt_succ_of_le h_len)
    specialize h_none idx h_mem
    simp [h_sum] at h_none

  match h_match : range.find? (fun k => cap ≤ (ws.take k).sum) with
  | none => contradiction
  | some k_found =>
    simp only [Option.getD_some]
    constructor
    · have h := List.find?_some h_match
      simp at h; exact h
    · intros j hj
      rcases (List.find?_eq_some_iff_getElem.mp h_match)
      simp_all only [not_le, List.find?_range_eq_some,
                     Bool.not_eq_eq_eq_not, Bool.not_true,
                     decide_eq_false_iff_not, range]

-- Lemma 3.1: The Perfect Split
lemma split_exact_of_dyadic
    (n : ℕ) (weights : List ℕ)
    (h_sorted : weights.IsChain (· ≥ ·))
    (h_pow2 : ∀ w ∈ weights, ∃ j, w = 2^j)
    (h_bounded : ∀ w ∈ weights, w ≤ 2^n)
    (h_sum_gt : weights.sum > 2^n) :
    (weights.take (splitIndex (2^n) weights)).sum = 2^n := by
  let cap := 2^n

  -- 1. Existence of valid split point
  have h_exists : ∃ k ≤ weights.length, cap ≤ (weights.take k).sum := by
    use weights.length; simp; apply le_of_lt h_sum_gt

  have spec := splitIndex_spec h_exists
  let k := splitIndex cap weights
  have h_le : cap ≤ (weights.take k).sum := spec.1
  have h_lt : ∀ j < k, (weights.take j).sum < cap := spec.2

  -- 2. k must be > 0
  have k_pos : 0 < k := by
    by_contra h_z
    -- Unfold cap to reveal contradiction
    simp_all [cap]

  -- 3. Decompose: S_k = S_{k-1} + w
  -- We define indices carefully to use getElem properties
  let idx_w := k - 1
  have h_idx_lt : idx_w < k := Nat.pred_lt (ne_of_gt k_pos)
  have h_idx_valid : idx_w < weights.length := by
      -- 1. We already know idx_w < k
      apply Nat.lt_of_lt_of_le h_idx_lt

      -- 2. We need to show k ≤ weights.length
      -- Unfold the definition to see the List.range bound
      dsimp [k, splitIndex]

      -- 3. Case analysis: did find? return a value or the default?
      match h_find : (List.range (weights.length + 1)).find? (fun i => cap ≤ (weights.take i).sum) with
      | none =>
        -- Default case: returns weights.length
        simp only [Option.getD_none]
        linarith
      | some index =>
        -- Found case: returns index
        simp only [Option.getD_some]
        -- Property: index must be in the range
        have h_mem := List.mem_of_find?_eq_some h_find
        rw [List.mem_range] at h_mem
        exact Nat.le_of_lt_succ h_mem

  let w := weights[idx_w]
  let S_prev := (weights.take idx_w).sum

  have h_decomp : (weights.take k).sum = S_prev + w := by
    subst S_prev w idx_w
    conv_lhs => rw [← Nat.sub_add_cancel k_pos]
    -- take (i+1) = take i ++ [l[i]?]
    rw [List.take_add_one,
        List.sum_append,
        List.getElem?_eq_getElem h_idx_valid]
    simp

  have h_prev_lt : S_prev < cap := h_lt idx_w h_idx_lt

  -- 4. Divisibility Argument
  rcases h_pow2 w (List.getElem_mem h_idx_valid) with ⟨j, _⟩

  have w_dvd_prev : 2^j ∣ S_prev := by
    apply List.dvd_sum
    intros x hx
    rcases h_pow2 x (List.mem_of_mem_take hx) with ⟨jx, rfl⟩

    have h_pairwise : weights.Pairwise (· ≥ ·) :=
      List.isChain_iff_pairwise.mp h_sorted

    -- Capture the equality h_eq_x : weights[i] = x
    rcases List.mem_take_iff_getElem.mp hx with ⟨i, hi_lt, h_eq_x⟩

    have hi_len : i < weights.length := Nat.lt_of_lt_of_le hi_lt (min_le_right _ _)
    have hi_idx : i < idx_w := Nat.lt_of_lt_of_le hi_lt (min_le_left _ _)

    have h_le : weights[idx_w] ≤ weights[i] :=
      List.pairwise_iff_getElem.mp h_pairwise i idx_w hi_len h_idx_valid hi_idx

    -- Rewrite weights[i] to x (which is 2^jx)

    -- Now h_le is effectively 2^j ≤ 2^jx (since weights[idx_w] is w is 2^j)
    -- We can apply divisibility directly without stripping exponents
    simp_all [cap, k, idx_w, S_prev, w]
    rw [Nat.pow_dvd_pow_iff_le_right (by decide)]
    rw [Nat.pow_le_pow_iff_right (by decide)] at h_le
    assumption

  have w_dvd_cap : 2^j ∣ cap := by
    have : weights[idx_w] ≤ 2 ^ n := h_bounded _ (List.getElem_mem h_idx_valid)
    have : 2^j ≤ 2^n := by linarith
    simp_all [cap, k, idx_w, S_prev, w]
    rw [Nat.pow_dvd_pow_iff_le_right (by decide)]
    rw [Nat.pow_le_pow_iff_right (by decide)] at this
    assumption

  -- 5. Contradiction
  have h_dvd_diff : 2^j ∣ (cap - S_prev) := Nat.dvd_sub w_dvd_cap w_dvd_prev
  have h_gap : 2^j ≤ cap - S_prev := Nat.le_of_dvd (Nat.sub_pos_of_lt h_prev_lt) h_dvd_diff

  -- 1. Prove S_prev + 2^j ≤ cap
  -- Nat.add_le_of_le_sub : m ≤ n → k ≤ n - m → k + m ≤ n
  -- We use m = S_prev, n = cap, k = 2^j. Result: 2^j + S_prev ≤ cap.
  have h_upper : S_prev + 2^j ≤ cap := by
    rw [Nat.add_comm]
    exact Nat.add_le_of_le_sub (le_of_lt h_prev_lt) h_gap

  -- 2. Align the goal and hypotheses

  -- Rewrite the goal: (take k).sum = 2^n  becomes  S_prev + 2^j = 2^n
  have h_le : cap ≤ (weights.take k).sum := spec.1
  rw [h_decomp]
  simp_all [cap, k, idx_w, S_prev, w]

  -- 3. Apply antisymmetry
  -- h_upper : S_prev + 2^j ≤ 2^n
  -- spec.1  : 2^n ≤ (take k).sum  ->  2^n ≤ S_prev + 2^j
  apply Nat.le_antisymm h_upper

  exact h_le

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
  "No Jump" Lemma: In the integers, you cannot jump over a multiple of k
  by adding k. If you start below T and add k to reach/exceed T,
  and both start and T are divisible by k, you must land on T exactly.
-/
lemma exact_hit_of_divisible_step (current target step : ℕ)
    (h_dvd_curr : step ∣ current)
    (h_dvd_targ : step ∣ target)
    (h_below : current < target)
    (h_above : target ≤ current + step) :
    current + step = target := by
  -- Proof: If strictly greater, we find an integer strictly between two integers.
  have h_dvd_diff : step ∣ (target - current) := Nat.dvd_sub h_dvd_targ h_dvd_curr
  have h_step_le : step ≤ target - current := Nat.le_of_dvd (Nat.sub_pos_of_lt h_below) h_dvd_diff
  -- current + step ≤ current + (target - current) = target
  omega

/--
  Divisibility Chain:
  If lengths are non-decreasing (sorted), then weights (2^(h-l)) are non-increasing.
  Therefore, the k-th weight (smallest seen so far) divides all previous weights.
-/
lemma sum_divisible_by_next_weight {h : ℕ} {l : List ℕ} (h_sorted : l.IsChain (· ≤ ·)) :
    ∀ k (hk : k < l.length),
    (2 ^ (h - l.get ⟨k, hk⟩)) ∣ List.sum ((l.take k).map (fun x ↦ 2 ^ (h - x))) := by
  intro k hk
  apply sum_dvd_of_forall_dvd
  intros w hw
  -- w is a weight 2^(h - x) where x is in l.take k
  rw [List.mem_map] at hw
  rcases hw with ⟨len_x, h_mem_take, rfl⟩
  rw [List.mem_take_iff_getElem] at h_mem_take
  rcases h_mem_take with ⟨j, hj_lt, rfl⟩

  -- Exponent logic: h - l[k] ≤ h - l[j]
  apply Nat.pow_dvd_of_le_of_pow_dvd _ (by rfl)
  apply Nat.sub_le_sub_left
  -- Chain logic: j < k implies l[j] ≤ l[k]
  have : l.Pairwise (· ≤ ·) := List.isChain_iff_pairwise.mp h_sorted
  rw [<-List.sortedLE_iff_pairwise] at this
  apply List.SortedLE.getElem_le_getElem_of_le this (by omega)


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

/--
  The Integer version of Lemma 3.1 on Lists.
  Finds the prefix of the list that sums exactly to the target 2^h.
-/
theorem list_kraft_exact (lengths : List ℕ)
    (h_sorted : lengths.IsChain (· ≤ ·))
    (h_sum_ge_1 : List.sum (lengths.map (fun l ↦ (2 ^ l : ℚ)⁻¹)) ≥ 1) :
    ∃ k, List.sum ((lengths.take k).map (fun l ↦ (2 ^ l : ℚ)⁻¹)) = 1 := by

  -- 1. Setup: Define the Integer Domain (Scale by 2^h)
  let h := lengths.foldr max 0
  let weights := lengths.map (fun l ↦ 2 ^ (h - l))
  let target := 2 ^ h

  -- 2. Hypothesis Conversion: Rational Sum ≥ 1 implies Integer Sum ≥ Target
  have h_mass_ge : weights.sum ≥ target := by
    -- A. Establish that h is the upper bound (needed for exponent subtraction)
    have h_bound : ∀ l ∈ lengths, l ≤ h := fun l hl ↦ le_foldr_max lengths l hl

    -- B. Prove the scaling identity in Rationals: Σ 2^(h-l) = 2^h * Σ 2^(-l)
    sorry


  -- 3. Search: Identify the "Split Point" k
  -- We find the *first* prefix length k such that the sum meets or exceeds the target.
  let range := List.range (lengths.length + 1)
  let k := range.find? (fun i ↦ (weights.take i).sum ≥ target)
           |>.getD lengths.length

  -- 4. Bounds: Establish the properties of k
  have k_bounds : k > 0 ∧ k ≤ lengths.length := by
    -- Proving k ≤ lengths.length
    have h_le : k ≤ lengths.length := by
      dsimp [k]
      match hf : range.find? _ with
      | some i =>
        have := List.mem_of_find?_eq_some hf
        rw [List.mem_range] at this
        exact Nat.le_of_lt_succ this
      | none => exact Nat.le_refl _

    -- Proving k > 0
    have h_pos : k > 0 := by
      sorry

    exact ⟨h_pos, h_le⟩

  let prev := k - 1

  -- Explicitly connect weights.length to lengths.length for omega
  have h_len_eq : weights.length = lengths.length := by
    sorry

  -- Now omega has everything it needs: prev < k ≤ lengths.length = weights.length
  let w_last := weights.get ⟨prev, by omega⟩

  have decomposition : (weights.take k).sum = (weights.take prev).sum + w_last := by
    sorry -- Proof: list manipulation (take succ = take ++ [get]).

  -- 6. Divisibility (The Core "No Jump" Logic)
  -- The last added weight must divide the previous sum and the target.
  have dvd_prev : w_last ∣ (weights.take prev).sum := by
    sorry -- Proof: Apply 'sum_divisible_by_next_weight'.

  have dvd_target : w_last ∣ target := by
    sorry -- Proof: w_last is 2^j, target is 2^h, and j ≤ h.

  -- 7. Exactness: Conclude we hit the target exactly
  -- "If you are below T, add w (which divides T and S), and end up >= T, you must be exactly T."
  have h_exact_int : (weights.take k).sum = target := by
    -- apply exact_hit_of_divisible_step
    sorry

  -- 8. Return: Convert back to Rational domain
  exists k
  have : List.sum ((lengths.take k).map (fun l ↦ (2 ^ l : ℚ)⁻¹)) = 1 := by
    sorry -- Proof: Reverse the scaling from step 2.

  exact this

/--
Lemma 3.1: Let I be a finite set and let l : I → ℕ satisfy ∑ 2^{-l(i)} ≥ 1.
There exists a subset S ⊆ I such that ∑_{i ∈ S} 2^{-l(i)} = 1.
-/
theorem lemma_3_1 {α : _} (I : Finset α) (l : α → ℕ) :
    ∑ i ∈ I, (2 ^ l i : ℚ)⁻¹ ≥ 1 ->
    ∃ S ⊆ I, ∑ i ∈ S, (2 ^ l i : ℚ)⁻¹ = 1 :=
  sorry

/--
Theorem 3.2: Let I be a finite set and let l : I → ℕ satisfy ∑ 2^{-l(i)} ≤ 1.
There exists an injective mapping w : I → {0,1}* whose image is prefix-free,
and furthermore |w(i)| = l(i).
-/
theorem theorem_3_2 {α : _} (I : Finset α) (l : α → ℕ)
    (h_sum : ∑ i ∈ I, (2 ^ l i : ℚ)⁻¹ ≤ 1) :
    ∃ w : α → Word,
      Set.InjOn w I ∧
      PrefixFree (I.image w) ∧
      ∀ i ∈ I, (w i).length = l i :=
  sorry

/-! ## 2. Construction -/

section Helpers

variable {h : ℕ} {lengths : List ℕ}

variable {n : ℕ} {reqs weights : List ℕ}

/--
  Helper 1: The definition of k implies k > 0 if the sum overflows 2^n.
  It also establishes the bounds S_{k-1} < 2^n ≤ S_k.
-/
lemma split_index_bounds
    (h_w : weights = reqs.map (fun l => 2^(n - l)))
    (h_overflow : weights.sum > 2^n)
    (k : ℕ) (hk : k = splitIndex (2^n) weights) :
    k > 0 ∧
    (weights.take k).sum ≥ 2^n ∧
    (weights.take (k-1)).sum < 2^n ∧
    k - 1 < weights.length := by
  -- 1. Establish existence of valid split
  have h_ex : ∃ i ≤ weights.length, 2^n ≤ (weights.take i).sum := by
    exists weights.length; simp; apply le_of_lt h_overflow

  let spec := splitIndex_spec h_ex
  rw [←hk] at spec

  -- 2. Prove k > 0
  have k_pos : k > 0 := by
    by_contra h0
    simp_all

  -- 3. Bounds and Length
  refine ⟨k_pos, spec.1, ?_, ?_⟩
  · -- S_{k-1} < 2^n
    convert spec.2 (k-1) (Nat.pred_lt (ne_of_gt k_pos))
  · -- k-1 < length
    have k_le : k ≤ weights.length := by
      dsimp [splitIndex] at hk
      rw [hk]
      match h_find : (List.range (weights.length + 1)).find? _ with
      | none => exact Nat.le_refl _
      | some idx =>
        have := List.mem_of_find?_eq_some h_find
        rw [List.mem_range] at this
        exact Nat.le_of_lt_succ this
    omega

/--
  Helper 2: The divisibility argument.
  The weight at the split point (w_last) divides the accumulated sum (S_prev).
-/
lemma split_divisibility
    (h_w : weights = reqs.map (fun l => 2^(n - l)))
    (h_sorted : reqs.IsChain (· ≤ ·))
    (idx : ℕ) (h_idx : idx < reqs.length) :
    let w_last := 2^(n - reqs[idx])
    let S_prev := (weights.take idx).sum
    w_last ∣ S_prev := by
  intro w_last S_prev
  apply List.dvd_sum
  intros x hx
  rw [List.mem_take_iff_getElem] at hx
  rcases hx with ⟨i, hi_lt, rfl⟩

  -- 1. Establish index validity for 'reqs' manually
  have h_len : weights.length = reqs.length := by rw [h_w, List.length_map]
  have h_i_reqs : i < reqs.length := by
    rw [←h_len]
    exact Nat.lt_of_lt_of_le (lt_min_iff.mp hi_lt).left (by omega)

  -- 2. Simplify the element access
  -- 'simp' is smarter than 'rw' here; it handles the dependent index proof (h_i_reqs)
  simp only [h_w, List.getElem_map]

  -- 3. Proceed with divisibility logic
  rw [Nat.pow_dvd_pow_iff_le_right (by decide)]
  rw [List.isChain_iff_pairwise] at h_sorted
  · simp_all
    have h_le : reqs[i] ≤ reqs[idx] :=
      List.pairwise_iff_getElem.mp h_sorted i idx h_i_reqs h_idx (lt_min_iff.mp hi_lt).left
    apply Nat.le_add_of_sub_le
    apply Nat.sub_le_sub_left h_le


/--
  Helper 3: The "Gap" Logic [cite: 70-76].
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
  Helper 4: Algebraic final step.
  If the prefix sum of weights is exactly 2^n, and total weights ≤ 2^(n+1),
  then Left Mass = 2^n and Right Mass ≤ 2^n.
-/
lemma mass_split_algebra (n k : ℕ) (reqs weights : List ℕ)
    (h_w : weights = reqs.map (fun l => 2^(n - l)))
    (h_left_sum : (weights.take k).sum = 2^n)
    (h_bound : weights.sum ≤ 2^(n+1)) :
    mass n (reqs.take k) = 2^n ∧ mass n (reqs.drop k) ≤ 2^n := by
  dsimp [mass]
  constructor
  · -- 1. Prove Left Mass = 2^n
    rw [List.map_take, ←h_w]
    exact h_left_sum
  · -- 2. Prove Right Mass ≤ 2^n
    rw [List.map_drop, ←h_w]
    have h_total := List.sum_take_add_sum_drop weights k
    omega

/--
  Lemma 3.1 (Arithmetic Split):
  If we accumulate sorted powers of 2 and overflow a target 2^n,
  we must have hit 2^n exactly.
-/
lemma split_properties (n : ℕ) (reqs : List ℕ) (weights : List ℕ)
    (h_w : weights = reqs.map (fun l => 2^(n - l)))
    (h_overflow : weights.sum > 2^n)
    (h_bound : weights.sum ≤ 2^(n+1))
    (h_sorted : reqs.IsChain (· ≤ ·)) :
    let k := splitIndex (2^n) weights
    let left := reqs.take k
    let right := reqs.drop k
    mass n left = 2^n ∧ mass n right ≤ 2^n := by
  intro k left right

  -- 1. Helper 1: Bounds and Index Validity (for weights)
  have ⟨k_pos, h_ge, h_lt, h_idx_valid_w⟩ := split_index_bounds h_w h_overflow k rfl
  let last_idx := k - 1

  -- Convert validity from 'weights' to 'reqs' explicitly
  have h_len : weights.length = reqs.length := by rw [h_w, List.length_map]
  have h_idx_valid_r : last_idx < reqs.length := by rw [←h_len]; exact h_idx_valid_w

  -- 2. Define values
  let l_last := reqs[last_idx]
  let w_last := 2^(n - l_last)
  let S_prev := (weights.take last_idx).sum

  -- 3. Helper 2: Divisibility
  have w_dvd_prev : w_last ∣ S_prev :=
    split_divisibility h_w h_sorted last_idx h_idx_valid_r

  -- 4. Helper 3: Exact Fit Logic
  have w_dvd_target : w_last ∣ 2^n :=  by
    rw [Nat.pow_dvd_pow_iff_pow_le_pow (by decide)]
    exact Nat.pow_le_pow_of_le (by decide) (by simp)

  -- Decomposition: weights.take k sum = S_prev + w_last
  have split_decomp : (weights.take k).sum = S_prev + w_last := by
    rw [←Nat.sub_add_cancel k_pos]
    rw [List.take_succ_eq_append_getElem h_idx_valid_w] -- Note: uses weights proof here
    rw [List.sum_append, List.sum_cons, List.sum_nil, add_zero]
    congr 1
    dsimp [w_last, l_last]
    simp_all
    rfl

  rw [split_decomp] at h_ge

  have h_exact : S_prev + w_last = 2^n :=
    exact_fit_logic S_prev w_last (2^n) h_lt h_ge w_dvd_prev w_dvd_target

  -- 5. Final Mass properties
  apply mass_split_algebra n k reqs weights h_w _ h_bound
  -- Prove the premise: (weights.take k).sum = 2^n
  rw [split_decomp]
  exact h_exact


-- A. Mass Constraints
/--
  If 0 is in the list, it contributes 2^h to the mass.
  Since total mass ≤ 2^h, no other elements can exist.
-/
lemma mass_zero_implies_singleton
    (h_mass : mass h lengths ≤ 2^h)
    (h_zero : 0 ∈ lengths) :
    lengths = [0] := by
  dsimp [mass] at h_mass
  rw [List.mem_iff_append] at h_zero
  rcases h_zero with ⟨pre, post, rfl⟩
  rw [List.map_append, List.sum_append] at h_mass
  rw [List.map_cons, List.sum_cons] at h_mass
  simp only [Nat.sub_zero] at h_mass
  have h_rest_zero : (pre.map (fun l => 2 ^ (h - l))).sum + (post.map (fun l => 2 ^ (h - l))).sum = 0 := by
    omega
  have h_pre_nil : pre = [] := by
    match pre with
    | [] => rfl
    | x :: xs =>
      simp only [List.map_cons, List.sum_cons] at h_rest_zero
      have : 2 ^ (h - x) > 0 := Nat.pow_pos (by decide)
      omega
  have h_post_nil : post = [] := by
    match post with
    | [] => rfl
    | x :: xs =>
      simp only [List.map_cons, List.sum_cons] at h_rest_zero
      have : 2 ^ (h - x) > 0 := Nat.pow_pos (by decide)
      omega
  subst pre post
  rfl

/-- Helper: If disjoint, the lengths of the union are the permutation of the combined lengths. -/
lemma lengths_union_disjoint {S1 S2 : Code} (h : Disjoint S1 S2) :
    List.Perm ((S1 ∪ S2).toList.map List.length)
              ((S1.toList.map List.length) ++ (S2.toList.map List.length)) := by
  -- Convert to multiset equality which handles permutation automatically
  sorry

lemma lengths_image_cons (b : Bool) (S : Code) :
    (S.image (List.cons b)).toList.map List.length =
    (S.toList.map List.length).map Nat.succ := by
  sorry

end Helpers

-- Helper: Lengths of a code as a multiset
def lengthMultiset (S : Code) : Multiset ℕ := S.val.map List.length

-- Helper: Lengths of a disjoint union are the sum of length multisets
lemma lengthMultiset_union_of_disjoint {S1 S2 : Code} (h : Disjoint S1 S2) :
    lengthMultiset (S1 ∪ S2) = lengthMultiset S1 + lengthMultiset S2 := by
  dsimp [lengthMultiset]
  -- S1 ∪ S2 is Finset.disjUnion because they are disjoint
  rw [<-Finset.disjUnion_eq_union _ _ h]
  -- val of disjUnion is map sum
  simp only [Finset.disjUnion_val, Multiset.map_add]

-- Word = List Bool in your development
lemma lengths_image_cons_perm (b : Bool) (S : Code) :
    ((S.image (List.cons b)).toList.map List.length
      ).Perm ((S.toList.map List.length).map Nat.succ) := by
  classical
  -- Convert to multisets; then simp.
  -- This relies on standard facts:
  --   (i) toList forgets order only (toMultiset),
  --  (ii) image with injective = map on the underlying multiset,
  -- (iii) length (b :: w) = succ (length w).
  sorry
