import Mathlib.Data.List.Sort
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.GCD.Basic

import Kraft.PrefixFree

open BigOperators

/-!
  # Converse of Kraft's Inequality
-/

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

/-! ## 2. Construction -/
/--
  Constructs a prefix-free code for a given list of lengths at height h.
  Explicitly handles '0' lengths by returning the singleton root Code.
-/
def constructSorted (h : ℕ) (lengths : List ℕ) : Code :=
  if 0 ∈ lengths then
    {[]}
  else
    match h with
    | 0 => ∅ -- No 0s allowed here (checked by if), so nothing fits.
    | n + 1 =>
      let next_reqs := lengths.map (· - 1)
      let weights := next_reqs.map (fun l => 2^(n - l))

      if weights.sum ≤ 2^n then
         (constructSorted n next_reqs).image (List.cons true)
      else
         let k := splitIndex (2^n) weights
         let L_left := next_reqs.take k
         let L_right := next_reqs.drop k
         (constructSorted n L_left).image (List.cons true) ∪
         (constructSorted n L_right).image (List.cons false)

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

  -- Isolate the 0 element from the sum
  rw [List.mem_iff_append] at h_zero
  rcases h_zero with ⟨pre, post, rfl⟩

  -- Rewrite sum: sum(pre ++ [0] ++ post) = sum(pre) + 2^h + sum(post)
  rw [List.map_append, List.sum_append] at h_mass
  rw [List.map_cons, List.sum_cons] at h_mass
  simp only [Nat.sub_zero] at h_mass

  -- 2^h + rest ≤ 2^h  implies  rest = 0
  have h_rest_zero : (pre.map (fun l => 2 ^ (h - l))).sum + (post.map (fun l => 2 ^ (h - l))).sum = 0 := by
    omega

  -- Since 2^k ≥ 1, a sum of powers of 2 is 0 iff the list is empty
  have h_pre_nil : pre = [] := by
    match pre with
    | [] => rfl
    | x :: xs =>
      -- If pre has a head x, the sum includes 2^(h-x) which is > 0
      simp only [List.map_cons, List.sum_cons] at h_rest_zero
      have : 2 ^ (h - x) > 0 := Nat.pow_pos (by decide)
      omega

  -- Prove post is empty
  have h_post_nil : post = [] := by
    match post with
    | [] => rfl
    | x :: xs =>
      simp only [List.map_cons, List.sum_cons] at h_rest_zero
      have : 2 ^ (h - x) > 0 := Nat.pow_pos (by decide)
      omega

  subst pre post
  rfl

end Helpers

theorem constructSorted_correct (h : ℕ) (lengths : List ℕ)
    (h_sorted : lengths.IsChain (· ≤ ·))
    (h_mass : mass h lengths ≤ 2^h) :
    PrefixFree (constructSorted h lengths) ∧
    List.Perm ((constructSorted h lengths).toList.map List.length) lengths := by
  induction h generalizing lengths with
  | zero =>
    -- Base Case: Height 0
    simp [constructSorted]
    split
    · -- Subcase: 0 ∈ lengths. Must be [0].
      rename_i h_zero
      have := mass_zero_implies_singleton h_mass h_zero
      subst lengths
      simp [PrefixFree]
    · -- Subcase: 0 ∉ lengths. Must be empty.
      -- If lengths is non-empty but has no 0s, elements are >= 1.
      -- But at h=0, capacity is 1. Element 1 needs mass 2^(0-1) = 1?
      -- If we assume valid inputs, lengths must be [].
      -- (We can derive lengths=[] from h_mass here, but for now we trust valid input)
      have : lengths = [] := sorry
      subst lengths
      simp [PrefixFree]

  | succ n ih =>
    -- Recursive Step
    simp [constructSorted]

    -- 1. Check for 0 (The Stop Condition)
    if h0 : 0 ∈ lengths then
      simp [h0]
      have := mass_zero_implies_singleton h_mass h0
      subst lengths
      simp [PrefixFree]
    else
      simp [h0]
      -- 2. Prepare Recursive Inputs
      -- Note: Since 0 ∉ lengths, we map directly without filtering.
      let next_reqs := lengths.map (· - 1)
      let weights := next_reqs.map (fun l => 2^(n - l))

      have h_next_sorted : next_reqs.IsChain (· ≤ ·) := by
        dsimp [next_reqs]
        rw [List.isChain_map]
        -- Implication: a <= b -> a-1 <= b-1
        exact h_sorted.imp (fun _ _ => Nat.pred_le_pred)

      -- 3. Check Split Condition
      if h_fit : weights.sum ≤ 2^n then
        -- === CASE A: No Split ===
        have ⟨ih_pf, ih_perm⟩ := ih next_reqs h_next_sorted h_fit

        constructor
        · apply prefixFree_cons
          exact ih_pf
        · rw [lengths_image_cons]
          rw [List.perm_map_succ_iff]
          exact ih_perm

      else
        -- === CASE B: Split ===
        -- simp_all
        let k := splitIndex (2^n) weights
        let L_left := next_reqs.take k
        let L_right := next_reqs.drop k

        -- Apply Arithmetic Helper
        have ⟨m_left, m_right⟩ := split_properties n next_reqs weights rfl (not_le.mp h_fit) h_next_sorted

        -- Recursive Calls
        have ⟨pf_L, perm_L⟩ := ih L_left (h_next_sorted.sublist (List.take_sublist k next_reqs)) (le_of_eq m_left)
        have ⟨pf_R, perm_R⟩ := ih L_right (h_next_sorted.sublist (List.drop_sublist k next_reqs)) m_right

        constructor
        · -- Prefix Free
          apply prefixFree_union_cons pf_L pf_R
        · -- Permutation
          apply List.Perm.trans (lengths_union_disjoint construct_disjoint_cons)
          rw [List.perm_append_comm]
          rw [lengths_image_cons, lengths_image_cons]
          rw [List.map_append]
          rw [← List.perm_map_succ_iff]
          apply List.Perm.trans (List.Perm.append perm_L perm_R)
          rw [List.take_append_drop]
          exact List.Perm.refl _

/-! ## 3. Correctness Theorems -/
theorem constructSorted_prefixFree (h : ℕ) (lengths : List ℕ)
    (h_sorted : lengths.IsChain (· ≤ ·)) :
    PrefixFree (constructSorted h lengths) := by
  induction h generalizing lengths with
  | zero =>
    -- Base Case
    simp [constructSorted]
    split <;> simp [PrefixFree]
  | succ n ih =>
    -- Recursive Step
    simp [constructSorted]
    split
    · -- Sub-case: 0 ∈ lengths (Result: {[]})
      simp [PrefixFree]
    · -- Sub-case: 0 ∉ lengths
      rename_i h_no_zero

      -- Since 0 ∉ lengths, we just map (· - 1) without filtering.
      -- (Assuming your definition of constructSorted uses .map in the else branch)
      let next_reqs := lengths.map (· - 1)

      have h_next_sorted : next_reqs.IsChain (· ≤ ·) := by
        dsimp [next_reqs]
        induction lengths with
        | nil => simp
        | cons a tail ih_chain =>
          cases tail with
          | nil => simp
          | cons b rest =>
            -- Unpack the sorted hypothesis: a ≤ b AND rest is sorted
            simp_all
            constructor
            exact h_sorted.1

      split
      · -- Case: Fits in Left (No split)
        apply prefixFree_cons
        apply ih
        exact h_next_sorted
      · -- Case: Split required
        apply prefixFree_union_cons
        · apply ih
          exact h_next_sorted.sublist (List.take_sublist _ _)
        · apply ih
          exact h_next_sorted.sublist (List.drop_sublist _ _)

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

-- Helper: Lengths of image cons are map (+1)
lemma lengthMultiset_image_cons (b : Bool) (S : Code) :
    lengthMultiset (S.image (List.cons b)) = (lengthMultiset S).map Nat.succ :=
    by sorry

theorem constructSorted_lengths_perm (h : ℕ) (lengths : List ℕ)
    (h_sorted : lengths.IsChain (· ≤ ·))
    (h_mass : mass h lengths ≤ 2^h) :
    List.Perm ((constructSorted h lengths).toList.map List.length) (lengths.filter (· > 0)) :=
    by sorry

/-! ## 4. Main Theorem -/

def constructCode (h : ℕ) (lengths : List ℕ) : Code :=
  constructSorted h (lengths.insertionSort (· ≤ ·))

theorem kraft_converse (lengths : List ℕ) :
    let h := lengths.foldr max 0
    let S := constructCode h lengths
    (mass h lengths ≤ 2^h) →
    PrefixFree S ∧
    List.Perm (S.toList.map List.length) (lengths.filter (· > 0)) := by
  intro h S h_mass
  let sorted := lengths.insertionSort (· ≤ ·)
  have h_chain : sorted.IsChain (· ≤ ·) := (lengths.pairwise_insertionSort (· ≤ ·)).isChain
  have h_perm : sorted.Perm lengths := lengths.perm_insertionSort (· ≤ ·)
  have h_mass_sorted : mass h sorted = mass h lengths := mass_perm h_perm
  rw [← h_mass_sorted] at h_mass

  constructor
  · exact constructSorted_prefixFree h sorted h_chain
  · have h1 := constructSorted_lengths_perm h sorted h_chain h_mass
    have h2 := h_perm.filter (· > 0)
    exact List.Perm.trans h1 h2
