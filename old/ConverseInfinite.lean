import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Order.Filter.Defs

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

import Kraft.Basic

namespace Kraft

open scoped BigOperators Real

variable {I : Type _} [DecidableEq I] (l : I → ℕ)

noncomputable section

/-! ### Helper Lemmas -/

lemma finite_le_of_summable {I : Type _} (l : I → ℕ)
    (h : Summable (fun i => (1 / 2 : ℝ) ^ l i)) (k : ℕ) :
    {i | l i ≤ k}.Finite := by
  classical

  -- terms → 0 along cofinite
  have h0 : Filter.Tendsto (fun i => (1 / 2 : ℝ) ^ l i) cofinite (𝓝 (0:ℝ)) :=
    h.tendsto_cofinite_zero

  have hkpos : (0:ℝ) < (1/2:ℝ)^k := by positivity

  -- eventually (term < (1/2)^k)
  have hlt : ∀ᶠ i in cofinite, (1/2:ℝ)^(l i) < (1/2:ℝ)^k :=
    h0.eventually (lt_mem_nhds hkpos)

  -- so the set where ¬(term < (1/2)^k) is finite
  have hfin :
      {i : I | ¬ ((1/2:ℝ)^(l i) < (1/2:ℝ)^k)}.Finite := by
    simpa [Filter.eventually_cofinite] using hlt

  -- and {i | l i ≤ k} is a subset of that set, because base ≤ 1 flips inequalities in exponent
  refine hfin.subset ?_
  intro i hi
  have hbase0 : (0:ℝ) ≤ (1/2:ℝ) := by norm_num
  have hbase1 : (1/2:ℝ) ≤ (1:ℝ) := by norm_num
  have hpow : (1/2:ℝ)^k ≤ (1/2:ℝ)^(l i) :=
    pow_le_pow_of_le_one hbase0 hbase1 hi
  -- hpow says (1/2)^(l i) ≥ (1/2)^k, so it is not < (1/2)^k
  exact not_lt_of_ge (by simpa [ge_iff_le] using hpow)

lemma eq_of_prefix_of_length_eq {α} {u v : List α}
    (hp : u <+: v) (hlen : u.length = v.length) : u = v := by
  rcases hp with ⟨t, rfl⟩
  -- now hlen : u.length = (u ++ t).length = u.length + t.length
  have htlen0 : 0 = t.length := by
    -- subtract u.length on both sides
    have := congrArg (fun n => n - u.length) hlen
    -- left: u.length - u.length = 0; right: (u.length + t.length) - u.length = t.length
    simpa [List.length_append, Nat.sub_self, Nat.add_sub_cancel_left] using this
  have ht : t = [] := by
    apply List.length_eq_zero.mp
    exact htlen0.symm
  subst ht
  simp


/-
If the series $\sum 2^{-l(i)}$ converges, then for any $k$, there are only finitely many $i$ such that $l(i) \le k$.
-/
lemma finite_le_of_summable {I : Type _} (l : I → ℕ)
    (h_summable : Summable (fun i => (1 / 2 : ℝ) ^ l i)) (k : ℕ) :
    {i | l i ≤ k}.Finite := by
  have := h_summable.hasSum.summable.tendsto_cofinite_zero; simp_all +decide
  -- Since $l(i) \leq k$, we have $(2 ^ l i)⁻¹ \geq (2 ^ k)⁻¹$.
  have h_bound : ∀ i : I, l i ≤ k → (2 ^ l i : ℝ)⁻¹ ≥ (2 ^ k : ℝ)⁻¹ := by
    exact fun i hi => inv_anti₀ ( by positivity ) ( pow_le_pow_right₀ ( by norm_num ) hi )
  exact Set.Finite.subset ( this.eventually ( gt_mem_nhds <| inv_pos.mpr <| pow_pos zero_lt_two k ) ) fun i hi => by simp_all

/-- If two strings have the same length and one is a prefix of the other, they are equal. -/
lemma eq_of_prefix_of_length_eq {α} {u v : List α}
    (hpref : u <+: v) (hlen : u.length = v.length) : u = v :=
  List.eq_of_prefix_of_length_eq hpref hlen

/-- If `u` is strictly shorter than `v` and they extend to the same string `x`, then `u` is a prefix of `v`. -/
lemma prefix_of_extends_common {α} {u v x : List α}
    (hu : u <+: x) (hv : v <+: x) (hlen : u.length < v.length) : u <+: v :=
  List.prefix_of_prefix_length_le hu hv (le_of_lt hlen)

/-! ### Definitions -/

/-- The finite set of indices with length `k`. -/
def indicesAt (k : ℕ) (h_summable : Summable (fun i ↦ (1 / 2 : ℝ) ^ l i)) : Finset I :=
  (finite_le_of_summable l h_summable k).toFinset.filter (fun i ↦ l i = k)

lemma mem_indicesAt_iff (k : ℕ) (h_summable : Summable (fun i ↦ (1 / 2 : ℝ) ^ l i)) (i : I) :
    i ∈ indicesAt l k h_summable ↔ l i = k := by
  simp [indicesAt]

/-- All binary strings of length `k`. -/
def allStrings (k : ℕ) : Finset (List Bool) :=
  (Finset.univ : Finset (Fin k → Bool)).image List.ofFn

lemma card_allStrings (k : ℕ) : (allStrings k).card = 2 ^ k := by
  simp [allStrings, Finset.card_image_of_injective _ List.ofFn_injective]

/-- Extensions of a word `w` to length `k` (assuming `w.length ≤ k`). -/
def extensionsAt (k : ℕ) (w : List Bool) : Finset (List Bool) :=
  (allStrings (k - w.length)).image (w ++ ·)

lemma card_extensionsAt (k : ℕ) (w : List Bool) (h : w.length ≤ k) :
    (extensionsAt k w).card = 2 ^ (k - w.length) := by
  classical
  -- card(image) = card(original) because append-left is injective
  simp [extensionsAt, card_allStrings,
        Finset.card_image_of_injective _ (List.append_left_injective w)]

/-! ### Partial Code Structure -/

/--
State at step `k`: We have assigned words to all indices `i` where `l i < k`.
We maintain that this partial assignment is length-correct, injective, and prefix-free.
-/
structure PartialCode (k : ℕ) where
  code : ∀ i, l i < k → List Bool
  len_eq : ∀ i (h : l i < k), (code i h).length = l i
  inj : ∀ i j (hi : l i < k) (hj : l j < k), code i hi = code j hj → i = j
  pfree : ∀ i j (hi : l i < k) (hj : l j < k), code i hi <+: code j hj → i = j

/--
The set of words assigned to indices with length `j`.
-/
def wordsAt (k : ℕ) (state : PartialCode l k) (h_summable : Summable (fun i ↦ (1 / 2 : ℝ) ^ l i))
    (j : ℕ) (hj : j < k) : Finset (List Bool) :=
  (indicesAt l j h_summable).attach.image fun x =>
    state.code x.1 (by
      have : l x.1 = j := (mem_indicesAt_iff l j h_summable x.1).mp (Finset.mem_attach _ x)
      linarith)

/--
The set of "blocked" nodes at level `k`.
These are all strings of length `k` that extend a word already assigned in `PartialCode`.
-/
def blocked (k : ℕ) (state : PartialCode l k) (h_summable : Summable (fun i ↦ (1 / 2 : ℝ) ^ l i)) : Finset (List Bool) :=
  (Finset.univ : Finset (Fin k)).biUnion fun j =>
    (wordsAt l k state h_summable j.1 j.2).biUnion fun w =>
      extensionsAt k w

/-! ### The Extension Lemma -/

lemma extend_code (k : ℕ)
    (h_summable : Summable (fun i ↦ (1 / 2 : ℝ) ^ l i))
    (h_sum : ∑' i, (1 / 2 : ℝ) ^ l i ≤ 1)
    (state : PartialCode l k) :
    ∃ (new_map : ∀ i, l i = k → List Bool),
      (∀ i h, (new_map i h).length = k) ∧
      (∀ i j hi hj, new_map i hi = new_map j hj → i = j) ∧
      (∀ i (hi : l i = k), new_map i hi ∉ blocked l k state h_summable) := by
  let S_k := indicesAt l k h_summable
  let B := blocked l k state h_summable

  -- 1. Calculate cardinality of blocked nodes
  have h_card_B : B.card = ∑ j in Finset.range k, (indicesAt l j h_summable).card * 2 ^ (k - j) := by
    -- We calculate sum over Fin k first
    have h_fin_sum : B.card = ∑ j : Fin k, (indicesAt l j.1 h_summable).card * 2 ^ (k - j.1) := by
      rw [blocked]
      rw [Finset.card_biUnion]
      · apply Finset.sum_congr rfl
        intro j _
        rw [Finset.card_biUnion]
        · -- Inner sum: |wordsAt| * |extensions|
          rw [wordsAt]
          rw [Finset.card_image_of_injective]
          · simp only [nsmul_eq_mul, Finset.sum_const, Finset.card_attach]
            intro w hw
            -- Extract length of w to prove constant size of extensions
            rcases Finset.mem_image.mp hw with ⟨x, _, rfl⟩
            have h_len : (state.code x.1 _).length = j.1 := by
               rw [state.len_eq]
               exact (mem_indicesAt_iff l j.1 h_summable x.1).mp x.2
            rw [card_extensionsAt _ _ (by rw [h_len]; exact le_of_lt j.2)]
          · -- Injectivity of the mapping i ↦ code i
            intro x y heq
            apply Subtype.ext
            apply state.inj _ _ _ _ heq
        · -- Disjointness within level j
          intro w1 hw1 w2 hw2 hne
          rw [Finset.disjoint_left]
          intro x hx1 hx2
          rcases Finset.mem_image.mp hx1 with ⟨_, _, rfl⟩
          rcases Finset.mem_image.mp hx2 with ⟨_, _, heq⟩
          -- w1 and w2 are codes from level j, so length j
          rcases Finset.mem_image.mp hw1 with ⟨i1, _, rfl⟩
          rcases Finset.mem_image.mp hw2 with ⟨i2, _, rfl⟩
          have len1 := state.len_eq i1.1 (by simp [indicesAt] at i1; linarith)
          have len2 := state.len_eq i2.1 (by simp [indicesAt] at i2; linarith)
          have eq_base : state.code i1.1 _ = state.code i2.1 _ :=
             eq_of_prefix_of_length_eq (List.prefix_of_prefix_length_le (List.prefix_append _ _) (by rw [heq]; apply List.prefix_append) (by rw [len1, len2])) (by rw [len1, len2])
          have : i1 = i2 := by apply Subtype.ext; apply state.inj _ _ _ _ eq_base
          subst this
          contradiction

      · -- Disjointness across levels
        intro j1 _ j2 _ hne_j
        rw [Finset.disjoint_left]
        intro x hB1 hB2
        simp only [Finset.mem_biUnion, wordsAt, Finset.mem_image, Finset.mem_attach] at hB1 hB2
        rcases hB1 with ⟨w1, ⟨i1, _, rfl⟩, h_ext1⟩
        rcases hB2 with ⟨w2, ⟨i2, _, rfl⟩, h_ext2⟩
        rcases Finset.mem_image.mp h_ext1 with ⟨_, _, rfl⟩
        rcases Finset.mem_image.mp h_ext2 with ⟨_, _, heq⟩

        -- Assume j1 < j2 WLOG
        wlog h_lt : j1.1 < j2.1 generalizing j1 j2 i1 i2
        · have : j1.1 ≠ j2.1 := by intro h; apply hne_j; apply Fin.ext h
          rcases lt_or_gt_of_ne this with h | h
          · exact this h j1 j2 hne_j i1 i2 rfl heq
          · exact (this h j2 j1 hne_j.symm i2 i1 heq.symm rfl).symm

        have len1 : (state.code i1.1 _).length = j1.1 := state.len_eq _ _
        have len2 : (state.code i2.1 _).length = j2.1 := state.len_eq _ _

        -- w1 is a prefix of w2 because both extend to x and len(w1) < len(w2)
        have : state.code i1.1 _ <+: state.code i2.1 _ :=
          prefix_of_extends_common (List.prefix_append _ _) (by rw [heq]; apply List.prefix_append) (by rw [len1, len2]; exact h_lt)

        -- Contradiction with prefix-free property
        have : i1.1 = i2.1 := state.pfree _ _ _ _ this
        subst this
        rw [len1] at len2; linarith

    -- Convert Sum over Fin k to Sum over range k
    rw [h_fin_sum]
    refine Finset.sum_bij (fun (x : Fin k) _ => x.1) (by simp) (by simp) (by intro a b _ _ h; apply Fin.ext h) (by intro b hb; use ⟨b, Finset.mem_range.mp hb⟩; simp)

  -- 2. Capacity Inequality: ∑ |S_j| * 2^(k-j) ≤ 2^k
  have h_capacity : S_k.card + B.card ≤ 2^k := by
    let J := Finset.range (k + 1)
    let F := (finite_le_of_summable l h_summable k).toFinset

    have h_le_one : ∑ i in F, (1 / 2 : ℝ) ^ l i ≤ 1 :=
      le_trans (Finset.sum_le_tsum _ (fun _ _ ↦ by positivity) h_summable) h_sum

    -- Group by fibers
    rw [Finset.sum_fiberwise_of_maps_to (g := l) (t := J)] at h_le_one
    · -- Rewrite inner sums
      have h_alg : ∑ j in J, ((indicesAt l j h_summable).card : ℝ) * ((1 / 2 : ℝ) ^ j) ≤ 1 := by
        convert h_le_one using 1
        apply Finset.sum_congr rfl
        intro j _
        simp only [Finset.sum_const, nsmul_eq_mul]
        congr 1
        ext i
        simp [indicesAt, F, mem_indicesAt_iff]
        constructor <;> intro h <;> simp [h] at * <;> exact h

      -- Multiply by 2^k to get integer bound
      have h_int : ∑ j in J, ((indicesAt l j h_summable).card : ℝ) * 2 ^ (k - j) ≤ 2 ^ k := by
        have : (2:ℝ)^k * ∑ j in J, (indicesAt l j h_summable).card * (1/2)^j ≤ (2:ℝ)^k * 1 :=
            mul_le_mul_of_nonneg_left h_alg (by positivity)
        rw [Finset.mul_sum] at this
        refine le_trans ?_ (by simpa using this)
        apply le_of_eq
        apply Finset.sum_congr rfl
        intro j hj
        simp only [Finset.mem_range] at hj
        rw [← mul_assoc, pow_sub₀ (by norm_num) (Nat.le_of_lt_succ hj)]
        field_simp; ring

      -- Split last term (j=k) from the rest (j < k)
      rw [Finset.sum_range_succ] at h_int
      norm_cast at h_int
      simp only [tsub_self, pow_zero, mul_one] at h_int
      rw [h_card_B]
      exact h_int

    · -- Proof of maps_to
      intro i hi
      simp only [Finset.mem_range]
      simp [F] at hi
      exact Nat.lt_succ_of_le hi

  -- 3. Construct the map
  have h_avail : S_k.card ≤ (allStrings k).card - B.card := by
    rw [card_allStrings]
    linarith

  have h_subset : B ⊆ allStrings k := by
    intro w hw
    simp only [blocked, Finset.mem_biUnion, wordsAt, Finset.mem_image, Finset.mem_attach] at hw
    rcases hw with ⟨j, _, _, ⟨i, _, rfl⟩, s, _, rfl⟩
    -- w = code(i) ++ s
    -- length = j + (k - j) = k
    simp [allStrings, state.len_eq _ (by linarith)]

  have h_diff_card : (allStrings k \ B).card = (allStrings k).card - B.card :=
    Finset.card_sdiff h_subset

  rw [← h_diff_card] at h_avail

  obtain ⟨f, hf_inj⟩ := Finset.exists_embedding_of_card_le h_avail

  let new_map (i : I) (hi : l i = k) : List Bool :=
    f ⟨i, by simp [S_k, indicesAt, hi]⟩

  use new_map
  constructor
  · intro i hi
    have := (f ⟨i, _⟩).2
    simp only [Finset.mem_sdiff, allStrings, Finset.mem_image, Finset.mem_univ, true_and] at this
    rcases this.1 with ⟨g, _, rfl⟩
    simp
  constructor
  · intro i j hi hj heq
    have : f ⟨i, _⟩ = f ⟨j, _⟩ := by apply Subtype.ext; exact heq
    have := hf_inj this
    simp at this
    exact this
  · intro i hi
    have := (f ⟨i, _⟩).2
    simp at this
    exact this.2

/-! ### Main Theorem -/

theorem kraft_inequality_tight_infinite
    (h_summable : Summable (fun i ↦ (1 / 2 : ℝ) ^ l i))
    (h_sum : ∑' i, (1 / 2 : ℝ) ^ l i ≤ 1) :
    ∃ w : I → List Bool,
      Function.Injective w ∧
      PrefixFree (Set.range w) ∧
      ∀ i, (w i).length = l i := by

  -- Recursive step
  let step (k : ℕ) (prev : PartialCode l k) : PartialCode l (k + 1) :=
    let ⟨new_map, h_len, h_inj, h_blocked⟩ := extend_code k _ h_summable h_sum prev
    {
      code := fun i hi ↦
        if h : l i < k then prev.code i h
        else new_map i (by linarith)
      len_eq := fun i hi ↦ by
        split_ifs with h_lt
        · exact prev.len_eq i h_lt
        · exact h_len i (by linarith)
      inj := fun i j hi hj heq ↦ by
        split_ifs at heq with h1 h2
        · exact prev.inj i j h1 h2 heq
        · exfalso; have l1 := prev.len_eq i h1; have l2 := h_len j (by linarith); rw [heq] at l1; rw [l1] at l2; linarith
        · exfalso; have l1 := h_len i (by linarith); have l2 := prev.len_eq j h2; rw [heq] at l1; rw [l1] at l2; linarith
        · exact h_inj i j (by linarith) (by linarith) heq
      pfree := fun i j hi hj h_pref ↦ by
        split_ifs at h_pref with h1 h2
        · exact prev.pfree i j h1 h2 h_pref
        · -- i old, j new
          exfalso
          have : prev.code i h1 <+: new_map j (by linarith) := h_pref
          have h_blk : new_map j (by linarith) ∈ blocked l k prev h_summable := by
             simp only [blocked, Finset.mem_biUnion, wordsAt, Finset.mem_image, Finset.mem_attach]
             use ⟨l i, by linarith⟩
             simp
             use prev.code i h1
             constructor
             · use ⟨i, by simp [indicesAt, h1]⟩, (by simp)
               simp
               simp [indicesAt] at h1
               exact h1
             · simp [extensionsAt, allStrings]
               rcases h_pref with ⟨s, hs⟩
               use s
               rw [hs] at h_len; rw [prev.len_eq i h1] at h_len; simp [h_len]; rw [hs]
          exact h_blocked j (by linarith) h_blk
        · -- i new, j old
          exfalso
          have : (new_map i (by linarith)).length ≤ (prev.code j h2).length := List.length_le_of_sublist (List.sublist_of_prefix h_pref)
          rw [h_len i (by linarith), prev.len_eq j h2] at this
          linarith
        · -- i new, j new
          have : new_map i (by linarith) = new_map j (by linarith) :=
             eq_of_prefix_of_length_eq h_pref (by rw [h_len _ _, h_len _ _])
          exact h_inj i j (by linarith) (by linarith) this
    }

  let code_seq : (k : ℕ) → PartialCode l k :=
    Nat.rec {
      code := fun i hi ↦ by linarith
      len_eq := fun i hi ↦ by linarith
      inj := fun i j hi hj ↦ by linarith
      pfree := fun i j hi hj ↦ by linarith
    } step

  have code_consistent : ∀ k, ∀ i (hi : l i < k),
      (code_seq (k + 1)).code i (Nat.lt_succ_of_lt hi) = (code_seq k).code i hi := by
    intro k i hi
    simp [code_seq, step]
    rw [dif_pos hi]

  have code_stable :
      ∀ k m i (hi : l i < k), k ≤ m →
        (code_seq m).code i (lt_of_lt_of_le hi ‹k ≤ m›) = (code_seq k).code i hi := by
    intro k m i hi hkm
    -- write m = k + d
    have hm : m = k + (m - k) := by
      -- m = k + (m-k) because k ≤ m
      exact (Nat.add_sub_of_le hkm).symm
    -- now induct on d = m-k
    revert m
    refine Nat.rec (motive := fun d => ∀ m, m = k + d → k ≤ m →
        (code_seq m).code i (lt_of_lt_of_le hi ‹k ≤ m›) = (code_seq k).code i hi) ?base ?step (m - k) m hm hkm
    · intro m hm' hkm'
      -- d=0, so m=k
      have : m = k := by simpa using hm'
      subst this
      rfl
    · intro d ih m hm' hkm'
      -- d+1: m = k + (d+1) = (k + d) + 1
      have hm1 : m = (k + d) + 1 := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hm'
      -- reduce using one-step consistency from (k+d) to (k+d+1)
      -- You want: code_seq ((k+d)+1) ... = code_seq (k+d) ...
      -- i is still “old” at level (k+d) because l i < k ≤ k+d
      have hikd : l i < k + d := lt_of_lt_of_le hi (Nat.le_add_right k d)
      -- unfold one step
      have step_eq :
          (code_seq ((k + d) + 1)).code i (Nat.lt_succ_of_lt hikd)
            = (code_seq (k + d)).code i hikd := by
        -- your `code_consistent` lemma is exactly this:
        simpa [Nat.add_assoc] using (code_consistent (k := k + d) i hikd)
      -- combine with IH at m = k+d
      have ih' := ih (k + d) (by rfl) (Nat.le_add_right k d)
      -- finish
      subst hm1
      -- rewrite the LHS by step_eq then apply ih'
      simpa [step_eq] using ih'

  have code_stable : ∀ k m, ∀ i (hi : l i < k), k ≤ m →
      (code_seq m).code i (lt_of_lt_of_le hi ‹k ≤ m›) = (code_seq k).code i hi := by
    intro k m i hi hle
    induction hle using Nat.le_induction with
    | base => rfl
    | succ n hle ih =>
      rw [← ih]
      exact (code_consistent n i (lt_of_lt_of_le hi hle)).symm

  let w (i : I) : List Bool := (code_seq (l i + 1)).code i (Nat.lt_succ_self _)

  use w
  constructor
  · -- Injectivity
    intro i j heq
    let k := max (l i) (l j) + 1
    have hi : l i < k := by linarith
    have hj : l j < k := by linarith
    have w_i : w i = (code_seq k).code i hi := code_stable _ _ _ _ (by linarith)
    have w_j : w j = (code_seq k).code j hj := code_stable _ _ _ _ (by linarith)
    rw [w_i, w_j] at heq
    exact (code_seq k).inj i j hi hj heq

  constructor
  · -- Prefix Free
    intro u hu v hv hpref
    rcases hu with ⟨i, rfl⟩
    rcases hv with ⟨j, rfl⟩
    let k := max (l i) (l j) + 1
    have hi : l i < k := by linarith
    have hj : l j < k := by linarith
    have w_i : w i = (code_seq k).code i hi := code_stable _ _ _ _ (by linarith)
    have w_j : w j = (code_seq k).code j hj := code_stable _ _ _ _ (by linarith)
    rw [w_i, w_j] at hpref
    have := (code_seq k).pfree i j hi hj hpref
    subst this
    rfl

  · intro i
    simp [w]
    exact (code_seq (l i + 1)).len_eq i (Nat.lt_succ_self _)

end

end Kraft
