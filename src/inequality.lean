import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic

import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin

open BigOperators

/-!
  # Integer Kraft Inequality
  Proving: if S is prefix-free and bounded by n, then ∑ 2^(n-|w|) ≤ 2^n.
-/

abbrev Word := List Bool
abbrev Code := Finset Word

/-- Prefix-free set of binary words -/
def PrefixFree (S : Code) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x <+: y → x = y

/-- Integer Kraft mass: ∑ 2^(n - |w|) -/
def countMass (n : ℕ) (S : Code) : ℕ :=
  ∑ w ∈ S, 2^(n - w.length)

/-! ## 1. Arithmetic & Word Lemmas -/

lemma pow_two_add_self (n : ℕ) : 2^n + 2^n = 2^(n+1) := by
  -- 2^(n+1) = 2^n * 2 by pow_succ
  -- and 2^n + 2^n = 2^n * 2 by Nat.mul_two
  -- (or by two_mul; depends on simp normalization)
  simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    (Nat.mul_two (2^n)).symm

lemma pow_sub_succ {n k : ℕ} :
    2^((n + 1) - (k + 1)) = 2^(n - k) := by
  rw [Nat.add_sub_add_right]

lemma length_le_of_cons_le {b : Bool} {t : Word} {n : ℕ}
    (h : (b :: t).length ≤ n + 1) :
    t.length ≤ n := by
  simp at h
  exact h

lemma cons_length_le_of_tail {b : Bool} {t : Word} {n : ℕ} :
    t.length ≤ n → (b :: t).length ≤ n+1 := by
  intro h; simpa using Nat.succ_le_succ h

/-! ## 2. Splitting Infrastructure -/

/-- Words in S starting with bit b, with head stripped -/
def tailsOf (b : Bool) (S : Code) : Code :=
  (S.filter (fun w => w.head? = some b)).image List.tail

/-! ## 3. Core Lemmas -/

lemma prefixFree_singleton_nil {S : Code}
    (hpf : PrefixFree S) (h_in : [] ∈ S) : S = {[]} := by
  ext w
  constructor
  · intro hw
    have h_eq : [] = w := hpf _ h_in _ hw List.nil_prefix
    rw [← h_eq]
    exact Finset.mem_singleton_self []
  · intro hw
    simp at hw
    subst hw
    exact h_in

lemma mem_tailsOf {S : Code} {b : Bool} {t : Word} :
    t ∈ tailsOf b S ↔ ∃ w, w ∈ S ∧ w.head? = some b ∧ w.tail = t := by
  classical
  -- expand tailsOf = image tail (filter ...)
  constructor
  · intro ht
    -- ht : t ∈ (S.filter ...).image List.tail
    rcases Finset.mem_image.mp ht with ⟨w, hwf, rfl⟩
    rcases Finset.mem_filter.mp hwf with ⟨hwS, hhead⟩
    exact ⟨w, hwS, hhead, rfl⟩
  · rintro ⟨w, hwS, hhead, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨w, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨hwS, hhead⟩

lemma length_le_tailsOf {S : Code} {b : Bool} {n : ℕ}
    (hlen : ∀ w ∈ S, w.length ≤ n+1) :
    ∀ t ∈ tailsOf b S, t.length ≤ n := by
  intro t ht
  rcases (mem_tailsOf (S:=S) (b:=b) (t:=t)).1 ht with ⟨w, hwS, hwHead, hwTail⟩
  -- want: t.length ≤ n, and we know hlen w hwS : w.length ≤ n+1
  have hwlen : w.length ≤ n+1 := hlen w hwS

  -- relate w and t via hwHead/hwTail:
  -- w must be b :: t
  have hw : w = b :: t := by
    -- same reconstruction pattern you used in prefixFree_tailsOf
    cases w with
    | nil =>
        simp at hwHead
    | cons h tl =>
        simp at hwHead hwTail
        subst hwHead
        subst hwTail
        rfl

  -- now reduce the length bound on w to length bound on t
  -- using your lemma length_le_of_cons_le
  -- rewrite hw into hwlen:
  have : (b :: t).length ≤ n + 1 := by simpa [hw] using hwlen
  exact length_le_of_cons_le (b:=b) (t:=t) (n:=n) this

lemma isPrefix_cons {x y : Word} (b : Bool) (h : x <+: y) :
    (b :: x) <+: (b :: y) := by
  rcases h with ⟨t, rfl⟩
  refine ⟨t, ?_⟩
  simp [List.cons_append]

lemma prefixFree_tailsOf {S : Code} (b : Bool) (hpf : PrefixFree S) :
    PrefixFree (tailsOf b S) := by
  intro x hx_mem y hy_mem hpre

  -- unpack membership in tailsOf using mem_tailsOf
  rcases (mem_tailsOf (S:=S) (b:=b) (t:=x)).1 hx_mem with ⟨wx, hwxS, hwxHead, hwxTail⟩
  rcases (mem_tailsOf (S:=S) (b:=b) (t:=y)).1 hy_mem with ⟨wy, hwyS, hwyHead, hwyTail⟩

  -- Reconstruct wx = b :: x from head?/tail facts
  have h_wx : wx = b :: x := by
    cases wx with
    | nil =>
        -- head? [] = none, contradiction with some b
        simp at hwxHead
    | cons h t =>
        -- head? (h::t) = some h, tail (h::t) = t
        -- So hwxHead gives h = b, and hwxTail gives t = x
        simp at hwxHead hwxTail
        subst hwxHead
        subst hwxTail
        rfl

  -- Reconstruct wy = b :: y
  have h_wy : wy = b :: y := by
    cases wy with
    | nil =>
        simp at hwyHead
    | cons h t =>
        simp at hwyHead hwyTail
        subst hwyHead
        subst hwyTail
        rfl

  -- wx.tail = x and wy.tail = y by construction
  -- show wx <+: wy using hpre (x <+: y) plus common head b
  have hpre_full : wx <+: wy := by
    rw [h_wx, h_wy]
    rcases hpre with ⟨t, rfl⟩
    refine ⟨t, ?_⟩
    simp [List.cons_append]

  -- apply prefix-freeness of S to get wx = wy
  have h_eq : wx = wy := hpf wx hwxS wy hwyS hpre_full

  -- conclude x = y by taking tails
  -- (rewrite with hwxTail / hwyTail)
  -- x = wx.tail = wy.tail = y
  calc
    x = wx.tail := by simp [hwxTail]
    _ = wy.tail := by simp [h_eq]
    _ = y := by simp [hwyTail]

lemma tail_injOn_filter_head (S : Code) (b : Bool) :
    Set.InjOn List.tail (fun w : Word => w ∈ S.filter (fun w => w.head? = some b)) := by
  intro w1 hw1 w2 hw2 htail
  have h1 : w1.head? = some b := (Finset.mem_filter.mp hw1).2
  have h2 : w2.head? = some b := (Finset.mem_filter.mp hw2).2
  cases w1 with
  | nil =>
      simp at h1
  | cons h t =>
      cases w2 with
      | nil =>
          simp at h2
      | cons h' t' =>
          -- tail equality gives t = t'
          have ht : t = t' := by simpa using htail
          -- head? equality gives h = b and h' = b
          have hb1 : h = b := by simpa using h1
          have hb2 : h' = b := by simpa using h2
          have hh : h = h' := by
            calc
              h = b  := hb1
              _ = h' := hb2.symm
          cases ht
          cases hh
          rfl


lemma pow_mass_of_head {n : ℕ} {b : Bool} {w : Word}
    (hw : w.head? = some b) :
    2^((n+1) - w.length) = 2^(n - (w.tail).length) := by
  cases w with
  | nil =>
      -- head? [] = none
      cases hw
  | cons h t =>
      -- head? (h::t) = some h, tail = t
      have : h = b := by simpa using hw
      subst this
      -- now w = b :: t
      -- (n+1) - (t.length+1) = n - t.length
      simp [Nat.add_sub_add_right]

lemma union_filter_head_eq (S : Code) (h_no_eps : [] ∉ S) :
    (S.filter (fun w => w.head? = some true)) ∪
    (S.filter (fun w => w.head? = some false)) = S := by
  classical
  ext w
  constructor
  · intro hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact (Finset.mem_filter.mp hw).1
    · exact (Finset.mem_filter.mp hw).1
  · intro hwS
    cases w with
    | nil =>
        exact (h_no_eps hwS).elim
    | cons h t =>
        cases h with
        | true =>
            apply Finset.mem_union.mpr
            left
            exact Finset.mem_filter.mpr ⟨hwS, by simp⟩
        | false =>
            apply Finset.mem_union.mpr
            right
            exact Finset.mem_filter.mpr ⟨hwS, by simp⟩

lemma disjoint_filter_head (S : Code) :
    Disjoint (S.filter (fun w => w.head? = some true))
             (S.filter (fun w => w.head? = some false)) := by
  classical
  refine Finset.disjoint_left.2 ?_
  intro w hwT hwF
  have hT : w.head? = some true := (Finset.mem_filter.mp hwT).2
  have hF : w.head? = some false := (Finset.mem_filter.mp hwF).2
  cases w with
  | nil =>
      simp at hT
  | cons h t =>
      simp at hT hF
      subst h
      contradiction

/-- The "Mass Split" Identity -/
lemma countMass_split {n : ℕ} {S : Code} (h_no_eps : [] ∉ S) :
    countMass (n+1) S =
    countMass n (tailsOf true S) + countMass n (tailsOf false S) := by
  classical

  -- A branch lemma: rewrite the head-filtered sum as the tail-image sum.
  have branch (b : Bool) :
      (∑ w ∈ S.filter (fun w => w.head? = some b), 2^((n+1) - w.length))
        =
      countMass n (tailsOf b S) := by
    -- unfold RHS
    unfold countMass tailsOf
    -- RHS is: ∑ t ∈ (filter ...).image tail, 2^(n - t.length)
    -- rewrite it using sum_image (needs tail injective on that filter)
    have hinj :
        Set.InjOn List.tail (↑(S.filter (fun w => w.head? = some b)) : Set Word) := by
      intro w1 hw1 w2 hw2 htail
      -- here hw1 : w1 ∈ (↑(filter ...) : Set Word), i.e. w1 ∈ filter ...
      -- so you can use Finset.mem_filter.mp hw1 after rewriting
      have h1 : w1.head? = some b := (Finset.mem_filter.mp hw1).2
      have h2 : w2.head? = some b := (Finset.mem_filter.mp hw2).2
      cases w1 with
      | nil => simp at h1
      | cons h t =>
          cases w2 with
          | nil => simp at h2
          | cons h' t' =>
              have ht : t = t' := by simpa using htail
              have hb1 : h = b := by simpa using h1
              have hb2 : h' = b := by simpa using h2
              have hh : h = h' := by
                calc
                  h = b  := hb1
                  _ = h' := hb2.symm
              cases ht; cases hh; rfl

    -- Turn the sum over the image into a sum over the source
    --   ∑ t ∈ (Sb.image tail), g t = ∑ w in Sb, g (tail w)
    have h_image :
            (∑ t ∈ (S.filter (fun w => w.head? = some b)).image List.tail,
                2 ^ (n - t.length))
              =
            (∑ w ∈ (S.filter (fun w => w.head? = some b)),
                2 ^ (n - w.tail.length)) := by
          -- The goal matches the theorem `sum_image` exactly
          rw [Finset.sum_image hinj]

    -- Now rewrite each term using pow_mass_of_head (symm direction)
    have h_terms :
        (∑ w ∈ (S.filter (fun w => w.head? = some b)),
            2^(n - (List.tail w).length))
          =
        (∑ w ∈ (S.filter (fun w => w.head? = some b)),
            2^((n+1) - w.length)) := by
      refine Finset.sum_congr rfl ?_
      intro w hw
      have hwHead : w.head? = some b := (Finset.mem_filter.mp hw).2
      -- pow_mass_of_head: 2^((n+1) - w.length) = 2^(n - (tail w).length)
      -- so we use it symmetrically
      simpa using (pow_mass_of_head (n := n) (b := b) (w := w) hwHead).symm

    -- Combine the two rewrites
    -- Goal at this point is:
    --   (∑ w in filter, 2^((n+1) - w.length)) = (∑ t in image, 2^(n - t.length))
    -- We have (image sum) = (tail-sum) = (original sum), so just chain and symm.
    calc
      (∑ w ∈ S.filter (fun w => w.head? = some b), 2^((n+1) - w.length))
          =
        (∑ w ∈ S.filter (fun w => w.head? = some b), 2^(n - (List.tail w).length)) := by
          symm
          exact h_terms
      _ =
        (∑ t ∈ (S.filter (fun w => w.head? = some b)).image List.tail, 2^(n - t.length)) := by
          symm
          exact h_image

  -- Now split the sum over S into head=true and head=false (since [] ∉ S).
  have hunion :
      (S.filter (fun w => w.head? = some true)) ∪
      (S.filter (fun w => w.head? = some false)) = S :=
    union_filter_head_eq S h_no_eps

  have hdisj :
      Disjoint (S.filter (fun w => w.head? = some true))
               (S.filter (fun w => w.head? = some false)) :=
    disjoint_filter_head S

  -- Expand countMass (n+1) S as sum over the union, then rewrite each branch via `branch`.
  -- countMass (n+1) S = ∑ w in S, 2^((n+1) - |w|)
  --                  = sum over filter(true) + sum over filter(false)
  --                  = countMass n tailsOf(true) + countMass n tailsOf(false)
  unfold countMass
  -- rewrite S as union of the two filters
  have :
      (∑ w ∈ S, 2^((n+1) - w.length))
        =
      (∑ w ∈ S.filter (fun w => w.head? = some true), 2^((n+1) - w.length))
        +
      (∑ w ∈ S.filter (fun w => w.head? = some false), 2^((n+1) - w.length)) := by
    -- swap S for the union using hunion, then apply sum_union
    calc
      (∑ w ∈ S, 2^((n+1) - w.length))
          =
        (∑ w ∈ (S.filter (fun w => w.head? = some true)) ∪
                 (S.filter (fun w => w.head? = some false)),
            2^((n+1) - w.length)) := by
              simp [hunion]
      _ =
        (∑ w ∈ S.filter (fun w => w.head? = some true), 2^((n+1) - w.length))
          +
        (∑ w ∈ S.filter (fun w => w.head? = some false), 2^((n+1) - w.length)) := by
              simp [Finset.sum_union, hdisj]

  -- finish by rewriting each branch with `branch`
  calc
    (∑ w ∈ S, 2^((n+1) - w.length))
        =
      (∑ w ∈ S.filter (fun w => w.head? = some true), 2^((n+1) - w.length))
        +
      (∑ w ∈ S.filter (fun w => w.head? = some false), 2^((n+1) - w.length)) := this
    _ =
      countMass n (tailsOf true S) + countMass n (tailsOf false S) := by
        simp [branch]


/-! ## 4. The Inductive Step (Decoupled) -/

/--
  The inductive step lemma.
  Notice it takes `ih` (Inductive Hypotheses) as arguments,
  rather than calling the theorem recursively.
-/
lemma kraft_step_lemma
    {n : ℕ} {S : Code}
    (hpf : PrefixFree S)
    (hlen : ∀ w ∈ S, w.length ≤ n + 1)
    (ih_true : countMass n (tailsOf true S) ≤ 2^n)   -- Given by Induction
    (ih_false : countMass n (tailsOf false S) ≤ 2^n) -- Given by Induction
    : countMass (n+1) S ≤ 2^(n+1) := by
  by_cases h_eps : [] ∈ S
  · -- Case 1: S = {[]}
    have hS : S = {[]} := prefixFree_singleton_nil hpf h_eps
    subst hS
    -- Mass of {[]} at depth n+1 is 2^((n+1)-0) = 2^(n+1)
    simp [countMass]
  · -- Case 2: Split
    rw [countMass_split h_eps]
    -- 2^n + 2^n = 2^(n+1)
    calc
      countMass n (tailsOf true S) + countMass n (tailsOf false S)
        ≤ 2^n + 2^n := Nat.add_le_add ih_true ih_false
      _ = 2^(n+1)   := pow_two_add_self n

/-! ## 5. Main Theorem -/
theorem kraft_inequality_nat (n : ℕ) (S : Code)
    (hpf : PrefixFree S)
    (hlen : ∀ w ∈ S, w.length ≤ n) :
    countMass n S ≤ 2^n := by
  induction n generalizing S with
  | zero =>
    classical
    -- Base case: n = 0
    by_cases h : S = ∅
    · subst h
      simp [countMass]
    · -- S is nonempty, show S = {[]}
      have hne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr h
      rcases hne with ⟨w, hw⟩
      have hwlen : w.length ≤ 0 := hlen w hw
      have hw0 : w.length = 0 := Nat.eq_zero_of_le_zero hwlen
      have wnil : w = [] := List.length_eq_zero_iff.1 hw0
      have h_in : [] ∈ S := by simpa [wnil] using hw
      have h_sing : S = {[]} := prefixFree_singleton_nil hpf h_in
      subst h_sing
      simp [countMass]
  | succ n ih =>
    apply kraft_step_lemma hpf hlen
    · -- IH for True branch
      have hlen_true : ∀ w ∈ tailsOf true S, w.length ≤ n :=
        length_le_tailsOf (S:=S) (b:=true) (n:=n) hlen
      exact ih (tailsOf true S) (prefixFree_tailsOf true hpf) hlen_true
    · -- IH for False branch
      have hlen_false : ∀ w ∈ tailsOf false S, w.length ≤ n :=
        length_le_tailsOf (S:=S) (b:=false) (n:=n) hlen
      exact ih (tailsOf false S) (prefixFree_tailsOf false hpf) hlen_false


def kraftSumQ (S : Code) : ℚ :=
  ∑ w ∈ S, ((2 : ℚ) ^ w.length)⁻¹


theorem kraft_inequality_Q (S : Code) (hpf : PrefixFree S) :
    kraftSumQ S ≤ 1 := by
  classical
  by_cases hS : S = ∅
  · subst hS
    simp [kraftSumQ]
  ·
    -- choose a uniform length bound n (finite code)
    let n : ℕ := S.sup List.length
    have hlen : ∀ w ∈ S, w.length ≤ n := by
      -- `w.length ≤ sup` lemma (Finset.le_sup / le_csSup / etc.)
      -- depends on which `sup` lemma you use
      intro w hw
      -- exact Finset.le_sup (s := S) (f := List.length) hw
      exact Finset.le_sup (s := S) (f := List.length) hw

    -- apply your nat theorem
    have hNat : countMass n S ≤ 2^n :=
      kraft_inequality_nat n S hpf hlen

    -- cast to ℚ and rewrite LHS/RHS into powers over ℚ
    have hQ : (∑ w ∈ S, (2 : ℚ) ^ (n - w.length)) ≤ (2 : ℚ) ^ n := by
      exact_mod_cast hNat

    -- relate truncated sum to scaled Kraft sum
    have hScale :
        (∑ w ∈ S, (2 : ℚ) ^ (n - w.length))
          =
        (2 : ℚ) ^ n * kraftSumQ S := by
      -- 1. Unfold definition and distribute 2^n into the sum
      unfold kraftSumQ
      rw [Finset.mul_sum]
      -- 2. Focus on term-wise equality
      refine Finset.sum_congr rfl ?_
      intro w hw
      -- 3. Use the exponent subtraction law: 2^(n-k) = 2^n / 2^k
      --    (Note: 2^n * (2^k)⁻¹ is definitionally 2^n / 2^k)
      rw [← div_eq_mul_inv]
      -- 4. Apply pow_sub₀ (requires base ≠ 0 and exponent inequality)
      exact pow_sub₀ (2 : ℚ) two_ne_zero (hlen w hw)

    -- combine and cancel the positive factor (2^n)
    have hPowPos : 0 < (2 : ℚ) ^ n := by
      apply Rat.pow_pos
      norm_num -- Proves 0 < 2 automatically

    -- rewrite hQ using hScale
    have h_ineq : (2 : ℚ) ^ n * kraftSumQ S ≤ (2 : ℚ) ^ n := by
      rw [← hScale]
      exact hQ
    nth_rw 2 [← mul_one ((2 : ℚ) ^ n)] at h_ineq
    apply Rat.le_of_mul_le_mul_left at h_ineq
    exact h_ineq hPowPos
