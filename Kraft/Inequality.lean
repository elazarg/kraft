import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin

import Kraft.PrefixFree

open BigOperators

/-!
  # Integer Kraft Inequality
  Proving: if S is prefix-free and bounded by n, then ∑ 2^(n-|w|) ≤ 2^n.
-/

/-- Integer Kraft mass: ∑ 2^(n - |w|) -/
def countMass (n : ℕ) (S : Code) : ℕ :=
  ∑ w ∈ S, 2^(n - w.length)

/-! ## 2. Core Properties -/

/-- Length bounds are preserved (shifted by 1) in tails -/
lemma length_le_tailsOf {S : Code} {b : Bool} {n : ℕ}
    (hlen : ∀ w ∈ S, w.length ≤ n + 1) :
    ∀ t ∈ tailsOf b S, t.length ≤ n := by
  intro t ht
  -- Recover w = b :: t from the image
  rw [tailsOf, Finset.mem_image] at ht
  rcases ht with ⟨w, hw_mem, rfl⟩
  simp_all only [Finset.mem_filter, List.length_tail, tsub_le_iff_right]

/-! ## 3. The Mass Split Identity -/

/-! ## 3.1 Helper: Equivalence of Sums -/

lemma tail_injOn_filter_head1 (S : Code) (b : Bool) : ∀ w,
  w ∈ ↑({w' ∈ S | List.head? w' = some b}) -> b :: w.tail = w := by
  intro w1 hw1
  rw [<-eq_cons_of_head?_eq_some]
  apply (Finset.mem_filter.mp hw1).2

lemma tail_injOn_filter_head (S : Code) (b : Bool) :
    Set.InjOn List.tail (↑(S.filter (fun w => w.head? = some b)) : Set Word) := by
  intro w1 hw1 w2 hw2 htail
  -- tail equality ⇒ cons equality ⇒ word equality
  have : b :: List.tail w1 = b :: List.tail w2 := congrArg (fun t => b :: t) htail
  simpa [tail_injOn_filter_head1 S b w1 hw1,
         tail_injOn_filter_head1 S b w2 hw2]

/-- The sum over the filter equals the sum over the tails image. -/
lemma sum_filter_eq_mass_tails (n : ℕ) (S : Code) (b : Bool) :
    (∑ w ∈ S.filter (fun w => w.head? = some b), 2^(n + 1 - w.length)) =
    countMass n (tailsOf b S) := by
  -- 1. Align definitions
  rw [countMass, tailsOf]

  -- 2. Use `sum_image` to pull the sum back from the image to the source.
  --    Formula: ∑ y ∈ f''s, g y = ∑ x ∈ s, g (f x)   (if f is injective)
  rw [Finset.sum_image (tail_injOn_filter_head S b)]
    -- 3. Now sides match structurally. Prove the values (exponents) match.
  apply Finset.sum_congr rfl
  intro w hw

  -- 4. Arithmetic: n + 1 - |w| = n - |tail w|
  have h_len : w.length = w.tail.length + 1 := by
    cases w <;> simp_all

  rw [h_len, Nat.add_sub_add_right]

/-! ## 3.1 The Main Lemma -/

lemma countMass_split {n : ℕ} {S : Code} (h_no_eps : [] ∉ S) :
    countMass (n+1) S =
    countMass n (tailsOf true S) + countMass n (tailsOf false S) := by
  -- 1. Split total sum into (head=true) + (head=false)
  let p := fun w : Word => w.head? = some true
  rw [countMass, ← Finset.sum_filter_add_sum_filter_not S p]

  -- 2. Handle the "True" branch
  --    We just need to match the p x term to our helper lemma
  have h_true_eq :
      (∑ x ∈ S with p x, 2 ^ (n + 1 - x.length)) = countMass n (tailsOf true S) :=
    sum_filter_eq_mass_tails n S true
  rw [h_true_eq]

  -- 3. Handle the "False" branch
  --    First, show ¬p w ↔ head=false (since [] is not in S)
  have h_not_p : ∀ w ∈ S, ¬p w ↔ w.head? = some false := by
    intro w hw
    cases w with
    | nil => exact (h_no_eps hw).elim
    | cons b t => cases b <;> simp [p]

  --    Prove the two filter sets are actually equal
  have h_filter_eq : S.filter (fun w => ¬p w) = S.filter (fun w => w.head? = some false) :=
    Finset.filter_congr h_not_p

  --    Rewrite the sum using this set equality, then apply the helper lemma
  rw [h_filter_eq, sum_filter_eq_mass_tails]

/-! ## 4. Main Theorem (Induction) -/

theorem kraft_inequality_nat (n : ℕ) (S : Code)
    (hpf : PrefixFree S)
    (hlen : ∀ w ∈ S, w.length ≤ n) :
    countMass n S ≤ 2^n := by
  induction n generalizing S with
  | zero =>
    -- Base Case: Max length 0 implies S ⊆ {[]}
    by_cases h : S = ∅
    · subst h
      simp [countMass]
    · have : S = {[]} := prefixFree_singleton_nil hpf (by
        rcases Finset.nonempty_iff_ne_empty.mpr h with ⟨w, hw⟩
        have : w.length = 0 := Nat.eq_zero_of_le_zero (hlen w hw)
        simp [List.length_eq_zero_iff] at this
        subst w
        exact hw)
      subst this
      simp [countMass]
  | succ n ih =>
    -- Recursive Step
    by_cases h_eps : [] ∈ S
    · -- If [] ∈ S, then S = {[]}
      have : S = {[]} := prefixFree_singleton_nil hpf h_eps
      subst this
      simp [countMass]
    · -- Otherwise split
      rw [countMass_split h_eps]
      -- Apply IH to both branches
      have h1 := ih (tailsOf true  S) (prefixFree_tailsOf hpf) (length_le_tailsOf hlen)
      have h2 := ih (tailsOf false S) (prefixFree_tailsOf hpf) (length_le_tailsOf hlen)
      -- Algebra: A + B ≤ 2^n + 2^n = 2^(n+1)
      calc
        countMass n (tailsOf true S) + countMass n (tailsOf false S)
          ≤ 2^n + 2^n := Nat.add_le_add h1 h2
        _ = 2^(n+1)   := by ring

/-! ## 5. Rational Corollary -/

theorem kraft_inequality (S : Code) (hpf : PrefixFree S) :
    kraftSum S ≤ 1 := by
  rcases S.eq_empty_or_nonempty with rfl | hne; · simp [kraftSum]

  -- 1. Setup
  let n := S.sup List.length
  have hlen : ∀ w ∈ S, w.length ≤ n := fun _ => Finset.le_sup

  -- 2. Algebraic Identity: Integer Mass = 2^n * Rational Kraft Sum
  have h_mass_eq : countMass n S = 2^n * kraftSum S := by
    simp [countMass, kraftSum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun w hw => ?_)
    rw [← div_eq_mul_inv, pow_sub₀ 2 (by norm_num) (hlen w hw)]
    norm_cast

  -- 3. Construct the scaled inequality
  have h_scaled : 2^n * kraftSum S ≤ 2^n * 1 := calc
    2^n * kraftSum S = countMass n S := h_mass_eq.symm
    _ ≤ 2^n := by exact_mod_cast kraft_inequality_nat n S hpf hlen
    _ = 2^n * 1 := (mul_one _).symm

  -- 4. Cancel the factor 2^n
  exact Rat.le_of_mul_le_mul_left h_scaled (by apply Rat.pow_pos; norm_num)
