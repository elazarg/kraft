/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import InformationTheory.Entropy.Basic

/-!
# Conditional Entropy

This file builds finite conditional entropy on top of `entropy`, along with the standard
identities and inequalities relating it to the entropy of marginals: the chain rule,
subadditivity, the data-processing inequality, relabeling invariance, the max-entropy bound,
and the vanishing of conditional entropy on deterministic joints.

Throughout, joint distributions are functions `p : I × J → ℝ` with `0 ≤ p` and `∑ p = 1`.
Marginals and conditional weights are total functions with the zero-mass convention: whenever a
term would divide by zero, `Real.negMulLog 0 = 0`, `Real.logb b 0 = 0`, and `x / 0 = 0` make it
vanish automatically (via `simp`, not defeq), so every statement below is stated with `0 ≤ p`
rather than `0 < p`.

## Main definitions

* `fst`, `snd`: the marginals of a joint distribution `p : I × J → ℝ`.
* `condEntropy`: conditional entropy `H(Y|X) = -∑ p(i,j) logb D (p(i,j)/fst p i)`.
* `jointOfGraph`: the joint distribution supported on the graph of `g : I → J`.
* `push`: the pushforward of `p : I → ℝ` along `f : I → J`.

## Main results

* `chain_rule`: `entropy D p = entropy D (fst p) + condEntropy D p`.
* `condEntropy_le_entropy_snd`: conditioning reduces entropy, `condEntropy D p ≤ entropy D (snd p)`.
* `entropy_push_le`: the data-processing inequality, `entropy D (push f p) ≤ entropy D p`.
* `entropy_relabel`: entropy is invariant under relabeling by an equivalence.
* `entropy_le_logb_card`: the max-entropy bound, `entropy D p ≤ logb D (card I)`.
* `condEntropy_nonneg`: conditional entropy is nonnegative (`entropy_nonneg` itself lives in
  `InformationTheory.Entropy.Basic`).
* `condEntropy_of_graph`, `entropy_jointOfGraph`: conditional entropy vanishes on a
  deterministic joint.

## References

* Cover & Thomas, *Elements of Information Theory*, Chapter 2
-/

@[expose] public section

namespace InformationTheory

open Real

variable {I J : Type*} [Fintype I] [Fintype J]

/-! ### Marginals -/

/-- The first marginal of a joint distribution. -/
noncomputable def fst (p : I × J → ℝ) : I → ℝ := fun i => ∑ j, p (i, j)

/-- The second marginal of a joint distribution. -/
noncomputable def snd (p : I × J → ℝ) : J → ℝ := fun j => ∑ i, p (i, j)

omit [Fintype I] in
lemma fst_nonneg {p : I × J → ℝ} (hp : ∀ x, 0 ≤ p x) (i : I) : 0 ≤ fst p i :=
  Finset.sum_nonneg (fun j _ => hp (i, j))

omit [Fintype J] in
lemma snd_nonneg {p : I × J → ℝ} (hp : ∀ x, 0 ≤ p x) (j : J) : 0 ≤ snd p j :=
  Finset.sum_nonneg (fun i _ => hp (i, j))

omit [Fintype I] in
/-- Each coordinate of the joint is bounded by its first marginal. -/
lemma le_fst {p : I × J → ℝ} (hp : ∀ x, 0 ≤ p x) (x : I × J) : p x ≤ fst p x.1 := by
  unfold fst
  exact (Finset.single_le_sum (fun j _ => hp (x.1, j)) (Finset.mem_univ x.2)).trans_eq (by simp)

omit [Fintype J] in
/-- Each coordinate of the joint is bounded by its second marginal. -/
lemma le_snd {p : I × J → ℝ} (hp : ∀ x, 0 ≤ p x) (x : I × J) : p x ≤ snd p x.2 := by
  unfold snd
  exact (Finset.single_le_sum (fun i _ => hp (i, x.2)) (Finset.mem_univ x.1)).trans_eq (by simp)

lemma sum_fst {p : I × J → ℝ} : ∑ i, fst p i = ∑ x, p x := by
  unfold fst; rw [← Fintype.sum_prod_type]

lemma sum_snd {p : I × J → ℝ} : ∑ j, snd p j = ∑ x, p x := by
  unfold snd; rw [Finset.sum_comm, ← Fintype.sum_prod_type]

omit [Fintype I] in
/-- The marginals of a product distribution recover the factors. -/
lemma fst_prod {a : I → ℝ} {b : J → ℝ} (hb : ∑ j, b j = 1) :
    fst (fun x => a x.1 * b x.2) = a := by
  funext i
  unfold fst
  simp only
  rw [← Finset.mul_sum, hb, mul_one]

omit [Fintype J] in
/-- The marginals of a product distribution recover the factors. -/
lemma snd_prod {a : I → ℝ} {b : J → ℝ} (ha : ∑ i, a i = 1) :
    snd (fun x => a x.1 * b x.2) = b := by
  funext j
  unfold snd
  simp only
  rw [← Finset.sum_mul, ha, one_mul]

/-! ### Conditional entropy -/

/-- Conditional entropy `H(Y|X)`, written as a single joint sum divided by `log D` (matching the
style of `entropy`) rather than a per-term `logb`. Zero-mass rows vanish automatically: if
`p x = 0` the term is `0` regardless of the (possibly ill-defined) ratio inside the log. -/
noncomputable def condEntropy (D : ℕ) (p : I × J → ℝ) : ℝ :=
  (∑ x : I × J, p x * log (fst p x.1 / p x)) / log D

omit [Fintype I] in
/-- Pointwise splitting of the conditional-entropy summand: holds unconditionally, including at
`p x = 0` where both sides collapse to `0`. -/
lemma pointwise_split_fst {p : I × J → ℝ} (hp : ∀ x, 0 ≤ p x) (x : I × J) :
    p x * log (fst p x.1 / p x) = p x * log (fst p x.1) - p x * log (p x) := by
  rcases (hp x).lt_or_eq with hpx | hpx
  · rw [log_div (ne_of_gt (lt_of_lt_of_le hpx (le_fst hp x))) (ne_of_gt hpx), mul_sub]
  · simp [← hpx]

omit [Fintype I] in
/-- Grouping a row of the joint sum by its first coordinate collapses to the marginal term. -/
lemma sum_fst_mul_log_fst {p : I × J → ℝ} (i : I) :
    ∑ j, p (i, j) * log (fst p i) = fst p i * log (fst p i) := by
  rw [← Finset.sum_mul]; rfl

omit [Fintype J] in
/-- Grouping a column of the joint sum by its second coordinate collapses to the marginal term. -/
lemma sum_snd_mul_log_snd {p : I × J → ℝ} (j : J) :
    ∑ i, p (i, j) * log (snd p j) = snd p j * log (snd p j) := by
  rw [← Finset.sum_mul]; rfl

lemma sum_condEntropy_split {p : I × J → ℝ} (hp : ∀ x, 0 ≤ p x) :
    ∑ x : I × J, p x * log (fst p x.1 / p x)
      = ∑ i, fst p i * log (fst p i) - ∑ x : I × J, p x * log (p x) := by
  simp_rw [pointwise_split_fst hp]
  rw [Finset.sum_sub_distrib]
  congr 1
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl (fun i _ => sum_fst_mul_log_fst i)

/-- **Chain rule**: `H(X,Y) = H(X) + H(Y|X)`. -/
theorem chain_rule (D : ℕ) {p : I × J → ℝ} (hp : ∀ x, 0 ≤ p x) :
    entropy D p = entropy D (fst p) + condEntropy D p := by
  have key : ∑ x : I × J, negMulLog (p x)
      = ∑ i, negMulLog (fst p i) + ∑ x : I × J, p x * log (fst p x.1 / p x) := by
    rw [sum_condEntropy_split hp]
    simp only [negMulLog, neg_mul, Finset.sum_neg_distrib]
    ring
  unfold entropy condEntropy
  rw [key, add_div]

/-! ### Nonnegativity -/

/-- `condEntropy` is nonnegative: conditioning never makes a code cheaper per symbol, each row's
ratio `fst p x.1 / p x` is at least `1`. -/
theorem condEntropy_nonneg (D : ℕ) (hD : 1 < D) {p : I × J → ℝ} (hp : ∀ x, 0 ≤ p x) :
    0 ≤ condEntropy D p := by
  have hlogD_pos : 0 < log D := log_pos (by exact_mod_cast hD)
  refine div_nonneg (Finset.sum_nonneg fun x _ => ?_) (le_of_lt hlogD_pos)
  rcases (hp x).lt_or_eq with hpx | hpx
  · have hratio_ge_one : 1 ≤ fst p x.1 / p x := (le_div_iff₀ hpx).mpr (by linarith [le_fst hp x])
    exact mul_nonneg hpx.le (log_nonneg hratio_ge_one)
  · simp [← hpx]

/-! ### Deterministic conditionals -/

/-- Conditional entropy vanishes on a joint supported on the graph of a function. -/
theorem condEntropy_of_graph (D : ℕ) {p : I × J → ℝ} {g : I → J}
    (hgraph : ∀ x : I × J, p x ≠ 0 → x.2 = g x.1) :
    condEntropy D p = 0 := by
  unfold condEntropy
  have hterm : ∀ x : I × J, p x * log (fst p x.1 / p x) = 0 := by
    intro x
    rcases eq_or_ne (p x) 0 with hpx | hpx
    · simp [hpx]
    · have hfst_eq : fst p x.1 = p x := by
        unfold fst
        rw [Finset.sum_eq_single x.2]
        · intro j _ hj
          by_contra hne
          have hj' := hgraph (x.1, j) hne
          simp only at hj'
          exact hj ((hgraph x hpx).trans hj'.symm).symm
        · intro h; exact absurd (Finset.mem_univ x.2) h
      rw [hfst_eq, div_self hpx, log_one, mul_zero]
  simp [hterm]

variable [DecidableEq J] in
/-- The joint distribution with law `q` on `I`, supported on the graph of `g : I → J`. -/
noncomputable def jointOfGraph (g : I → J) (q : I → ℝ) : I × J → ℝ :=
  fun x => if x.2 = g x.1 then q x.1 else 0

variable [DecidableEq J] in
/-- Embedding a distribution onto the graph of a function preserves entropy. -/
theorem entropy_jointOfGraph (D : ℕ) (g : I → J) (q : I → ℝ) :
    entropy D (jointOfGraph g q) = entropy D q := by
  unfold entropy jointOfGraph
  congr 1
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_eq_single (g i)]
  · simp
  · intro j _ hj
    simp only [if_neg hj]
    exact negMulLog_zero
  · intro h; exact absurd (Finset.mem_univ (g i)) h

/-! ### Relabeling invariance -/

/-- Entropy is invariant under relabeling by an equivalence. -/
theorem entropy_relabel (D : ℕ) {K L : Type*} [Fintype K] [Fintype L] (e : K ≃ L) (p : L → ℝ) :
    entropy D (p ∘ e) = entropy D p := by
  unfold entropy
  congr 1
  exact Equiv.sum_comp e (fun l => negMulLog (p l))

/-! ### Subadditivity -/

/-- **Conditioning reduces entropy**: `H(Y|X) ≤ H(Y)`, equivalently `H(X,Y) ≤ H(X) + H(Y)`. -/
theorem condEntropy_le_entropy_snd (D : ℕ) (hD : 1 < D) {p : I × J → ℝ}
    (hp : ∀ x, 0 ≤ p x) (hp_sum : ∑ x, p x = 1) :
    condEntropy D p ≤ entropy D (snd p) := by
  have hlogD_pos : 0 < log D := log_pos (by exact_mod_cast hD)
  set q : I × J → ℝ := fun x => fst p x.1 * snd p x.2 with hqdef
  have hfst_sum : ∑ i, fst p i = 1 := sum_fst.trans hp_sum
  have hsnd_sum : ∑ j, snd p j = 1 := sum_snd.trans hp_sum
  have hq_nonneg : ∀ x, 0 ≤ q x := fun x => mul_nonneg (fst_nonneg hp x.1) (snd_nonneg hp x.2)
  have hq_sum : ∑ x : I × J, q x ≤ 1 := by
    have heq2 : ∑ x : I × J, q x = (∑ i, fst p i) * (∑ j, snd p j) := by
      rw [Fintype.sum_prod_type]; simp_rw [hqdef]; rw [← Finset.sum_mul_sum]
    rw [heq2, hfst_sum, hsnd_sum]; norm_num
  have hac : ∀ x : I × J, q x = 0 → p x = 0 := by
    intro x hqx
    rcases mul_eq_zero.mp hqx with h | h
    · linarith [le_fst hp x, hp x]
    · linarith [le_snd hp x, hp x]
  have hgibbs := gibbs_sum_log_ratio_nonneg_of_ac hp hp_sum hq_nonneg hq_sum hac
  have hqlog : ∀ x : I × J, p x * log (p x / q x)
      = p x * log (p x) - p x * log (fst p x.1) - p x * log (snd p x.2) := by
    intro x
    rcases (hp x).lt_or_eq with hpx | hpx
    · have hfst_pos : 0 < fst p x.1 := lt_of_lt_of_le hpx (le_fst hp x)
      have hsnd_pos : 0 < snd p x.2 := lt_of_lt_of_le hpx (le_snd hp x)
      rw [hqdef, log_div (ne_of_gt hpx) (ne_of_gt (mul_pos hfst_pos hsnd_pos)),
        log_mul (ne_of_gt hfst_pos) (ne_of_gt hsnd_pos)]
      ring
    · simp [← hpx]
  have hqsum_eq : ∑ x : I × J, p x * log (p x / q x)
      = ∑ x : I × J, p x * log (p x) - ∑ x : I × J, p x * log (fst p x.1)
        - ∑ x : I × J, p x * log (snd p x.2) := by
    simp_rw [hqlog]; rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have hgroup1 : ∑ x : I × J, p x * log (fst p x.1) = ∑ i, fst p i * log (fst p i) := by
    rw [Fintype.sum_prod_type]; exact Finset.sum_congr rfl (fun i _ => sum_fst_mul_log_fst i)
  have hgroup2 : ∑ x : I × J, p x * log (snd p x.2) = ∑ j, snd p j * log (snd p j) := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j _ => sum_snd_mul_log_snd j)
  rw [hqsum_eq, hgroup1, hgroup2] at hgibbs
  unfold condEntropy entropy
  apply (div_le_div_iff_of_pos_right hlogD_pos).mpr
  simp_rw [pointwise_split_fst hp]
  rw [Finset.sum_sub_distrib, hgroup1]
  simp only [negMulLog, neg_mul]
  rw [Finset.sum_neg_distrib]
  linarith [hgibbs]

/-! ### Max-entropy bound -/

/-- **Max-entropy bound**: `H(p) ≤ log_D |I|`, Gibbs against the uniform distribution. -/
theorem entropy_le_logb_card (D : ℕ) (hD : 1 < D) [Nonempty I]
    {p : I → ℝ} (hp : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1) :
    entropy D p ≤ logb D (Fintype.card I) := by
  have hlogD_pos : 0 < log D := log_pos (by exact_mod_cast hD)
  have hcardR_pos : (0 : ℝ) < (Fintype.card I : ℝ) := by exact_mod_cast Fintype.card_pos
  set q : I → ℝ := fun _ => 1 / (Fintype.card I : ℝ) with hqdef
  have hq_pos : ∀ i, 0 < q i := fun i => by rw [hqdef]; positivity
  have hq_sum : ∑ i, q i ≤ 1 := by
    rw [hqdef]
    simp only [Finset.sum_const, Finset.card_univ]
    rw [nsmul_eq_mul, mul_one_div, div_self (ne_of_gt hcardR_pos)]
  have hac : ∀ i, q i = 0 → p i = 0 := fun i hqi => absurd hqi (ne_of_gt (hq_pos i))
  have hgibbs := gibbs_sum_log_ratio_nonneg_of_ac hp hp_sum (fun i => (hq_pos i).le) hq_sum hac
  have hqconst : ∀ i, log (q i) = -log (Fintype.card I) := fun i => by rw [hqdef]; simp
  have hsum2 : ∑ i, p i * log (p i / q i) = ∑ i, p i * log (p i) + log (Fintype.card I) := by
    have hsplit : ∀ i, p i * log (p i / q i) = p i * log (p i) - p i * log (q i) := by
      intro i
      rcases (hp i).lt_or_eq with hpi | hpi
      · rw [log_div (ne_of_gt hpi) (ne_of_gt (hq_pos i)), mul_sub]
      · simp [← hpi]
    simp_rw [hsplit, hqconst]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hp_sum, one_mul, sub_neg_eq_add]
  rw [hsum2] at hgibbs
  have hentropy_eq : entropy D p = - (∑ i, p i * log (p i)) / log D := by
    unfold entropy
    simp only [negMulLog, neg_mul]
    rw [Finset.sum_neg_distrib]
  rw [hentropy_eq, logb, div_le_div_iff_of_pos_right hlogD_pos]
  linarith

/-! ### Data processing -/

variable [DecidableEq J] in
/-- The pushforward of `p : I → ℝ` along `f : I → J`. -/
noncomputable def push (f : I → J) (p : I → ℝ) : J → ℝ :=
  fun j => ∑ i ∈ Finset.univ.filter (fun i => f i = j), p i

variable [DecidableEq J] in
/-- **Data-processing inequality**: applying a deterministic function never increases entropy.
Proof route: embed `p` on the graph of `f` (`entropy_jointOfGraph`), swap the two coordinates
(a bijection, `entropy_relabel`), then the chain rule on the swapped joint gives
`entropy D p = entropy D (push f p) + condEntropy D (…)`, and conditional entropy is
nonnegative. -/
theorem entropy_push_le (D : ℕ) (hD : 1 < D) {f : I → J} {p : I → ℝ} (hp : ∀ i, 0 ≤ p i) :
    entropy D (push f p) ≤ entropy D p := by
  set joint : I × J → ℝ := jointOfGraph f p with hjointdef
  set swapped : J × I → ℝ := joint ∘ (Equiv.prodComm J I) with hswappeddef
  have hswap_nonneg : ∀ y : J × I, 0 ≤ swapped y := by
    intro y
    rw [hswappeddef, hjointdef]
    simp only [Function.comp_apply, jointOfGraph]
    split
    · exact hp _
    · exact le_refl 0
  have hfst_swapped : fst swapped = push f p := by
    funext j
    unfold fst push
    simp only [hswappeddef, hjointdef, jointOfGraph, Function.comp_apply, Equiv.prodComm_apply,
      Prod.swap_prod_mk]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases h : f i = j
    · simp [h]
    · simp [h, Ne.symm h]
  have hchain := chain_rule D hswap_nonneg
  rw [hfst_swapped] at hchain
  have hcond_nonneg := condEntropy_nonneg D hD hswap_nonneg
  have hrelabel : entropy D swapped = entropy D joint := by
    rw [hswappeddef]; exact entropy_relabel D (Equiv.prodComm J I) joint
  have hjoint_eq : entropy D joint = entropy D p := entropy_jointOfGraph D f p
  rw [hjoint_eq] at hrelabel
  linarith [hchain, hcond_nonneg, hrelabel]

end InformationTheory
