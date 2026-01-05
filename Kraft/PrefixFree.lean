import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.BigOperators.Fin

abbrev Word := List Bool
abbrev Code := Finset Word

/-- Prefix-free set of binary words -/
def PrefixFree (S : Code) : Prop :=
  ∀ ⦃x y⦄, x ∈ S → y ∈ S → x <+: y → x = y

lemma prefixFree_singleton_nil {S : Code}
    (hpf : PrefixFree S) (h_in : ([] : Word) ∈ S) : S = {[]} := by
  ext w
  constructor
  · intro hw
    have : ([] : Word) = w := hpf h_in hw List.nil_prefix
    simp [this]
  · intro hw
    simp at hw
    subst hw
    exact h_in

lemma eq_cons_of_head?_eq_some {w : Word} {b : Bool} (h : w.head? = some b) :
    w = b :: w.tail := by
  -- `List.eq_cons_of_mem_head? : x ∈ head? w → w = x :: tail w`
  apply List.eq_cons_of_mem_head?
  -- membership in `Option`: `b ∈ some b`
  simp [h]


/-! ## Splitting Infrastructure -/

/-- Words in S starting with bit b, with head stripped -/
def tailsOf (b : Bool) (S : Code) : Code :=
  (S.filter (fun w => w.head? = some b)).image List.tail

/-- Tails of a prefix-free code are also prefix-free -/
lemma prefixFree_tailsOf {S : Code} {b : Bool} (hpf : PrefixFree S) :
    PrefixFree (tailsOf b S) := by
  intro t1 t2 ht1 ht2 hpre
  -- 1. Extract original words w1 and w2 from the image
  -- 2. Peel the filter logic to get properties of w1 (and w2)
  rw [tailsOf, Finset.mem_image] at ht1 ht2
  rcases ht1 with ⟨w1, hw1_mem, rfl⟩
  replace ⟨w1_mem, w1_head_eqb⟩ := Finset.mem_filter.mp hw1_mem

  rcases ht2 with ⟨w2, hw2_mem, rfl⟩
  replace ⟨w2_mem, w2_head_eqb⟩ := Finset.mem_filter.mp hw2_mem

  -- 3. Lift the prefix relation to the full words (w1 <+: w2)
  have h_full : w1 <+: w2 := by
    rw [List.eq_cons_of_mem_head? w1_head_eqb,
        List.eq_cons_of_mem_head? w2_head_eqb]
    -- 'simp' automatically knows b::t1 <+: b::t2 ↔ t1 <+: t2
    simp [hpre]

  -- 4. Conclude t1 = t2 from w1 = w2
  --    If b::t1 = b::t2, then t1 = t2.
  rw [hpf w1_mem w2_mem h_full]
