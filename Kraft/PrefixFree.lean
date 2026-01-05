import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic

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
