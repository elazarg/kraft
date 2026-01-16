/- Copyright (c) 2026 Elazar Gershuni.
Released under MIT license.
Authors: Elazar Gershuni -/
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.List.Basic
import Mathlib.Data.Fin.Basic

import Kraft.Helpers

namespace Kraft

open Nat

/-!
Internal implementation: fixed-width digits built from `Nat.digits`.
Public API at the bottom exposes only:

* `kraftCodeword`
* `kraftCodeword_length`
* `kraftCodeword_prefix_iff_div`
* `kraftCodeword_inj`
-/

section BE

/-- Fixed-width little-endian digits: take low digits, pad with zeros. -/
private def digitsLE_fixed (D n width : ℕ) : List ℕ :=
  let ds := (Nat.digits D n).take width
  ds ++ List.replicate (width - ds.length) 0

/-- Fixed-width big-endian digits. -/
private def digitsBE_fixed (D n width : ℕ) : List ℕ :=
  (digitsLE_fixed D n width).reverse

private lemma digitsLE_fixed_length (D n width : ℕ) :
    (digitsLE_fixed D n width).length = width := by
  unfold digitsLE_fixed
  set ds := (Nat.digits D n).take width with hds
  -- length(ds ++ replicate (width - ds.length) 0) = width
  simp [ds, List.length_append, List.length_replicate]

private lemma digitsBE_fixed_length (D n width : ℕ) :
    (digitsBE_fixed D n width).length = width := by
  simp [digitsBE_fixed, digitsLE_fixed_length]

private lemma digitsLE_fixed_lt_base {D n width d : ℕ} (hD : 1 < D) :
    d ∈ digitsLE_fixed D n width → d < D := by
  intro hd
  unfold digitsLE_fixed at hd
  set ds := (Nat.digits D n).take width with hds
  -- membership in append
  rcases List.mem_append.mp hd with hd' | hd'
  · -- comes from `take`, hence from `digits`
    exact Nat.digits_lt_base hD (List.mem_of_mem_take (by simpa [hds] using hd'))
  · -- comes from replicate zeros
    have : d = 0 := List.eq_of_mem_replicate (by simpa using hd')
    subst this
    exact lt_trans Nat.zero_lt_one hD

private lemma digitsBE_fixed_lt_base {D n width d : ℕ} (hD : 1 < D) :
    d ∈ digitsBE_fixed D n width → d < D := by
  intro hd
  have : d ∈ digitsLE_fixed D n width := by
    -- mem(reverse xs) ↔ mem xs
    simpa [digitsBE_fixed] using List.mem_reverse.mp hd
  exact digitsLE_fixed_lt_base hD this

/-- Under `n < D^width`, `ofDigits` of the fixed-width LE digits is `n`. -/
private lemma ofDigits_digitsLE_fixed
  {D n width : ℕ} (hD : 1 < D) (hn : n < D^width) :
  Nat.ofDigits D (digitsLE_fixed D n width) = n := by
  -- `digits_length_le_iff` gives `(digits D n).length ≤ width`
  have hlen : (Nat.digits D n).length ≤ width :=
    (Nat.digits_length_le_iff hD n).2 hn
  -- thus `take width` is no-op
  have ht : (Nat.digits D n).take width = Nat.digits D n :=
    List.take_of_length_le hlen
  unfold digitsLE_fixed
  -- `ofDigits` ignores trailing zeros
  simp [ht, Nat.ofDigits_append_replicate_zero, Nat.ofDigits_digits]

private lemma div_pow_lt_pow_of_lt {D m v w : ℕ} (hDpos : 0 < D) (hm : m < D^v) (hwv : w ≤ v) :
    m / D^(v-w) < D^w := by
  have hvpow : D^v = D^(v-w) * D^w := by
    calc D^v = D^((v-w)+w) := by simp [Nat.sub_add_cancel hwv]
      _ = D^(v-w) * D^w := by simp [Nat.pow_add]
  have : m < D^(v-w) * D^w := by simpa [hvpow] using hm
  have hpos : 0 < D^(v-w) := Nat.pow_pos hDpos
  exact (Nat.div_lt_iff_lt_mul hpos).2
    (by simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this)

/-- LE bridge: dropping `(v-w)` low digits corresponds to dividing by `D^(v-w)`. -/
private lemma digitsLE_fixed_drop_eq_div
  {D m w v : ℕ} (hD : 1 < D) (hm : m < D^v) (hvw : w ≤ v) :
  (digitsLE_fixed D m v).drop (v - w) =
    digitsLE_fixed D (m / D^(v-w)) w := by
  have hDpos : 0 < D := lt_trans Nat.zero_lt_one hD

  have wL :
      ∀ d ∈ (digitsLE_fixed D m v).drop (v-w), d < D := by
    intro d hd
    exact digitsLE_fixed_lt_base hD
      (List.mem_of_mem_drop hd)

  have wR :
      ∀ d ∈ digitsLE_fixed D (m / D^(v-w)) w, d < D := by
    intro d hd
    exact digitsLE_fixed_lt_base hD hd

  have h_ofDigits_L :
      Nat.ofDigits D ((digitsLE_fixed D m v).drop (v-w))
        = Nat.ofDigits D (digitsLE_fixed D m v) / D^(v-w) := by
    -- `ofDigits_div_pow_eq_ofDigits_drop` gives `/` = ofDigits(drop); rearrange
    simpa [eq_comm] using
      (Nat.ofDigits_div_pow_eq_ofDigits_drop
        (p:=D) (i:=v-w) (hpos:=hDpos)
        (digits:=digitsLE_fixed D m v)
        (w₁:=fun _ => digitsLE_fixed_lt_base hD)).symm

  have hq : m / D^(v-w) < D^w := div_pow_lt_pow_of_lt hDpos hm hvw

  -- conclude list equality by `ofDigits` injectivity (fixed length + digit bounds)
  apply Nat.ofDigits_inj_of_len_eq (b:=D) hD
  · -- length equality
    simp [digitsLE_fixed_length, hvw, Nat.sub_sub_right]
  · exact wL
  · exact wR
  · -- ofDigits equality
    calc
      Nat.ofDigits D ((digitsLE_fixed D m v).drop (v-w))
          = Nat.ofDigits D (digitsLE_fixed D m v) / D^(v-w) := h_ofDigits_L
      _   = m / D^(v-w) := by simp [ofDigits_digitsLE_fixed hD hm]
      _   = Nat.ofDigits D (digitsLE_fixed D (m / D^(v-w)) w) := by simp [ofDigits_digitsLE_fixed hD hq]

/-- BE bridge: taking `w` MSB digits corresponds to dividing by `D^(v-w)`. -/
private lemma digitsBE_fixed_take_eq_div
  {D m w v : ℕ} (hD : 1 < D) (hm : m < D^v) (hvw : w ≤ v) :
  (digitsBE_fixed D m v).take w =
    digitsBE_fixed D (m / D^(v-w)) w := by
  unfold digitsBE_fixed
  have hl : (digitsLE_fixed D m v).length = v := by
    simp [digitsLE_fixed_length]
  -- `take` on `reverse` becomes `reverse` of `drop (len - w)`
  -- `List.take_reverse` is in `Mathlib.Data.List.Basic`.
  -- Statement: `l.reverse.take n = (l.drop (l.length - n)).reverse`.
  simp [List.take_reverse, hl,
        digitsLE_fixed_drop_eq_div hD hm hvw]

/-- Nat-level prefix characterization for fixed-width BE digits. -/
private lemma digitsBE_fixed_prefix_iff_div
  {D n m w v : ℕ} (hD : 1 < D)
  (hn : n < D^w) (hm : m < D^v) :
  digitsBE_fixed D n w <+: digitsBE_fixed D m v
    ↔ w ≤ v ∧ m / D^(v-w) = n := by
  constructor
  · intro hpre
    have hwv : w ≤ v := by
      have := hpre.length_le
      simpa [digitsBE_fixed_length] using this

    -- Prefix -> take equality on length w
    have ht :
        (digitsBE_fixed D m v).take w = digitsBE_fixed D n w := by
      rcases hpre with ⟨t, ht⟩
      -- take w of both sides; use `take_append` normal form
      -- `take w (A ++ t) = A` when `A.length = w`.
      have hlenA : (digitsBE_fixed D n w).length = w := digitsBE_fixed_length D n w
      -- rewrite, then simplify
      -- `List.take_append` is the standard lemma: `take n (l1++l2) = take n l1 ++ take (n-l1.length) l2`.
      -- With `n = l1.length`, it collapses to `l1`.
      calc
        (digitsBE_fixed D m v).take w
            = ((digitsBE_fixed D n w) ++ t).take w := by simp [ht]
        _   = (digitsBE_fixed D n w) := by simp [hlenA]

    -- rewrite take via division bridge
    have hdiv_eq :
        digitsBE_fixed D (m / D^(v-w)) w = digitsBE_fixed D n w := by
      calc
        digitsBE_fixed D (m / D^(v-w)) w
            = (digitsBE_fixed D m v).take w := by
                symm
                exact digitsBE_fixed_take_eq_div hD hm hwv
        _   = digitsBE_fixed D n w := ht

    -- Turn BE equality into LE equality by reversing both sides.
    have hLE :
        digitsLE_fixed D (m / D^(v-w)) w = digitsLE_fixed D n w := by
      -- `digitsBE_fixed = reverse digitsLE_fixed`, so reversing cancels.
      simpa [digitsBE_fixed] using congrArg List.reverse hdiv_eq

    -- Turn LE equality into equality of numbers via `ofDigits_digitsLE_fixed`.
    have hDpos : 0 < D := lt_trans Nat.zero_lt_one hD
    have hq : m / D^(v-w) < D^w := div_pow_lt_pow_of_lt hDpos hm hwv

    have : m / D^(v-w) = n := by
      have h_of := congrArg (Nat.ofDigits D) hLE
      simpa
        [ ofDigits_digitsLE_fixed hD hq
        , ofDigits_digitsLE_fixed hD hn
        ] using h_of

    exact ⟨hwv, this⟩

  · rintro ⟨hwv, hdiv⟩
    -- show prefix by `take_append_drop`
    refine ⟨(digitsBE_fixed D m v).drop w, ?_⟩
    have ht :
        (digitsBE_fixed D m v).take w = digitsBE_fixed D n w := by
      have htake :=
        digitsBE_fixed_take_eq_div hD hm hwv
      simpa [hdiv] using htake
    simpa [ht] using (List.take_append_drop w (digitsBE_fixed D m v))

end BE

/- ========== PUBLIC API ========== -/

/-- Fixed-width, MSB-first digits of `n` base `D`, as `Fin D`. -/
def kraftCodeword {D: ℕ} (hD : 1 < D) (n width : ℕ) : List (Fin D) :=
  (digitsBE_fixed D n width).pmap
    (fun d hd => ⟨d, hd⟩)
    (fun _ hd => digitsBE_fixed_lt_base hD hd)

@[simp]
lemma kraftCodeword_length {D: ℕ} (hD : 1 < D) (n width : ℕ) :
    (kraftCodeword hD n width).length = width := by
  simp [kraftCodeword, digitsBE_fixed_length]

/-- Internal bridge: forgetting `Fin` gives the underlying Nat BE digits. -/
@[simp]
private lemma kraftCodeword_map_val {D: ℕ} (n width : ℕ) (hD : 1 < D) :
    (kraftCodeword hD n width).map (fun x => x.val)
      = digitsBE_fixed D n width := by
  -- general lemma: mapping `val` over `pmap (Fin.mk)` returns the original list
  have map_val_pmap_mk :
      ∀ (xs : List ℕ) (hx : ∀ d ∈ xs, d < D),
        (List.pmap (fun d hd => (⟨d, hd⟩ : Fin D)) xs hx).map (fun x => x.val) = xs := by
    intro xs hx
    induction xs with
    | nil =>
        simp [List.pmap]
    | cons a tl ih =>
        have ha : a < D := hx a (by simp)
        have htl : ∀ d ∈ tl, d < D := by
          intro d hd
          exact hx d (by simp [hd])
        simp [List.pmap, ih htl]

  unfold kraftCodeword
  simpa using map_val_pmap_mk (digitsBE_fixed D n width)
    (by
      intro d hd
      exact digitsBE_fixed_lt_base hD hd)

/-- Prefix characterization (MSB-first): prefix iff quotient agrees. -/
lemma kraftCodeword_prefix_iff_div
  {D n m w v : ℕ} (hD : 1 < D)
  (hn : n < D^w) (hm : m < D^v) :
  kraftCodeword hD n w <+: kraftCodeword hD m v
    ↔ w ≤ v ∧ m / D^(v - w) = n := by
  -- reduce prefix on `Fin` lists to prefix on Nat lists
  rw [←List.IsPrefix.map_iff Fin.val_injective]
  simp [kraftCodeword_map_val]
  exact digitsBE_fixed_prefix_iff_div hD hn hm

/-- Injectivity under the Kraft bound `n,m < D^w`. -/
lemma kraftCodeword_inj
  {D n m w : ℕ} (hD : 1 < D)
  (hn : n < D^w) (hm : m < D^w)
  (h : kraftCodeword hD n w = kraftCodeword hD m w) :
  n = m := by
  -- forget `Fin` and reduce to Nat BE equality
  have h_map := congrArg (List.map (fun x => x.val)) h
  have h_nat : digitsBE_fixed D n w = digitsBE_fixed D m w := by
    simpa [kraftCodeword_map_val] using h_map

  -- cancel reverse to get LE equality
  have h_le : digitsLE_fixed D n w = digitsLE_fixed D m w := by
    -- `digitsBE_fixed = reverse digitsLE_fixed`
    have := congrArg List.reverse h_nat
    simpa [digitsBE_fixed] using this

  -- apply `ofDigits` and use the reconstruction lemma under bounds
  have h_of := congrArg (Nat.ofDigits D) h_le
  simpa
    [ ofDigits_digitsLE_fixed hD hn
    , ofDigits_digitsLE_fixed hD hm
    ] using h_of

end Kraft
