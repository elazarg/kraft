/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.Order.Sub.Basic

import Mathlib.Tactic.NormNum.Basic

import Kraft.Helpers

namespace Digits

open Nat

/-- Fixed-width base-`b` digits, **little-endian** (least significant digit first).

`natToDigitsLE b n width` has length `width`, and digit `i` is `(n / b^i) % b`. -/
def natToDigitsLE (b n width : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin width => (n / b ^ (i : ℕ)) % b)

/-- Big-endian base-`b` digits of `n`, padded/truncated to length `width`. -/
def natToDigitsBE (b n width : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin width => n / b^(width - 1 - (i : ℕ)) % b)

@[simp] lemma natToDigitsBE_length (b n width : ℕ) :
    (natToDigitsBE b n width).length = width := by
  simp [natToDigitsBE]

/--
Key bridge: taking the first `w` BE digits of a `v`-digit encoding is the same as
encoding `m / b^(v-w)` in width `w`.

This is the “base-`b` analogue” of shifting right to drop low digits.
-/
lemma natToDigitsBE_div_eq_take
    {b m w v : ℕ} (hb : 0 < b) (hvw : w ≤ v) :
    natToDigitsBE b (m / b^(v - w)) w
      = (natToDigitsBE b m v).take w := by
  -- ext by index
  apply List.ext_get
  · -- lengths
    simp [natToDigitsBE, List.length_take, Nat.min_eq_left (by simpa using hvw)]
  · intro n hn1 hn2
    -- `n < w`
    have hnw : n < w := by simpa [natToDigitsBE_length] using hn1
    have hnv : n < v := lt_of_lt_of_le hnw hvw

    -- evaluate both sides at index `n`
    -- Left: digit of `m / b^(v-w)` at place `(w-1-n)`
    -- Right: digit of `m` at place `(v-1-n)` (because take keeps MSBs)
    simp [List.getElem_take, natToDigitsBE]
    --   (m / b^(v-w)) / b^(w-1-n) % b = m / b^(v-1-n) % b
    -- do the div/div/pow algebra
    have hbpow : 0 < b^(v - w) := Nat.pow_pos hb
    have hbpow2 : 0 < b^(w - 1 - n) := Nat.pow_pos hb
    -- rewrite the nested division
    -- (m / B) / C = m / (B*C)
    rw [Nat.div_div_eq_div_mul]
    -- and collapse exponents
    have hexp :
        (v - w) + (w - 1 - n) = (v - 1 - n) := by
      omega
    -- turn `b^(a+b)` into `b^a * b^b`
    -- so `b^(v-w) * b^(w-1-n) = b^(v-1-n)`
    -- then finish by rewriting that product
    -- (the `simp [pow_add, hexp, mul_assoc]` usually works)
    rw [<-Nat.pow_add, hexp]


lemma natToDigitsLE_succ (b n w : ℕ) :
    natToDigitsLE b n (w+1)
      = (n % b) :: natToDigitsLE b (n / b) w := by
  -- `ofFn` over `Fin (w+1)` splits into head + ofFn over tail indices
  simp [natToDigitsLE, List.ofFn_succ]
  ext i
  -- 1) Normalize the RHS: (n / b) / b^i = n / (b * b^i)
  have hR : n / b / b ^ (i : ℕ) = n / (b * b ^ (i : ℕ)) := by
    simp [Nat.div_div_eq_div_mul]

  -- 2) Normalize the LHS denom: b^(i+1) = b * b^i (up to comm)
  have hPow : b ^ ((i : ℕ) + 1) = b * b ^ (i : ℕ) := by
    -- `pow_succ` gives `b^i * b`; commute to `b * b^i`
    simp [Nat.pow_succ, Nat.mul_comm]

  have hL : n / b ^ ((i : ℕ) + 1) = n / (b * b ^ (i : ℕ)) := by
    -- rewrite the denominator using hPow
    simp [hPow]

  -- 3) Rewrite both sides and finish by reflexivity
  simp [hL, hR]


lemma natToDigitsLE_inj {b n m width : ℕ}
    (hb0 : b ≠ 0)
    (hn : n < b ^ width) (hm : m < b ^ width)
    (h : natToDigitsLE b n width = natToDigitsLE b m width) :
    n = m := by
  induction width generalizing n m with
  | zero =>
      -- b^0 = 1, so n,m < 1
      have hn1 : n < 1 := by simpa using hn
      have hm1 : m < 1 := by simpa using hm
      have hn0 : n = 0 := (Nat.lt_one_iff.mp hn1)
      have hm0 : m = 0 := (Nat.lt_one_iff.mp hm1)
      simp [hn0, hm0]
  | succ w ih =>
      -- unfold the (w+1)-digits into head+tail
      have hsN :
          natToDigitsLE b n (w+1) = (n % b) :: natToDigitsLE b (n / b) w :=
        natToDigitsLE_succ b n w
      have hsM :
          natToDigitsLE b m (w+1) = (m % b) :: natToDigitsLE b (m / b) w :=
        natToDigitsLE_succ b m w

      have h' :
          (n % b) :: natToDigitsLE b (n / b) w
            = (m % b) :: natToDigitsLE b (m / b) w := by
        simpa [hsN, hsM] using h

      have hmod : n % b = m % b := (List.cons.inj h').1
      have htail : natToDigitsLE b (n / b) w = natToDigitsLE b (m / b) w :=
        (List.cons.inj h').2

      -- bounds: n/b, m/b < b^w
      have hbpos : 0 < b := Nat.pos_of_ne_zero hb0

      have hnq : n / b < b ^ w := by
        -- want: n < (b^w) * b
        have hn' : n < (b ^ w) * b := by
          -- b^(w+1) = b^w * b
          simpa [Nat.pow_succ, Nat.mul_assoc] using hn
        exact (Nat.div_lt_iff_lt_mul hbpos).2 hn'

      have hmq : m / b < b ^ w := by
        have hm' : m < (b ^ w) * b := by
          simpa [Nat.pow_succ, Nat.mul_assoc] using hm
        exact (Nat.div_lt_iff_lt_mul hbpos).2 hm'

      have hdiv : n / b = m / b := ih hnq hmq htail
      -- reconstruct from quotient+remainder
      calc
        n = (n / b) * b + (n % b) := by
          simpa [Nat.div_add_mod] using (Nat.div_add_mod' n b).symm
        _ = (m / b) * b + (m % b) := by simp [hdiv, hmod]
        _ = m := by
          simpa [Nat.div_add_mod] using (Nat.div_add_mod' m b)


/-- BE digits reversed are LE digits.  (Works for any `b`, no assumptions.) -/
lemma natToDigitsBE_reverse (b n width : ℕ) :
    (natToDigitsBE b n width).reverse = natToDigitsLE b n width := by
  -- compare by `get?` at every index
  apply List.ext_get
  · simp [natToDigitsBE, natToDigitsLE]
  · intro i h1 h2
    -- turn the bounds into `i < width`
    have hi : i < width := by
      -- `h2 : i < (natToDigitsLE ...).length`
      simpa [natToDigitsLE] using h2

    have hwpos : 0 < width := zero_lt_of_lt hi

    -- index used by `reverse`: `width - 1 - i`
    have hidx : width - 1 - i < (natToDigitsBE b n width).length := by
      -- `width - 1 - i ≤ width - 1 < width = length`
      have hle : width - 1 - i ≤ width - 1 := Nat.sub_le _ _
      have hlt : width - 1 < width := Nat.pred_lt (Nat.ne_zero_of_lt hi)
      -- rewrite the RHS length
      simpa [natToDigitsBE] using lt_of_le_of_lt hle hlt

    -- arithmetic: reversing twice lands back on `i`
    have hsub : width - 1 - (width - 1 - i) = i := by
      have : i ≤ width - 1 := Nat.le_pred_of_lt hi
      omega
    simp [natToDigitsBE, natToDigitsLE, hsub]

/-- `natToDigitsBE` is injective for `n,m < b^width`. -/
lemma natToDigitsBE_inj {b n m width : ℕ}
    (hb0 : b ≠ 0)
    (hn : n < b ^ width) (hm : m < b ^ width)
    (h : natToDigitsBE b n width = natToDigitsBE b m width) :
    n = m := by
  -- reverse both sides, then rewrite BE.reverse to LE
  have hrev : (natToDigitsBE b n width).reverse = (natToDigitsBE b m width).reverse :=
    congrArg List.reverse h
  have hLE : natToDigitsLE b n width = natToDigitsLE b m width := by
    -- use the bridge on both sides
    simpa [natToDigitsBE_reverse] using hrev
  -- finish with your LE injectivity lemma
  exact natToDigitsLE_inj (b := b) (n := n) (m := m) (width := width) hb0 hn hm hLE

/--
Prefix characterization (MSB-first): `natToDigitsBE b n w` is a prefix of `natToDigitsBE b m v`
iff `w ≤ v` and dividing `m` by `b^(v-w)` yields `n`.

The bounds `n < b^w`, `m < b^v` are needed because the fixed-width encoding truncates higher digits.
-/
lemma natToDigitsBE_prefix_iff_div
    {b n m w v : ℕ} (hb : 0 < b)
    (hn : n < b^w) (hm : m < b^v) :
    natToDigitsBE b n w <+: natToDigitsBE b m v
      ↔ w ≤ v ∧ m / b^(v - w) = n := by
  constructor
  · intro hpre
    have hwv : w ≤ v := by
      -- length monotonicity of prefix
      have := hpre.length_le
      simpa [natToDigitsBE_length] using this

    -- turn prefix into an equality about `take`
    have ht_take : (natToDigitsBE b m v).take w = natToDigitsBE b n w := by
      rcases hpre with ⟨t, n_append⟩
      rw [<-n_append]
      simp [natToDigitsBE_length]

    -- use the div/take bridge:
    -- digits of (m / b^(v-w)) at width w = take w digits of m at width v
    have hdigits :
        natToDigitsBE b (m / b^(v - w)) w = natToDigitsBE b n w := by
      calc
        natToDigitsBE b (m / b^(v - w)) w
            = (natToDigitsBE b m v).take w := natToDigitsBE_div_eq_take (b:=b) (m:=m) hb hwv
        _   = natToDigitsBE b n w := ht_take

    -- conclude quotient equality by injectivity of BE encoding on the bounded range.
    -- You said you already proved the general `natToDigitsLE_inj`; typically you prove
    -- `natToDigitsBE_inj` from it (reverse index), then use it here.
    have hq_lt : m / b^(v - w) < b^w := by
      -- from hm: m < b^v = b^(v-w) * b^w
      have : m < b^(v - w) * b^w := by
        -- because v = (v-w) + w when w ≤ v
        have : b^v = b^(v - w) * b^w := by
          -- `pow_add` with `v = (v-w)+w`
          -- `Nat.sub_add_cancel hwv : v - w + w = v`
          rw [<-Nat.pow_add]
          simp_all only [Nat.sub_add_cancel]
        -- rewrite hm using that factorization
        simpa [this] using hm
      exact Nat.div_lt_of_lt_mul this

    -- bound the quotient: (m / b^(v-w)) < b^w
    have hb0 : b ≠ 0 := Nat.ne_of_gt hb

    -- bridge: take w digits of BE(v) = BE(w) of quotient
    have hdigits :
        natToDigitsBE b (m / b^(v - w)) w = natToDigitsBE b n w := by
      calc
        natToDigitsBE b (m / b^(v - w)) w
            = (natToDigitsBE b m v).take w := natToDigitsBE_div_eq_take (b:=b) (m:=m) (w:=w) (v:=v) hb hwv
        _   = natToDigitsBE b n w := ht_take

    -- injectivity on width w gives quotient = n
    have hdiv : m / b^(v - w) = n := by
      -- use your BE injectivity lemma (likely proved via reverse+LE_inj)
      exact natToDigitsBE_inj (b:=b) (n:=m / b^(v - w)) (m:=n) (width:=w)
            hb0 hq_lt hn hdigits
    exact ⟨hwv, hdiv⟩

  · rintro ⟨hwv, hdiv⟩
    -- show prefix by exhibiting the tail `drop w`
    refine ⟨(natToDigitsBE b m v).drop w, ?_⟩
    -- use take_append_drop: take w B ++ drop w B = B
    -- and identify take w B with natToDigitsBE b n w via the bridge + hdiv
    have ht_take : (natToDigitsBE b m v).take w = natToDigitsBE b n w := by
      -- rewrite m / ... = n
      simpa [hdiv] using (natToDigitsBE_div_eq_take (b:=b) (m:=m) (w:=w) (v:=v) hb hwv).symm

    -- now finish: B = (take w B) ++ (drop w B) = A ++ tail
    simpa [ht_take] using (List.take_append_drop w (natToDigitsBE b m v))

def natToDigitsBEFin (D n width : ℕ) (ne: 0 < D): List (Fin D) :=
  List.ofFn (fun i : Fin width =>
    ⟨ n / D^(width - 1 - (i:ℕ)) % D, Nat.mod_lt _ ne⟩ )

/-- `natToDigitsBEFin` and `natToDigitsBE` produce the same digits. -/
lemma natToDigitsBEFin_eq_map (D n w : ℕ) (hD : 0 < D) :
    (natToDigitsBEFin D n w hD).map (·.val) = natToDigitsBE D n w := by
  simp only [natToDigitsBEFin, natToDigitsBE, List.map_ofFn]
  rfl

@[simp] lemma natToDigitsBEFin_length (D n w : ℕ) (hD : 0 < D) :
    (natToDigitsBEFin D n w hD).length = w := by
  simp [natToDigitsBEFin]

variable {α : Type _} [DecidableEq α] [Fintype α] [Nonempty α]

noncomputable def natToWord (n width : ℕ) : List α :=
  (natToDigitsBEFin (Fintype.card α) n width Fintype.card_pos).map ((Fintype.equivFin α).symm)

/-- Length of `natToWord`. -/
@[simp] lemma natToWord_length {α : Type _} [DecidableEq α] [Fintype α] [Nonempty α]
    (n w : ℕ) : (natToWord n w : List α).length = w := by
  simp [natToWord]

lemma natToDigitsBEFin_prefix_iff_div
  {D n m w v : ℕ} (hD : 0 < D)
  (hn : n < D^w) (hm : m < D^v) :
  natToDigitsBEFin D n w hD <+: natToDigitsBEFin D m v hD
    ↔ w ≤ v ∧ m / D^(v - w) = n := by
  -- proof: map (·.val), rewrite with natToDigitsBEFin_eq_map,
  -- then apply natToDigitsBE_prefix_iff_div, then pull back.
  -- 1. Transform the prefix relation on Fin lists to a prefix relation on Nat lists
  --    using the injectivity of the mapping function (Fin.val).
  rw [← List.IsPrefix.map_iff Fin.val_injective]

  -- 2. Rewrite the mapped lists using the equivalence lemma `natToDigitsBEFin_eq_map`.
  --    This turns `(natToDigitsBEFin ...).map val` into `natToDigitsBE ...`.
  simp only [natToDigitsBEFin_eq_map]

  -- 3. Apply the previously proved lemma for `natToDigitsBE`.
  exact natToDigitsBE_prefix_iff_div hD hn hm

lemma natToDigitsBEFin_inj
  {D n m w : ℕ} (hD : 0 < D)
  (hn : n < D^w) (hm : m < D^w)
  (h : natToDigitsBEFin D n w hD = natToDigitsBEFin D m w hD) :
  n = m := by
  -- proof: congrArg (List.map (·.val)) h, rewrite with natToDigitsBEFin_eq_map,
  -- then use natToDigitsBE_inj.
  -- 1. Apply `map (·.val)` to both sides of the equality `h`.
  have h_map := congrArg (List.map (·.val)) h

  -- 2. Rewrite the mapped lists to their Nat equivalents.
  simp only [natToDigitsBEFin_eq_map] at h_map

  -- 3. Apply the injectivity lemma for `natToDigitsBE`.
  --    Note: We need `D ≠ 0`, which follows from `0 < D`.
  exact natToDigitsBE_inj (Nat.ne_of_gt hD) hn hm h_map

end Digits
