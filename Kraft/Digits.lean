import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.Order.Sub.Basic

import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Tactic.NormNum.Basic

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

/-- Convenient `get` lemma. -/
@[simp] lemma natToDigitsBE_get (b n width : ℕ) (i : Fin width) :
    (natToDigitsBE b n width)[i] = n / b^(width - 1 - (i : ℕ)) % b := by
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

def digit2ToBool (d : ℕ) : Bool := decide (d % 2 = 1)

def Nat.testDigit (b n i d : ℕ) : Prop :=
  (n / b^i) % b = d

/-- Converts a natural number `n` to a big-endian list of bits of length `width`.

For example, `natToBits 5 4 = [false, true, false, true]` representing 0101₂ = 5. -/
def natToBits (n width : ℕ) : List Bool :=
  List.ofFn (fun i : Fin width => n.testBit (width - 1 - i))

def natToBits' (n w : ℕ) : List Bool :=
  (natToDigitsBEFin 2 n w (by decide)).map (fun d : Fin 2 => decide (d = 1))

/-- `natToBits` is injective for numbers less than `2^width`. -/
lemma natToBits_inj {n m width : ℕ} (hn : n < 2 ^ width) (hm : m < 2 ^ width)
    (h : natToBits n width = natToBits m width) : n = m := by
      refine' Nat.eq_of_testBit_eq fun i => _
      by_cases hi : i < width
      · replace h := congr_arg (fun l => l[width - 1 - i]!) h
        unfold natToBits at h
        simp_all only [Nat.shiftRight_eq_div_pow, Nat.testBit, Nat.shiftRight_eq_div_pow]

        have hw : 0 < width := (by exact Nat.zero_lt_of_lt hi)
        have hcond : width - 1 - i < width := by
          -- ≤ width-1 < width
          have hle : width - 1 - i ≤ width - 1 := Nat.sub_le _ _
          exact lt_of_le_of_lt hle (Nat.pred_lt (by exact Nat.ne_zero_of_lt hi))

        have hsub : width - 1 - (width - 1 - i) = i := by
          -- `i ≤ width-1` since `i < width`
          have hi' : i ≤ width - 1 := Nat.le_pred_of_lt hi
          -- standard arithmetic on `Nat` subtraction
          omega

        -- extract the Bool equality from `h` and convert == to =
        have hbool : (n / 2 ^ i % 2 == 1) = (m / 2 ^ i % 2 == 1) := by simpa [hcond, hsub] using h
        simpa [Nat.beq_eq_true_eq, decide_eq_decide] using hbool

      · simp_all only [not_lt, Nat.testBit]
        rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
        rw [Nat.div_eq_of_lt (lt_of_lt_of_le hn (Nat.pow_le_pow_right (by decide) hi)), Nat.div_eq_of_lt (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide) hi))]

/-- `natToBits n w` is a prefix of `natToBits m v` iff `w ≤ v` and `m` lies in the
dyadic interval `[n·2^{v-w}, (n+1)·2^{v-w})`. This characterizes when two codewords
in our construction have a prefix relationship. -/
lemma natToBits_prefix_iff {n m w v : ℕ} (hn : n < 2 ^ w) (hm : m < 2 ^ v) :
    natToBits n w <+: natToBits m v ↔ w ≤ v ∧ n * 2 ^ (v - w) ≤ m ∧ m < (n + 1) * 2 ^ (v - w) := by
      constructor <;> intro h_1
      · -- If `natToBits n w` is a prefix of `natToBits m v`, then `w ≤ v`.
        have h_le : w ≤ v := by
          have := h_1.length_le
          unfold natToBits at this
          simp_all only [List.length_ofFn]
        -- If `natToBits n w` is a prefix of `natToBits m v`, then `m >> (v - w) = n`.
        have h_shift : m / 2 ^ (v - w) = n := by
          have h_shift : ∀ k < w, m.testBit (v - 1 - k) = n.testBit (w - 1 - k) := by
            rw [natToBits, natToBits] at h_1
            obtain ⟨ k, hk ⟩ := h_1
            intro i hi
            replace hk := congr_arg (fun l => l[i]!) hk
            have hiv : i < v := lt_of_lt_of_le hi h_le
            have hnmi : m.testBit (v - 1 - i) = n.testBit (w - 1 - i) := by
                -- 1. Accessing index 'i' in 'L1 ++ k' falls into 'L1' because i < length L1
                simp_all only [List.getElem!_eq_getElem?_getD]
                rw [List.getElem?_append_left] at hk
                · -- 2. Accessing index 'i' in 'List.ofFn f' is just 'f i'
                  rw [List.getElem?_ofFn] at hk
                  simp_all only [↓reduceDIte, Option.getD_some, List.length_ofFn, getElem?_pos, List.getElem_ofFn]
                · -- Proof that i < length L1 (for step 1)
                  simp [hi]
            exact hnmi
          refine' Nat.eq_of_testBit_eq _
          intro i
          specialize h_shift (w - 1 - i)
          rcases lt_trichotomy i (w - 1) with hi | rfl | hi
          · simp_all only [Nat.testBit]
            convert h_shift (by omega) using 2 <;> norm_num [Nat.shiftRight_eq_div_pow]
            · rw [Nat.div_div_eq_div_mul]
              rw [← pow_add, show v - w + i = v - 1 - (w - 1 - i) by omega]
            · rw [Nat.sub_sub_self (by omega)]
          · simp_all only [Nat.testBit]
            rcases w with (_ | w)
            · simp_all only [pow_zero, Nat.lt_one_iff, tsub_zero, Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two, Nat.mod_two_bne_zero]
              rw [Nat.div_eq_of_lt hm, Nat.zero_mod]
            · simp_all only [tsub_self, tsub_zero, Nat.shiftRight_eq_div_pow]
              convert h_shift using 1
              rw [show v - 1 = v - (w + 1) + w by omega, Nat.pow_add]
              norm_num [Nat.div_div_eq_div_mul]
          · simp_all only [Nat.testBit]
            rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
            rw [Nat.div_eq_of_lt, Nat.div_eq_of_lt]
            · exact hn.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
            · rw [Nat.div_lt_iff_lt_mul <| by positivity]
              rw [← pow_add]
              exact hm.trans_le (pow_le_pow_right₀ (by decide) (by omega))
        exact ⟨ h_le, by nlinarith [Nat.div_mul_le_self m (2 ^ (v - w)), pow_pos (zero_lt_two' ℕ) (v - w)], by nlinarith [Nat.div_add_mod m (2 ^ (v - w)), Nat.mod_lt m (pow_pos (zero_lt_two' ℕ) (v - w)), pow_pos (zero_lt_two' ℕ) (v - w)] ⟩
      · -- Since $m$ lies in the dyadic interval corresponding to $n$, the binary representation of $m$ starts with the binary representation of $n$.
        have h_binary : ∀ i : Fin w, (m.testBit (v - 1 - i)) = (n.testBit (w - 1 - i)) := by
          intro i
          have h_div : m / 2 ^ (v - w) = n := by
            exact Nat.le_antisymm (Nat.le_of_lt_succ <| Nat.div_lt_of_lt_mul <| by linarith) (Nat.le_div_iff_mul_le (by positivity) |>.2 <| by linarith)
          -- 1. Replace n with the division form given in h_div
          rw [← h_div]

          -- 2. Use the lemma that relates bit-testing on division to bit-testing on the original number
          -- Lemma: (m / 2^k).testBit i = m.testBit (i + k)
          rw [Nat.testBit_div_two_pow]

          -- 3. Now the goal is m.testBit (...) = m.testBit (...).
          -- We just need to prove the indices are equal.
          congr 1

          -- 4. Prove the arithmetic equality: (v - 1 - i) = (w - 1 - i) + (v - w)
          -- We need to unpack the fact that i < w and w ≤ v to ensure subtraction behaves nicely.
          have hi : ↑i < w := i.isLt
          have hwv : w ≤ v := h_1.1
          omega
        unfold natToBits
        refine' ⟨ List.ofFn fun i : Fin (v - w) => m.testBit (v - 1 - (w + i)), _ ⟩
        refine' List.ext_get _ _
        · simp_all only [List.length_append, List.length_ofFn, add_tsub_cancel_of_le]
        · simp_all only [List.get_eq_getElem, List.getElem_append, List.getElem_ofFn]
          intro i hi
          split_ifs
          · simp_all only [List.length_append, List.length_ofFn, add_tsub_cancel_of_le, forall_const]
            exact Eq.symm (h_binary ⟨ i, by linarith ⟩)
          · simp_all only [List.length_append, List.length_ofFn, add_tsub_cancel_of_le, not_lt, imp_self]

end Digits
