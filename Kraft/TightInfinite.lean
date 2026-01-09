/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: d90cdb53-c612-45f9-9657-d4ef79f12a98

The following was proved by Aristotle:

- theorem kraft_inequality_tight_infinite {I : Type _} (l : I → ℕ)
    (h_summable : Summable (fun i ↦ (1 / 2 : ℝ) ^ l i))
    (h_sum : ∑' i, (1 / 2 : ℝ) ^ l i ≤ 1) :
    ∃ w : I → List Bool,
      Function.Injective w ∧
      PrefixFree (Set.range w) ∧
      ∀ i, (w i).length = l i

At Harmonic, we use a modified version of the `generalize_proofs` tactic.
For compatibility, we include this tactic at the start of the file.
If you add the comment "-- Harmonic `generalize_proofs` tactic" to your file, we will not do this.
-/

import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Kraft.Basic
import Kraft.InequalityFinite


import Batteries.Tactic.GeneralizeProofs

namespace Harmonic.GeneralizeProofs
-- Harmonic `generalize_proofs` tactic

open Lean Meta Elab Parser.Tactic Elab.Tactic Batteries.Tactic.GeneralizeProofs
def mkLambdaFVarsUsedOnly' (fvars : Array Expr) (e : Expr) : MetaM (Array Expr × Expr) := do
  let mut e := e
  let mut fvars' : List Expr := []
  for i' in [0:fvars.size] do
    let fvar := fvars[fvars.size - i' - 1]!
    e ← mkLambdaFVars #[fvar] e (usedOnly := false) (usedLetOnly := false)
    match e with
    | .letE _ _ v b _ => e := b.instantiate1 v
    | .lam _ _ _b _ => fvars' := fvar :: fvars'
    | _ => unreachable!
  return (fvars'.toArray, e)

partial def abstractProofs' (e : Expr) (ty? : Option Expr) : MAbs Expr := do
  if (← read).depth ≤ (← read).config.maxDepth then MAbs.withRecurse <| visit (← instantiateMVars e) ty?
  else return e
where
  visit (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    if (← read).config.debug then
      if let some ty := ty? then
        unless ← isDefEq (← inferType e) ty do
          throwError "visit: type of{indentD e}\nis not{indentD ty}"
    if e.isAtomic then
      return e
    else
      checkCache (e, ty?) fun _ ↦ do
        if ← isProof e then
          visitProof e ty?
        else
          match e with
          | .forallE n t b i =>
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              mkForallFVars #[x] (← visit (b.instantiate1 x) none) (usedOnly := false) (usedLetOnly := false)
          | .lam n t b i => do
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              let ty'? ←
                if let some ty := ty? then
                  let .forallE _ _ tyB _ ← pure ty
                    | throwError "Expecting forall in abstractProofs .lam"
                  pure <| some <| tyB.instantiate1 x
                else
                  pure none
              mkLambdaFVars #[x] (← visit (b.instantiate1 x) ty'?) (usedOnly := false) (usedLetOnly := false)
          | .letE n t v b _ =>
            let t' ← visit t none
            withLetDecl n t' (← visit v t') fun x ↦ MAbs.withLocal x do
              mkLetFVars #[x] (← visit (b.instantiate1 x) ty?) (usedLetOnly := false)
          | .app .. =>
            e.withApp fun f args ↦ do
              let f' ← visit f none
              let argTys ← appArgExpectedTypes f' args ty?
              let mut args' := #[]
              for arg in args, argTy in argTys do
                args' := args'.push <| ← visit arg argTy
              return mkAppN f' args'
          | .mdata _ b  => return e.updateMData! (← visit b ty?)
          | .proj _ _ b => return e.updateProj! (← visit b none)
          | _           => unreachable!
  visitProof (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    let eOrig := e
    let fvars := (← read).fvars
    let e := e.withApp' fun f args => f.beta args
    if e.withApp' fun f args => f.isAtomic && args.all fvars.contains then return e
    let e ←
      if let some ty := ty? then
        if (← read).config.debug then
          unless ← isDefEq ty (← inferType e) do
            throwError m!"visitProof: incorrectly propagated type{indentD ty}\nfor{indentD e}"
        mkExpectedTypeHint e ty
      else pure e
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← getLCtx) e do
        throwError m!"visitProof: proof{indentD e}\nis not well-formed in the current context\n\
          fvars: {fvars}"
    let (fvars', pf) ← mkLambdaFVarsUsedOnly' fvars e
    if !(← read).config.abstract && !fvars'.isEmpty then
      return eOrig
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← read).initLCtx pf do
        throwError m!"visitProof: proof{indentD pf}\nis not well-formed in the initial context\n\
          fvars: {fvars}\n{(← mkFreshExprMVar none).mvarId!}"
    let pfTy ← instantiateMVars (← inferType pf)
    let pfTy ← abstractProofs' pfTy none
    if let some pf' ← MAbs.findProof? pfTy then
      return mkAppN pf' fvars'
    MAbs.insertProof pfTy pf
    return mkAppN pf fvars'
partial def withGeneralizedProofs' {α : Type} [Inhabited α] (e : Expr) (ty? : Option Expr)
    (k : Array Expr → Array Expr → Expr → MGen α) :
    MGen α := do
  let propToFVar := (← get).propToFVar
  let (e, generalizations) ← MGen.runMAbs <| abstractProofs' e ty?
  let rec
    go [Inhabited α] (i : Nat) (fvars pfs : Array Expr)
        (proofToFVar propToFVar : ExprMap Expr) : MGen α := do
      if h : i < generalizations.size then
        let (ty, pf) := generalizations[i]
        let ty := (← instantiateMVars (ty.replace proofToFVar.get?)).cleanupAnnotations
        withLocalDeclD (← mkFreshUserName `pf) ty fun fvar => do
          go (i + 1) (fvars := fvars.push fvar) (pfs := pfs.push pf)
            (proofToFVar := proofToFVar.insert pf fvar)
            (propToFVar := propToFVar.insert ty fvar)
      else
        withNewLocalInstances fvars 0 do
          let e' := e.replace proofToFVar.get?
          modify fun s => { s with propToFVar }
          k fvars pfs e'
  go 0 #[] #[] (proofToFVar := {}) (propToFVar := propToFVar)

partial def generalizeProofsCore'
    (g : MVarId) (fvars rfvars : Array FVarId) (target : Bool) :
    MGen (Array Expr × MVarId) := go g 0 #[]
where
  go (g : MVarId) (i : Nat) (hs : Array Expr) : MGen (Array Expr × MVarId) := g.withContext do
    let tag ← g.getTag
    if h : i < rfvars.size then
      let fvar := rfvars[i]
      if fvars.contains fvar then
        let tgt ← instantiateMVars <| ← g.getType
        let ty := (if tgt.isLet then tgt.letType! else tgt.bindingDomain!).cleanupAnnotations
        if ← pure tgt.isLet <&&> Meta.isProp ty then
          let tgt' := Expr.forallE tgt.letName! ty tgt.letBody! .default
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .app g' tgt.letValue!
          return ← go g'.mvarId! i hs
        if let some pf := (← get).propToFVar.get? ty then
          let tgt' := tgt.bindingBody!.instantiate1 pf
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .lam tgt.bindingName! tgt.bindingDomain! g' tgt.bindingInfo!
          return ← go g'.mvarId! (i + 1) hs
        match tgt with
        | .forallE n t b bi =>
          let prop ← Meta.isProp t
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            let t' := t'.cleanupAnnotations
            let tgt' := Expr.forallE n t' b bi
            let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
            g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
            let (fvar', g') ← g'.mvarId!.intro1P
            g'.withContext do Elab.pushInfoLeaf <|
              .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
            if prop then
              MGen.insertFVar t' (.fvar fvar')
            go g' (i + 1) (hs ++ hs')
        | .letE n t v b _ =>
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            withGeneralizedProofs' v t' fun hs'' pfs'' v' => do
              let tgt' := Expr.letE n t' v' b false
              let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
              g.assign <| mkAppN (← mkLambdaFVars (hs' ++ hs'') g' (usedOnly := false) (usedLetOnly := false)) (pfs' ++ pfs'')
              let (fvar', g') ← g'.mvarId!.intro1P
              g'.withContext do Elab.pushInfoLeaf <|
                .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
              go g' (i + 1) (hs ++ hs' ++ hs'')
        | _ => unreachable!
      else
        let (fvar', g') ← g.intro1P
        g'.withContext do Elab.pushInfoLeaf <|
          .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
        go g' (i + 1) hs
    else if target then
      withGeneralizedProofs' (← g.getType) none fun hs' pfs' ty' => do
        let g' ← mkFreshExprSyntheticOpaqueMVar ty' tag
        g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
        return (hs ++ hs', g'.mvarId!)
    else
      return (hs, g)

end GeneralizeProofs

open Lean Elab Parser.Tactic Elab.Tactic Batteries.Tactic.GeneralizeProofs
partial def generalizeProofs'
    (g : MVarId) (fvars : Array FVarId) (target : Bool) (config : Config := {}) :
    MetaM (Array Expr × MVarId) := do
  let (rfvars, g) ← g.revert fvars (clearAuxDeclsInsteadOfRevert := true)
  g.withContext do
    let s := { propToFVar := ← initialPropToFVar }
    GeneralizeProofs.generalizeProofsCore' g fvars rfvars target |>.run config |>.run' s

elab (name := generalizeProofsElab'') "generalize_proofs" config?:(Parser.Tactic.config)?
    hs:(ppSpace colGt binderIdent)* loc?:(location)? : tactic => withMainContext do
  let config ← elabConfig (mkOptionalNode config?)
  let (fvars, target) ←
    match expandOptLocation (Lean.mkOptionalNode loc?) with
    | .wildcard => pure ((← getLCtx).getFVarIds, true)
    | .targets t target => pure (← getFVarIds t, target)
  liftMetaTactic1 fun g => do
    let (pfs, g) ← generalizeProofs' g fvars target config
    g.withContext do
      let mut lctx ← getLCtx
      for h in hs, fvar in pfs do
        if let `(binderIdent| $s:ident) := h then
          lctx := lctx.setUserName fvar.fvarId! s.getId
        Expr.addLocalVarInfoForBinderIdent fvar h
      Meta.withLCtx lctx (← Meta.getLocalInstances) do
        let g' ← Meta.mkFreshExprSyntheticOpaqueMVar (← g.getType) (← g.getTag)
        g.assign g'
        return g'.mvarId!

end Harmonic

namespace Kraft

open scoped BigOperators Real

noncomputable section AristotleLemmas

/-
Converts a natural number `n` to a list of bits of length `width` (big-endian).
-/
def natToBits (n width : ℕ) : List Bool :=
  List.ofFn (fun i : Fin width => n.testBit (width - 1 - i))

/-
`natToBits` is injective for numbers fitting in the width.
-/
lemma natToBits_inj {n m width : ℕ} (hn : n < 2 ^ width) (hm : m < 2 ^ width)
    (h : natToBits n width = natToBits m width) : n = m := by
      refine' Nat.eq_of_testBit_eq fun i => _
      by_cases hi : i < width <;> simp_all [Nat.testBit]
      · replace h := congr_arg ( fun l => l[width - 1 - i ]! ) h
        simp_all [Nat.shiftRight_eq_div_pow]
        unfold Kraft.natToBits at h; simp_all +decide [ Nat.testBit, Nat.shiftRight_eq_div_pow ]

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

        -- extract the Bool equality from `h`
        have hbool :
            (n / 2 ^ i % 2 == 1) = (m / 2 ^ i % 2 == 1) := by
          simpa [hcond, hsub] using h

        -- bridge between `==` and `=` (simp knows this for Nat)
        have hn_iff : ((n / 2 ^ i % 2 == 1) = true) ↔ (n / 2 ^ i % 2 = 1) := by simp
        have hm_iff : ((m / 2 ^ i % 2 == 1) = true) ↔ (m / 2 ^ i % 2 = 1) := by simp

        constructor
        · intro hn1
          have hntrue : (n / 2 ^ i % 2 == 1) = true := (hn_iff).2 hn1
          have hmtrue : (m / 2 ^ i % 2 == 1) = true := by simpa [hbool] using hntrue
          exact (hm_iff).1 hmtrue
        · intro hm1
          have hmtrue : (m / 2 ^ i % 2 == 1) = true := (hm_iff).2 hm1
          have hntrue : (n / 2 ^ i % 2 == 1) = true := by simpa [hbool] using hmtrue
          exact (hn_iff).1 hntrue

      · rw [ Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow ]
        rw [ Nat.div_eq_of_lt ( lt_of_lt_of_le hn ( Nat.pow_le_pow_right ( by decide ) hi ) ), Nat.div_eq_of_lt ( lt_of_lt_of_le hm ( Nat.pow_le_pow_right ( by decide ) hi ) ) ]

/-
`natToBits n w` is a prefix of `natToBits m v` iff `w ≤ v` and `m` lies in the dyadic interval corresponding to `n`.
-/
lemma natToBits_prefix_iff {n m w v : ℕ} (hn : n < 2 ^ w) (hm : m < 2 ^ v) :
    natToBits n w <+: natToBits m v ↔ w ≤ v ∧ n * 2 ^ (v - w) ≤ m ∧ m < (n + 1) * 2 ^ (v - w) := by
      constructor <;> intro h_1
      · -- If `natToBits n w` is a prefix of `natToBits m v`, then `w ≤ v`.
        have h_le : w ≤ v := by
          have := h_1.length_le
          unfold Kraft.natToBits at this; aesop
        -- If `natToBits n w` is a prefix of `natToBits m v`, then `m >> (v - w) = n`.
        have h_shift : m / 2 ^ (v - w) = n := by
          have h_shift : ∀ k < w, m.testBit (v - 1 - k) = n.testBit (w - 1 - k) := by
            rw [ Kraft.natToBits, Kraft.natToBits ] at h_1
            obtain ⟨ k, hk ⟩ := h_1
            intro i hi; replace hk := congr_arg ( fun l => l[i]! ) hk
            simp_all
            grind
          refine' Nat.eq_of_testBit_eq _
          intro i; specialize h_shift ( w - 1 - i ) ; rcases lt_trichotomy i ( w - 1 ) with hi | rfl | hi <;> simp_all +decide [ Nat.testBit ]
          · convert h_shift ( by omega ) using 2 <;> norm_num [ Nat.shiftRight_eq_div_pow ]
            · rw [ Nat.div_div_eq_div_mul ]
              rw [ ← pow_add, show v - w + i = v - 1 - ( w - 1 - i ) by omega ]
            · rw [ Nat.sub_sub_self ( by omega ) ]
          · rcases w with ( _ | w ) <;> simp_all +decide [ Nat.shiftRight_eq_div_pow ]
            · rw [ Nat.div_eq_of_lt hm, Nat.zero_mod ]
            · convert h_shift using 1
              rw [ show v - 1 = v - ( w + 1 ) + w by omega, pow_add ] ; norm_num [ Nat.div_div_eq_div_mul ]
          · rw [ Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow ]
            rw [ Nat.div_eq_of_lt, Nat.div_eq_of_lt ]
            · exact hn.trans_le ( Nat.pow_le_pow_right ( by decide ) ( by omega ) )
            · rw [ Nat.div_lt_iff_lt_mul <| by positivity ]
              rw [ ← pow_add ]
              exact hm.trans_le ( pow_le_pow_right₀ ( by decide ) ( by omega ) )
        exact ⟨ h_le, by nlinarith [ Nat.div_mul_le_self m ( 2 ^ ( v - w ) ), pow_pos ( zero_lt_two' ℕ ) ( v - w ) ], by nlinarith [ Nat.div_add_mod m ( 2 ^ ( v - w ) ), Nat.mod_lt m ( pow_pos ( zero_lt_two' ℕ ) ( v - w ) ), pow_pos ( zero_lt_two' ℕ ) ( v - w ) ] ⟩
      · -- Since $m$ lies in the dyadic interval corresponding to $n$, the binary representation of $m$ starts with the binary representation of $n$.
        have h_binary : ∀ i : Fin w, (m.testBit (v - 1 - i)) = (n.testBit (w - 1 - i)) := by
          intro i
          have h_div : m / 2 ^ (v - w) = n := by
            exact Nat.le_antisymm ( Nat.le_of_lt_succ <| Nat.div_lt_of_lt_mul <| by linarith ) ( Nat.le_div_iff_mul_le ( by positivity ) |>.2 <| by linarith )
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
        unfold Kraft.natToBits
        refine' ⟨ List.ofFn fun i : Fin ( v - w ) => m.testBit ( v - 1 - ( w + i ) ), _ ⟩
        refine' List.ext_get _ _ <;> simp_all +decide [ List.getElem_append ]
        intro i hi; split_ifs <;> simp_all +decide [ Nat.sub_sub, add_comm ]
        exact Eq.symm ( h_binary ⟨ i, by linarith ⟩ )

/-
Recursive definition of the integer values corresponding to the cumulative sums.
-/
def kraft_A (l : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => (kraft_A l n + 1) * 2 ^ (l (n + 1) - l n)

/-
If `l` is monotone, then `kraft_A l n / 2^(l n)` equals the partial sum.
-/
lemma kraft_A_div_pow_eq_sum (l : ℕ → ℕ) (h_mono : Monotone l) (n : ℕ) :
    (kraft_A l n : ℝ) / 2 ^ l n = ∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ l k := by
      induction n <;> simp_all +decide [Finset.sum_range_succ]
      -- Substitute the definition of `kraft_A` into the left-hand side.
      have h_sub : (Kraft.kraft_A l (Nat.succ ‹_›) : ℝ) = (Kraft.kraft_A l ‹_› + 1) * 2 ^ (l (Nat.succ ‹_›) - l ‹_›) := by
        norm_cast
      rw [ ← ‹ ( Kraft.kraft_A l _ : ℝ ) / 2 ^ l _ = ∑ x ∈ Finset.range _, ( 2 ^ l x ) ⁻¹ ›, h_sub ]
      rw [ show l ( _ + 1 ) = l _ + ( l ( _ + 1 ) - l _ ) by rw [ Nat.add_sub_of_le ( h_mono ( Nat.le_succ _ ) ) ] ]
      ring_nf
      -- Combine like terms and simplify the expression.
      field_simp
      ring_nf
      norm_num [ ← mul_pow ]

theorem kraft_inequality_tight_nat_mono (l : ℕ → ℕ) (h_mono : Monotone l)
    (h_summable : Summable (fun i => (1 / 2 : ℝ) ^ l i))
    (h_sum : ∑' i, (1 / 2 : ℝ) ^ l i ≤ 1) :
    ∃ w : ℕ → List Bool,
      Function.Injective w ∧
      Kraft.PrefixFree (Set.range w) ∧
      ∀ i, (w i).length = l i := by
        -- By definition of $kraft_A$, we know that $kraft_A n < 2^{l n}$ for all $n$.
        have h_kraft_A_lt : ∀ n, kraft_A l n < 2 ^ l n := by
          have h_kraft_A_lt : ∀ n, (kraft_A l n : ℝ) / 2 ^ l n < 1 := by
            intro n
            have h_sum_lt : (kraft_A l n : ℝ) / 2 ^ l n = ∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ l k := by
              exact kraft_A_div_pow_eq_sum l h_mono n
            exact h_sum_lt.symm ▸ lt_of_lt_of_le ( by exact ( show ( ∑ k ∈ Finset.range n, ( 1 / 2 : ℝ ) ^ l k ) < ∑' k : ℕ, ( 1 / 2 : ℝ ) ^ l k from by simpa using ( show ( ∑ k ∈ Finset.range n, ( 1 / 2 : ℝ ) ^ l k ) < ∑' k : ℕ, ( 1 / 2 : ℝ ) ^ l k from by exact lt_of_lt_of_le ( by simpa using ( show ( ∑ k ∈ Finset.range n, ( 1 / 2 : ℝ ) ^ l k ) < ∑ k ∈ Finset.range ( n + 1 ), ( 1 / 2 : ℝ ) ^ l k from by simp [ Finset.sum_range_succ ] ) ) ( Summable.sum_le_tsum ( Finset.range ( n + 1 ) ) ( fun _ _ => by positivity ) h_summable ) ) ) ) h_sum
          exact fun n => by have := h_kraft_A_lt n; rw [ div_lt_one ( by positivity ) ] at this; exact_mod_cast this
        refine' ⟨ fun n => natToBits ( kraft_A l n ) ( l n ), _, _, _ ⟩
        · intro n m hnm
          -- Since $kraft_A n < 2^{l n}$ and $kraft_A m < 2^{l m}$, and $natToBits$ is injective, we have $kraft_A n = kraft_A m$.
          have h_kraft_A_eq : kraft_A l n = kraft_A l m := by
            apply natToBits_inj
            exact h_kraft_A_lt n
            · unfold Kraft.natToBits at hnm
              replace hnm := congr_arg List.length hnm ; aesop
            · have := congr_arg List.length hnm; norm_num [ Kraft.natToBits ] at this; aesop
          -- Since $kraft_A$ is strictly increasing, we have $n = m$.
          have h_kraft_A_inj : StrictMono (kraft_A l) := by
            refine' strictMono_nat_of_lt_succ _
            intro n
            exact lt_of_lt_of_le ( by norm_num ) ( Nat.mul_le_mul_left _ ( Nat.one_le_pow _ _ ( by norm_num ) ) )
          exact h_kraft_A_inj.injective h_kraft_A_eq
        · rintro _ ⟨ n, rfl ⟩ _ ⟨ m, rfl ⟩ hnm
          by_cases hnm' : n = m <;> simp_all +decide [ natToBits_prefix_iff ]
          -- Since $l n \le l m$, we have $S_n \le S_m < S_n + 2^{-l n}$.
          have h_sum_bounds : (∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ l k) ≤ (∑ k ∈ Finset.range m, (1 / 2 : ℝ) ^ l k) ∧ (∑ k ∈ Finset.range m, (1 / 2 : ℝ) ^ l k) < (∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ l k) + (1 / 2 : ℝ) ^ l n := by
            have h_sum_bounds : (kraft_A l n : ℝ) / 2 ^ l n ≤ (kraft_A l m : ℝ) / 2 ^ l m ∧ (kraft_A l m : ℝ) / 2 ^ l m < (kraft_A l n : ℝ) / 2 ^ l n + (1 / 2 : ℝ) ^ l n := by
              field_simp
              norm_num [ mul_assoc, ← mul_pow ]
              norm_cast
              rw [ show 2 ^ l m = 2 ^ l n * 2 ^ ( l m - l n ) by rw [ ← pow_add, Nat.add_sub_of_le hnm.1 ] ] ; constructor <;> nlinarith [ pow_pos ( zero_lt_two' ℕ ) ( l n ), pow_pos ( zero_lt_two' ℕ ) ( l m - l n ) ]
            convert h_sum_bounds using 2 <;> norm_num [ kraft_A_div_pow_eq_sum ]
            · rw [ kraft_A_div_pow_eq_sum ]
              assumption
            · rw [ kraft_A_div_pow_eq_sum ]
              assumption
            · rw [ kraft_A_div_pow_eq_sum ]
              assumption
            · rw [ kraft_A_div_pow_eq_sum ]
              assumption
          cases lt_or_gt_of_ne hnm' <;> simp_all
          · -- Since $n < m$, we have $\sum_{k=n}^{m-1} 2^{-l k} \geq 2^{-l n}$.
            have h_sum_ge : ∑ k ∈ Finset.Ico n m, (1 / 2 : ℝ) ^ l k ≥ (1 / 2 : ℝ) ^ l n := by
              exact le_trans ( by norm_num ) ( Finset.single_le_sum ( fun x _ => by positivity ) ( Finset.left_mem_Ico.mpr ‹_› ) )
            simp_all +decide [ Finset.sum_Ico_eq_sub _ ( by linarith : n ≤ m ) ]
            linarith
          · -- Since $m < n$, we have $\sum_{k=m}^{n-1} 2^{-l k} \geq 2^{-l n}$.
            have h_sum_ge : ∑ k ∈ Finset.Ico m n, (1 / 2 : ℝ) ^ l k ≥ (1 / 2 : ℝ) ^ l n := by
              exact le_trans ( by norm_num ) ( Finset.single_le_sum ( fun x _ => by positivity ) ( Finset.mem_Ico.mpr ⟨ le_rfl, by linarith ⟩ ) ) |> le_trans <| Finset.sum_le_sum fun x hx => pow_le_pow_of_le_one ( by norm_num ) ( by norm_num ) <| h_mono <| Finset.mem_Ico.mp hx |>.2.le
            simp_all +decide [ Finset.sum_Ico_eq_sub _ ( by linarith : m ≤ n ) ]
            linarith
        · unfold Kraft.natToBits; aesop

/-
`KraftOrder` is a strict total order.
-/
def KraftOrder {I : Type _} (l : I → ℕ) (e : I ↪ ℕ) (i j : I) : Prop :=
  l i < l j ∨ (l i = l j ∧ e i < e j)

lemma KraftOrder_isStrictTotalOrder {I : Type _} (l : I → ℕ) (e : I ↪ ℕ) :
    IsStrictTotalOrder I (KraftOrder l e) := by
      have h_irrefl : Irreflexive (Kraft.KraftOrder l e) := by
        intro i hi; cases hi <;> aesop
      refine' { .. }
      · intro a b
        rcases lt_trichotomy ( l a ) ( l b ) with h | h | h <;> rcases lt_trichotomy ( e a ) ( e b ) with h' | h' | h'
        all_goals unfold Kraft.KraftOrder; aesop
      · exact h_irrefl
      · rintro a b c ( h | h ) ( h' | h' )
        · exact Or.inl ( lt_trans h h' )
        · exact Or.inl ( by linarith )
        · exact Or.inl ( by linarith )
        · exact Or.inr ⟨ by linarith, by linarith ⟩

/-
Initial segments of `KraftOrder` are finite if fibers of `l` are finite.
-/
lemma KraftOrder_finite_initial_segment {I : Type _} (l : I → ℕ) (e : I ↪ ℕ)
    (h_finite : ∀ k, {i | l i = k}.Finite) (i : I) :
    {j | KraftOrder l e j i}.Finite := by
      -- The set {j | l j < l i} is a subset of the union of {j | l j = k} for k < l i, which is finite by h_finite.
      have h1 : {j | l j < l i} ⊆ ⋃ k < l i, {j | l j = k} := by
        -- Take any $j$ such that $l j < l i$. Then $l j$ is some natural number less than $l i$, so $j$ is in the set $\{j | l j = l j\}$.
        intro j hj
        aesop
      -- The set {j | l j = l i ∧ e j < e i} is a subset of {j | l j = l i}, which is finite by h_finite.
      have h2 : {j | l j = l i ∧ e j < e i} ⊆ {j | l j = l i} := by
        aesop
      exact Set.Finite.subset ( Set.Finite.union ( Set.Finite.biUnion ( Set.finite_lt_nat ( l i ) ) fun k hk => h_finite k ) ( h_finite _ ) ) ( by rintro j; unfold Kraft.KraftOrder; aesop )

/-
The rank of an element `i` is the number of elements strictly smaller than `i` in `KraftOrder`.
-/
noncomputable def kraftRank {I : Type _} (l : I → ℕ) (e : I ↪ ℕ)
    (h_finite : ∀ k, {i | l i = k}.Finite) (i : I) : ℕ :=
  (KraftOrder_finite_initial_segment l e h_finite i).toFinset.card

/-
`kraftRank` is strictly monotone with respect to `KraftOrder`.
-/
lemma kraftRank_lt_of_KraftOrder {I : Type _} (l : I → ℕ) (e : I ↪ ℕ)
    (h_finite : ∀ k, {i | l i = k}.Finite) {i j : I} (h : KraftOrder l e i j) :
    kraftRank l e h_finite i < kraftRank l e h_finite j := by
      apply_rules [ Finset.card_lt_card ]
      unfold Kraft.KraftOrder at *
      simp_all +decide [ Finset.ssubset_def, Finset.subset_iff ]
      grind

/-
`kraftRank` is surjective.
-/
lemma kraftRank_surjective {I : Type _} [Infinite I] (l : I → ℕ) (e : I ↪ ℕ)
    (h_finite : ∀ k, {i | l i = k}.Finite) :
    Function.Surjective (kraftRank l e h_finite) := by
      -- First, we show the range is an initial segment.
      have h_initial_segment : ∀ n, (∃ i, kraftRank l e h_finite i = n) → ∀ m < n, ∃ i, kraftRank l e h_finite i = m := by
        intro n hn m hm
        obtain ⟨i, hi⟩ := hn
        have h_card : Finset.card (Finset.image (kraftRank l e h_finite) (Set.Finite.toFinset (KraftOrder_finite_initial_segment l e h_finite i))) = n := by
          rw [ Finset.card_image_of_injOn, ← hi, kraftRank ]
          intro x hx y hy hxy
          have h_eq : ∀ x y, x ≠ y → KraftOrder l e x y ∨ KraftOrder l e y x := by
            intros x y hxy
            have h_total : ∀ x y : I, x ≠ y → l x < l y ∨ l y < l x ∨ (l x = l y ∧ e x < e y) ∨ (l y = l x ∧ e y < e x) := by
              intro x y hxy; cases lt_trichotomy ( l x ) ( l y ) <;> cases lt_trichotomy ( e x ) ( e y ) <;> aesop
            specialize h_total x y hxy; unfold Kraft.KraftOrder; aesop
          exact Classical.not_not.1 fun h => by cases h_eq x y h <;> linarith [ kraftRank_lt_of_KraftOrder l e h_finite ‹_› ]
        have h_image : Finset.image (kraftRank l e h_finite) (Set.Finite.toFinset (KraftOrder_finite_initial_segment l e h_finite i)) = Finset.range n := by
          refine' Finset.eq_of_subset_of_card_le ( Finset.image_subset_iff.2 fun x hx => Finset.mem_range.2 <| _ ) _
          · exact hi ▸ kraftRank_lt_of_KraftOrder l e h_finite ( by aesop )
          · aesop
        replace h_image := Finset.ext_iff.mp h_image m; aesop
      -- Since `I` is infinite and `kraftRank` is injective, the range is infinite.
      have h_range_infinite : Set.Infinite (Set.range (Kraft.kraftRank l e h_finite)) := by
        refine Set.infinite_range_of_injective ?_
        -- By definition of `kraftRank`, if `kraftRank i = kraftRank j`, then `i` and `j` must be comparable under `KraftOrder`.
        have h_comparable : ∀ i j, kraftRank l e h_finite i = kraftRank l e h_finite j → i = j := by
          intro i j hij
          have h_comparable : i = j ∨ KraftOrder l e i j ∨ KraftOrder l e j i := by
            have := @KraftOrder_isStrictTotalOrder I l e
            cases this.trichotomous i j <;> tauto
          rcases h_comparable with ( rfl | h | h ) <;> simp_all
          · exact absurd hij ( ne_of_lt ( kraftRank_lt_of_KraftOrder l e h_finite h ) )
          · exact absurd hij ( ne_of_gt ( kraftRank_lt_of_KraftOrder _ _ _ h ) )
        exact fun i j hij => h_comparable i j hij
      rw [ Set.infinite_iff_exists_gt ] at h_range_infinite
      intro n; specialize h_range_infinite n; aesop

/-
`kraftRank` is injective.
-/
lemma kraftRank_injective {I : Type _} (l : I → ℕ) (e : I ↪ ℕ)
    (h_finite : ∀ k, {i | l i = k}.Finite) :
    Function.Injective (kraftRank l e h_finite) := by
      -- Assume `i ≠ j`. By trichotomy of `KraftOrder`, either `KraftOrder i j` or `KraftOrder j i`.
      intro i j hij
      by_contra h_neq
      have h_trichotomy : Kraft.KraftOrder l e i j ∨ Kraft.KraftOrder l e j i := by
        have h_trichotomy : IsTrichotomous I (Kraft.KraftOrder l e) := by
          have := @Kraft.KraftOrder_isStrictTotalOrder I l e
          exact this.toIsTrichotomous
        cases h_trichotomy.trichotomous i j <;> tauto
      rcases h_trichotomy with ( H | H ) <;> [ exact hij.not_lt ( kraftRank_lt_of_KraftOrder _ _ _ H ) ; exact hij.not_gt ( kraftRank_lt_of_KraftOrder _ _ _ H ) ]

/-
If `l` is summable, we can reorder `I` to make `l` monotone.
-/
lemma exists_equiv_nat_monotone_of_infinite {I : Type _} [Infinite I] (l : I → ℕ)
    (h_summable : Summable (fun i => (1 / 2 : ℝ) ^ l i)) :
    ∃ e : ℕ ≃ I, Monotone (l ∘ e) := by
      obtain ⟨e, he⟩ : ∃ e : ℕ ≃ I, ∀ n m, n ≤ m → l (e n) ≤ l (e m) := by
        have h_countable : Countable I := by
          have := h_summable.countable_support
          simp_all [ Function.support ]
          exact Set.countable_univ_iff.mp this
        -- Let `e = Encodable.encode`.
        obtain ⟨e, he⟩ : ∃ e : I ↪ ℕ, True := by
          simp
          exact countable_iff_nonempty_embedding.mp h_countable
        have h_finite : ∀ k, {i : I | l i = k}.Finite := by
          intro k
          refine' Set.Finite.subset ( h_summable.tendsto_cofinite_zero.eventually ( gt_mem_nhds <| show 0 < ( 1 / 2 : ℝ ) ^ k by positivity ) ) _
          exact fun x hx => by aesop
        -- By definition of `kraftRank`, we know that `kraftRank` is a bijection between `I` and `ℕ`.
        have h_bij : Function.Bijective (kraftRank l e h_finite) := by
          exact ⟨ kraftRank_injective l e h_finite, kraftRank_surjective l e h_finite ⟩
        obtain ⟨e_iso, he_iso⟩ : ∃ e_iso : ℕ ≃ I, ∀ n, kraftRank l e h_finite (e_iso n) = n := by
          exact ⟨ Equiv.symm ( Equiv.ofBijective _ h_bij ), fun n => Equiv.apply_symm_apply ( Equiv.ofBijective _ h_bij ) n ⟩
        refine' ⟨ e_iso, fun n m hnm => _ ⟩
        contrapose! hnm
        have := kraftRank_lt_of_KraftOrder l e h_finite ( show KraftOrder l e ( e_iso m ) ( e_iso n ) from Or.inl hnm ) ; aesop
      exact ⟨ e, fun n m hnm => he n m hnm ⟩

/-
Extension of `l` to `ℕ` preserving monotonicity, assuming `k > 0`.
-/
def l_ext {k : ℕ} (l : Fin k → ℕ) (hk : k ≠ 0) (i : ℕ) : ℕ :=
  if h : i < k then l ⟨i, h⟩ else l ⟨k - 1, by omega⟩ + (i - k + 1)

/-
`l_ext` agrees with `l` on `Fin k`.
-/
lemma l_ext_eq {k : ℕ} (l : Fin k → ℕ) (hk : k ≠ 0) (i : Fin k) :
    l_ext l hk i = l i := by
      unfold Kraft.l_ext; aesop

/-
`l_ext` is monotone.
-/
lemma l_ext_monotone {k : ℕ} (l : Fin k → ℕ) (h_mono : Monotone l) (hk : k ≠ 0) :
    Monotone (l_ext l hk) := by
      -- Let's prove the monotonicity of `l_ext` by considering different cases.
      intro i j hij
      simp [Kraft.l_ext] at *
      split_ifs <;> try omega
      · exact h_mono hij
      · exact le_add_of_le_of_nonneg ( h_mono ( Nat.le_pred_of_lt ‹_› ) ) ( Nat.zero_le _ )

lemma kraft_inequality_tight_finite_mono {k : ℕ} (l : Fin k → ℕ) (h_mono : Monotone l)
    (h_sum : ∑ i, (1 / 2 : ℝ) ^ l i ≤ 1) :
    ∃ w : Fin k → List Bool,
      Function.Injective w ∧
      Kraft.PrefixFree (Set.range w) ∧
      ∀ i, (w i).length = l i := by
        -- For `i ≥ k`, `kraft_A L i / 2^{L i} = \sum_{j=0}^{i-1} 2^{-L j} = (\sum_{j=0}^{k-1} 2^{-L j}) + \sum_{j=k}^{i-1} 2^{-L j}`.
        have h_split_sum : ∀ i : Fin k, kraft_A (l_ext l (by
        linarith [ Fin.is_lt i ]) ∘ fun i => i) i < 2 ^ (l i) := by
          all_goals generalize_proofs at *
          intro i
          have h_split_sum :
            kraft_A (l_ext l (by expose_names; exact pf_1 i)
             ∘ fun i => i) i / (2 : ℝ) ^ (l_ext l (by expose_names; exact pf_1 i) i)
              = ∑ j ∈ Finset.range i, (1 / 2 : ℝ) ^ (l_ext l (by expose_names; exact pf_1 i) j) := by
            all_goals generalize_proofs at *
            convert kraft_A_div_pow_eq_sum ( l_ext l ‹_› ∘ fun i => i ) ( l_ext_monotone l h_mono ‹_› ) i using 1
          generalize_proofs at *
          have h_split_sum : ∑ j ∈ Finset.range i, (1 / 2 : ℝ) ^ (l_ext l (by
          assumption) j) < 1 := by
            have h_split_sum : ∑ j ∈ Finset.range k, (1 / 2 : ℝ) ^ (l_ext l (by
            assumption) j) ≤ 1 := by
              rw [ Finset.sum_range ]
              unfold Kraft.l_ext; aesop
            generalize_proofs at *
            refine' lt_of_lt_of_le ( _ ) h_split_sum
            rw [ ← Finset.sum_range_add_sum_Ico _ ( show ( i : ℕ ) ≤ k from i.2.le ) ] ; exact lt_add_of_pos_right _ ( Finset.sum_pos ( fun _ _ => by positivity ) ( by aesop ) )
          generalize_proofs at *
          rw [ div_eq_iff ] at * <;> norm_num at *
          exact_mod_cast ( by nlinarith [ pow_pos ( zero_lt_two' ℝ ) ( l i ), show ( 2 : ℝ ) ^ Kraft.l_ext l ‹_› i = 2 ^ l i from by erw [ Kraft.l_ext_eq ] ] : ( Kraft.kraft_A ( Kraft.l_ext l ‹_› ∘ fun i => i ) i : ℝ ) < 2 ^ l i )
        generalize_proofs at *
        refine' ⟨ _, _, _, _ ⟩
        use fun i => natToBits ( Kraft.kraft_A ( l_ext l ( by tauto ) ∘ fun i => i ) i ) ( l i )
        · intro i j hij
          -- Since `natToBits` is injective, we have `kraft_A L i = kraft_A L j`.
          have h_kraft_A_eq : Kraft.kraft_A (l_ext l (by
          expose_names; exact pf_1 i) ∘ fun i => i) i = Kraft.kraft_A (l_ext l (by
          expose_names; exact pf_1 i) ∘ fun i => i) j := by
            apply natToBits_inj
            exact h_split_sum i
            · replace hij := congr_arg List.length hij ; simp_all +decide [ Kraft.natToBits ]
            · convert hij using 1
              replace hij := congr_arg List.length hij ; simp_all +decide [ Kraft.natToBits ]
          generalize_proofs at *
          -- Since `kraft_A` is strictly monotone, we have `i = j`.
          have h_kraft_A_mono : StrictMono (Kraft.kraft_A (l_ext l (by tauto) ∘ fun i => i)) := by
            refine' strictMono_nat_of_lt_succ _
            intro n
            exact Nat.lt_of_lt_of_le ( Nat.lt_succ_self _ ) ( Nat.le_mul_of_pos_right _ ( pow_pos ( by decide ) _ ) )
          exact Fin.ext <| h_kraft_A_mono.injective h_kraft_A_eq
        · intro x hx y hy hxy
          obtain ⟨ i, rfl ⟩ := hx; obtain ⟨ j, rfl ⟩ := hy; simp_all +decide [ natToBits_prefix_iff ]
          -- If `i < j`, then `S_j \ge S_i + 2^{-l i}`, contradiction.
          by_cases hij : i < j
          · have h_contradiction : (Kraft.kraft_A (l_ext l (by expose_names; exact pf_1 i) ∘ fun i => i) j : ℝ) / 2 ^ (l j) ≥ (Kraft.kraft_A (l_ext l (by
            expose_names; exact pf_1 i) ∘ fun i => i) i : ℝ) / 2 ^ (l i) + (1 / 2 : ℝ) ^ (l i) := by
              all_goals generalize_proofs at *
              have h_contradiction : (Kraft.kraft_A (l_ext l (by
              assumption) ∘ fun i => i) j : ℝ) / 2 ^ (l j) = (∑ k ∈ Finset.range j, (1 / 2 : ℝ) ^ (l_ext l (by
              assumption) k)) ∧ (Kraft.kraft_A (l_ext l (by
              assumption) ∘ fun i => i) i : ℝ) / 2 ^ (l i) = (∑ k ∈ Finset.range i, (1 / 2 : ℝ) ^ (l_ext l (by
              assumption) k)) := by
                apply And.intro
                all_goals generalize_proofs at *
                · convert kraft_A_div_pow_eq_sum ( l_ext l ( by tauto ) ∘ fun i => i ) ( l_ext_monotone l h_mono ( by tauto ) ) j using 1
                  generalize_proofs at *
                  unfold Kraft.l_ext; aesop
                · convert kraft_A_div_pow_eq_sum _ _ _ using 1
                  generalize_proofs at *
                  · unfold Kraft.l_ext; aesop
                  · exact l_ext_monotone l h_mono ( by tauto )
              generalize_proofs at *
              rw [ h_contradiction.1, h_contradiction.2, ← Finset.sum_range_add_sum_Ico _ ( show ( i : ℕ ) ≤ j from Nat.le_of_lt hij ) ]
              set A := ∑ k_1 ∈ Finset.range (↑i), (1 / 2 : ℝ) ^ l_ext l (by assumption) k_1
              set B := ∑ k_1 ∈ Finset.Ico (↑i) (↑j), (1 / 2 : ℝ) ^ l_ext l (by assumption) k_1
              set C := (1 / 2 : ℝ) ^ l i
              have hiIco : (↑i) ∈ Finset.Ico (↑i) (↑j) := by
                exact Finset.left_mem_Ico.2 (show (↑i) < (↑j) from hij)
              have hC_le_B :
                  (1 / 2 : ℝ) ^ l i ≤
                    ∑ k_1 ∈ Finset.Ico (↑i) (↑j), (1 / 2 : ℝ) ^ l_ext l (by assumption) k_1 := by
                -- single term ≤ sum over Ico
                have h :=
                  (Finset.single_le_sum (s := Finset.Ico (↑i) (↑j))
                    (f := fun k_1 => (1 / 2 : ℝ) ^ l_ext l (by assumption) k_1)
                    (by intro _ _; positivity)
                    (by exact Finset.left_mem_Ico.mpr hij))
                -- h : (1/2)^(l_ext ... ↑i) ≤ ∑ ...
                -- rewrite l_ext at ↑i using ↑i < k (since i : Fin k)
                simpa [Kraft.l_ext, (show (↑i) < k from i.is_lt)] using h
              have h_add :
                  A + (1 / 2 : ℝ) ^ l i ≤ A + B :=
                add_le_add_right (α := ℝ) (a := A) hC_le_B
              simp_all
              unfold C
              simp
              assumption

            generalize_proofs at *
            contrapose! h_contradiction
            rw [ div_add', div_lt_div_iff₀ ] <;> norm_cast <;> norm_num
            norm_num [ ← mul_pow ]
            norm_cast
            convert mul_lt_mul_of_pos_right hxy.2.2 ( pow_pos ( zero_lt_two' ℕ ) ( l i ) ) using 1 ; rw [ show l j = l i + ( l j - l i ) by rw [ Nat.add_sub_of_le hxy.1 ] ]
            ring_nf
            norm_num
          · cases lt_or_eq_of_le ( le_of_not_gt hij ) <;> simp_all [Fin.ext_iff]
            · -- Since `j < i`, we have `l j < l i`.
              have h_lt : l j < l i := by
                refine' lt_of_le_of_ne ( h_mono hij ) _
                intro h
                simp_all
                -- Since `l` is monotone, `kraft_A` is strictly increasing.
                have h_kraft_A_mono : StrictMono (Kraft.kraft_A (Kraft.l_ext l (by expose_names; exact pf_1 i) ∘ fun i => i)) := by
                  refine' strictMono_nat_of_lt_succ _
                  intro n; exact (by
                  exact Nat.lt_of_lt_of_le ( Nat.lt_succ_self _ ) ( Nat.le_mul_of_pos_right _ ( pow_pos ( by decide ) _ ) ))
                generalize_proofs at *
                linarith [ h_kraft_A_mono ( show ( j : ℕ ) < i from by assumption ) ]
              linarith
            · grind
        · unfold Kraft.natToBits
          aesop

/-
We can sort a finite type `I` by `l`.
-/
lemma exists_equiv_fin_monotone {I : Type _} [Fintype I] (l : I → ℕ) :
    ∃ e : Fin (Fintype.card I) ≃ I, Monotone (l ∘ e) := by
      have h_order_iso : ∃ (e : Fin (Fintype.card I) ≃ I), ∀ i j, i ≤ j → l (e i) ≤ l (e j) := by
        -- By definition of `Finset.sort`, we can obtain a sorted list of elements from `I` based on `l`.
        obtain ⟨sorted_list, h_sorted⟩ : ∃ sorted_list : List I, List.Pairwise (fun x y => l x ≤ l y) sorted_list ∧ List.length sorted_list = Fintype.card I ∧ List.Nodup sorted_list ∧ ∀ x ∈ sorted_list, x ∈ Finset.univ := by
          have h_insertion_sort : ∀ {xs : List I}, List.Nodup xs → ∃ sorted_list : List I, List.Pairwise (fun x y => l x ≤ l y) sorted_list ∧ List.length sorted_list = List.length xs ∧ List.Nodup sorted_list ∧ ∀ x ∈ sorted_list, x ∈ xs := by
            have h_insertion_sort : ∀ {xs : List I}, List.Nodup xs → ∃ sorted_list : List I, List.Pairwise (fun x y => l x ≤ l y) sorted_list ∧ List.length sorted_list = List.length xs ∧ List.Nodup sorted_list ∧ ∀ x ∈ sorted_list, x ∈ xs := by
              intro xs h_nodup
              exact ⟨List.insertionSort (fun x y => l x ≤ l y) xs, by
                convert List.pairwise_insertionSort _ _
                · exact ⟨ fun x y => le_total _ _ ⟩
                · exact ⟨ fun x y z hxy hyz => le_trans hxy hyz ⟩, by
                exact List.length_insertionSort (fun x y ↦ l x ≤ l y) xs, by
                exact List.Perm.nodup_iff ( List.perm_insertionSort _ _ ) |>.2 h_nodup, by
                exact fun x hx => List.mem_insertionSort ( fun x y => l x ≤ l y ) |>.1 hx⟩
            assumption
          simpa using h_insertion_sort ( Finset.nodup_toList Finset.univ )
        have h_equiv : ∃ e : Fin (Fintype.card I) ≃ I, ∀ i, e i = sorted_list[i] := by
          have h_equiv : Function.Bijective (fun i : Fin (Fintype.card I) => sorted_list[i]) := by
            have h_equiv : Function.Injective (fun i : Fin (Fintype.card I) => sorted_list[i]) := by
              intro i j hij
              have := List.nodup_iff_injective_get.mp h_sorted.2.2.1
              exact Fin.ext <| by simpa [ h_sorted.2.1 ] using this hij
            have := Fintype.bijective_iff_injective_and_card ( fun i : Fin ( Fintype.card I ) => sorted_list[i] ) ; aesop
          exact ⟨ Equiv.ofBijective _ h_equiv, fun i => rfl ⟩
        obtain ⟨ e, he ⟩ := h_equiv
        refine' ⟨ e, fun i j hij => _ ⟩
        have := List.pairwise_iff_get.mp h_sorted.1
        cases lt_or_eq_of_le hij <;> simp_all [ Fin.ext_iff ]
        exact this ⟨ i, by linarith [ Fin.is_lt i, Fin.is_lt j ] ⟩ ⟨ j, by linarith [ Fin.is_lt i, Fin.is_lt j ] ⟩ ‹_›
      exact ⟨ h_order_iso.choose, fun i j hij => h_order_iso.choose_spec i j hij ⟩

end AristotleLemmas

theorem kraft_inequality_tight_infinite {I : Type _} (l : I → ℕ)
    (h_summable : Summable (fun i ↦ (1 / 2 : ℝ) ^ l i))
    (h_sum : ∑' i, (1 / 2 : ℝ) ^ l i ≤ 1) :
    ∃ w : I → List Bool,
      Function.Injective w ∧
      PrefixFree (Set.range w) ∧
      ∀ i, (w i).length = l i := by
  by_cases h_finite : Finite I
  · haveI := Fintype.ofFinite I
    -- By `exists_equiv_fin_monotone`, there exists an equivalence `e : Fin (card I) ≃ I` such that `l ∘ e` is monotone.
    obtain ⟨e, he⟩ : ∃ e : Fin (Fintype.card I) ≃ I, Monotone (l ∘ e) := by
      exact exists_equiv_fin_monotone l
    -- By `kraft_inequality_tight_finite_mono`, there exists `w' : Fin (card I) → List Bool` satisfying the conditions for `l ∘ e`.
    obtain ⟨w', hw'⟩ : ∃ w' : Fin (Fintype.card I) → List Bool, Function.Injective w' ∧ Kraft.PrefixFree (Set.range w') ∧ ∀ i, (w' i).length = l (e i) := by
      have h_sum_eq : ∑ i, (1 / 2 : ℝ) ^ (l (e i)) ≤ 1 := by
        convert h_sum using 1
        rw [ tsum_fintype, ← Equiv.sum_comp e ]
      exact kraft_inequality_tight_finite_mono (fun i ↦ l (e i)) he h_sum_eq
    refine' ⟨ w' ∘ e.symm, _, _, _ ⟩ <;> simp_all [Function.Injective]
    exact fun a₁ a₂ h => e.symm.injective ( hw'.1 h )
  · have h_equiv : ∃ e : ℕ ≃ I, Monotone (l ∘ e) := by
      convert exists_equiv_nat_monotone_of_infinite l h_summable using 1
      simpa using h_finite
    obtain ⟨ e, he ⟩ := h_equiv
    have h_exists_w : ∃ w : ℕ → List Bool, Function.Injective w ∧ Kraft.PrefixFree (Set.range w) ∧ ∀ i, (w i).length = l (e i) := by
      have h_exists_w : ∑' i : ℕ, (1 / 2 : ℝ) ^ l (e i) ≤ 1 := by
        convert h_sum using 1
        conv_rhs => rw [ ← Equiv.tsum_eq e ]
      have h_exists_w : Summable (fun i : ℕ => (1 / 2 : ℝ) ^ l (e i)) := by
        convert h_summable.comp_injective e.injective using 1
      expose_names
      exact kraft_inequality_tight_nat_mono (fun i ↦ l (e i)) he h_exists_w h_exists_w_1
    obtain ⟨ w, hw₁, hw₂, hw₃ ⟩ := h_exists_w
    refine' ⟨ fun i => w ( e.symm i ), _, _, _ ⟩
    · exact hw₁.comp e.symm.injective
    · intro x hx y hy hxy
      aesop
    · aesop

end Kraft
