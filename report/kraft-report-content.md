# Kraft Formalization — Report Content (Draft)

Source for a 2–4 page PDF summary report. Content only; formatting decisions deferred.

---

## Header

- **Title:** Formalizing Kraft's Inequality in Lean 4 — Project Summary Report
- **Author:** Elazar Gershuni
- **Date:** 2026-04-19
- **Project duration:** 2025-12-07 → 2026-01-23 (≈7 weeks, 149 commits on `main`)
- **License:** Apache 2.0

### Links

- Repository: <https://github.com/elazarg/kraft>
- README: `README.md` in the repo root (full file list, build instructions, theorem table)
- Mathematical specification: `kraft.tex` in the repo root
- Upstream Mathlib PR (merged): <https://github.com/leanprover-community/mathlib4/pull/34108>
- Upstream Lean 4 PR (merged): <https://github.com/leanprover/lean4/pull/12108>

---

## 1. Original task vs. delivered scope

**Original task.** Formalize the contents of `kraft.tex` in Lean 4 + Mathlib. The source file contains four results:

1. Kraft's inequality for finite prefix-free codes over `{0,1}` (two proofs: disjoint-extension counting and induction on max length).
2. Converse (Theorem `kraft-tight`): any length sequence with `∑ 2^{-ℓᵢ} ≤ 1` is realized by a prefix-free code. Relies on an auxiliary "subset-sum equals 1" lemma.
3. Kraft–McMillan inequality for uniquely decodable codes, proved via the `r`-fold concatenation trick and the bound `C ≤ (rℓ)^{1/r} → 1`.
4. Prefix-free ⟹ uniquely decodable (assuming `ε ∉ S`).

**What actually shipped.** All four, plus substantial generalizations and an application:

| # | Direction | What was added |
|---|---|---|
| 1 | Alphabet | All results parameterized by an alphabet of size `D`, not just `{0,1}` (`Fintype α` with `Nontrivial α`). |
| 2 | Index set | Converse and Kraft inequality extended to **infinite** index sets (`Summable` + `tsum` bounds). |
| 3 | Abstraction | Kraft–McMillan proved once abstractly for any graded monoid via a `WeightModel` structure (`KraftGeneralized.lean`); the list case is a specialization. |
| 4 | Weight model | Lifted from natural-number counting (`KraftNatural.lean`) to `ℝ≥0`-valued weights via a limit argument; both `ℝ≥0` and `ℝ` surface APIs. |
| 5 | Application | `SourceCodingLowerBound.lean` proves `H_D(p) ≤ E[L]` via the Gibbs / KL divergence inequality for any uniquely decodable code. |
| 6 | Application | `Example.lean` proves Shannon-Fano: `exists_prefix_code_near_entropy` — `E[L] < H_D(p) + 1`. |
| 7 | Upstream | Mathlib PR #34108 (Kraft-McMillan + `UniquelyDecodable`). |
| 8 | Upstream | Lean 4 PR #12108 (list `prefix_map_iff_of_injective` / `suffix_map_iff_of_injective`). |

None of items 2–8 are in `kraft.tex`. They arose naturally: to prove the `tex` version cleanly, the abstractions underneath kept suggesting they were the real theorems.

---

## 2. Architecture

Layered dependency diagram (top imports bottom):

```
         SourceCodingLowerBound    Example (Shannon-Fano)
                    \            /
                     \          /
         Kraft    KraftConverse    KraftMcMillan
            \        |                /
             \       |               /
              KraftGeneralized  (ℝ≥0 weight model, limits)
                        |
              KraftNatural  (ℕ counting, ExpBounded axiom, prodTuple)
                        |
        PrefixFree   UniquelyDecodable  (definitions, basic lemmas)
```

Sizes (.lean lines): `KraftConverse` 408, `KraftNatural` 408, `KraftGeneralized` 306, `SourceCodingLowerBound` 300, `Example` 253, `PrefixFree` 153, `Kraft` 99, `KraftMcMillan` 96, `UniquelyDecodable` 63. Plus `ConstructionHelpers/` for the converse: `Construction.lean` (568), `Codeword.lean` (294), `Sum.lean` (92), `ExtShift.lean` (68), `Helpers.lean` (38). Core library (excluding helpers): ≈ 2086 lines; with helpers: ≈ 3146 lines.

**Key abstractions worth naming in the report:**

- `ExpBounded (len : M → ℕ) (base : ℕ)` (`KraftNatural.lean:118`): for any finite `T ⊆ M`, the number of `x ∈ T` with `len x = s` is `≤ base^s`. This is what makes the McMillan counting argument go through for *any* monoid, not just lists.
- `prodTuple : (Fin r → S) → M` (`KraftNatural.lean:122`): the r-fold product of elements drawn from a finite set `S ⊆ M`.
- `WeightModel M D` (`KraftGeneralized.lean:61`): bundles a cost `M → ℕ` additive under multiplication, a multiplicative weight `μ : M →* ℝ≥0`, and the domination `μ x ≤ (1/D)^{cost x}`. This is the monoid-agnostic statement of "D-ary code with sub-geometric weights".

**Public theorem surface** (what a user of the library calls):

- `InformationTheory.kraft_inequality` (`Kraft.lean:51`) — finite prefix-free case.
- `InformationTheory.kraft_inequality_infinite` (`Kraft.lean:69`) — infinite via `HasSum` + bound.
- `InformationTheory.kraft_mcmillan_inequality` (`KraftMcMillan.lean:86`) — uniquely decodable, general `D`.
- `InformationTheory.kraft_inequality_of_injective` / `_real` (`KraftGeneralized.lean:278`, `:293`) — abstract monoid.
- `InformationTheory.exists_code` (`KraftConverse.lean:300`) — converse for arbitrary index type, finite or infinite.
- `InformationTheory.exists_code_binary` (`KraftConverse.lean:395`) — converse specialized to `List Bool`.
- `InformationTheory.source_coding_lower_bound` (`SourceCodingLowerBound.lean:198`) — `H_D(p) ≤ E[L]`.
- `InformationTheory.exists_prefix_code_near_entropy` (`Example.lean:100`) — Shannon-Fano bound.
- `InformationTheory.PrefixFree.uniquely_decodable` — prefix-free ⟹ uniquely decodable.
- `InformationTheory.UniquelyDecodable.prod_injective` — uniquely decodable ⟹ concatenation injective on list-tuples.

---

## 3. Issues overcome

A running list of concrete problems that consumed real time, with the commit or file that closed each one.

### 3.1 Constructive converse

The converse required an algorithmic allocator of D-ary intervals. The spec says "there exists a prefix-free code"; the proof had to name one. `ConstructionHelpers/Construction.lean` (568 lines) implements it via `kraftNumerator` (interval start positions) and `kraftCodeword` (fixed-width digit representations). The public theorem `exists_code` packages finite (`Fin k`) and infinite (`ℕ`) paths and transports through `exists_equiv_fin_monotone` / `exists_equiv_nat_monotone_of_infinite` so callers never pick. Commits `83847cd`, `f469698` ("Converse complete"), then cleanup `128b4c0`, `53b24d7`.

### 3.2 Eliminating subtraction in ℕ (`96fd642`, 2026-01-23)

Natural-number subtraction in Lean is truncated (`5 - 7 = 0`), which breaks ring-style rewrites. Earlier versions of `KraftNatural` threaded `Nat.sub_add_cancel` everywhere. The "no-subtraction version" rewrote the counting bound so the invariants only need additive identities, removing a class of brittle hypotheses. The still-remaining subtraction (e.g. `pow_sub_mul_inv_pow_eq_inv_pow` in `KraftGeneralized`) is now isolated behind a one-shot lemma.

### 3.3 Weakening injectivity (`c02b15f`, 2026-01-23)

The abstract Kraft statement originally required a stronger injectivity hypothesis on `prodTuple`. Tightening what was actually used in the proof let the monoid statement `kraft_inequality_of_injective'` accept just "for every `r`, `prodTuple` is injective on `S^r`" — exactly the McMillan unique-decodability condition.

### 3.4 List → monoid (`9722f44`, `c69e809`)

Original proofs were over `List α` with concatenation. Extracting the proof to an arbitrary monoid via `WeightModel` + `ExpBounded` was what made the surface API small and uniform — `KraftMcMillan.lean` shrinks to ~10 lines of plumbing, and `Example.lean` / `SourceCodingLowerBound.lean` reuse the same engine.

### 3.5 `ℕ` → `ℝ≥0` via limits (`c8727a6`, `387197b`)

The natural-number counting bound `K^r ≤ r · maxLen + 1` doesn't directly give `K ≤ 1`; you need to take `r`-th roots and push `r → ∞`. `pow_sum_le_linear_bound_of_inj` packages the counting side in `ℝ≥0`; `kraft_inequality_of_injective'` closes with a `by_contra` plus `tendsto_self_mul_const_pow_of_abs_lt_one` to derive the contradiction `K > 1 ⟹ K^r` outgrows any linear bound.

### 3.6 Fighting automation brittleness

A recurring theme in the git log:

- `grind` was introduced and then removed: commits `aee5a3d`, `0d1df02`, `cc6779c`, `eb920e4` (all titled "grind--"), then `1bb4829` ("Finish all theorems, organize, remove brittle grind"), then `f20c1dd` ("no grind"). Verdict: `grind` closes a goal today but the next Mathlib bump may reshuffle it silently. For a formalization intended to outlive the current toolchain, explicit rewrites are worth the verbosity.
- `simp_all` → `simp_all only`: commits `199c631`, `f063ddb`, `4f766ca`. `simp_all` pulls in every hypothesis and is similarly fragile.
- `generalize_proofs` avoidance: commits `fd392b2`, `062c26d`, `900f8e3`. Anonymous proof terms leak through and clash on refactor.
- `aesop` removed (`eb44360`).

### 3.7 Reusing Mathlib's `Digits` (`b2e6377`)

The converse originally defined a bespoke `natToDigits`. Replacing it with `Nat.digits` (mathlib) removed dozens of lines of index arithmetic and gave library lemmas for free.

### 3.8 `Pair.Lex` for ordering codewords (`b0f0fc9`)

The construction orders codewords lexicographically by `(length, index)`. Rolling a custom order led to unfolding issues; switching to `Prod.Lex` gave decidable comparison and `Finset.sorted` hooks out of the box.

### 3.9 Gibbs inequality for the source coding bound

The last sorry (`33503f6`) was the discrete Gibbs step `0 ≤ ∑ p·log(p/q)`. Rather than prove non-negativity of KL from scratch, the final version routes through Mathlib's `klDiv` for measures: define `pmfMeasure`, show absolute continuity, transport `MeasureTheory.toReal_klDiv_of_measure_eq`, then specialize back to a `Finset.sum` (`gibbs_sum_log_ratio_nonneg` at `SourceCodingLowerBound.lean:141`). This is a small example of when buying into Mathlib's heavy measure-theoretic stack pays for itself.

A known limitation: `source_coding_lower_bound` currently requires `hp_pos : ∀ i, 0 < p i`; the file has a `TODO` sketching how to relax to `p i ≥ 0` via support truncation or `q_ε = (1-ε)q + εr` regularization.

### 3.10 Finite ↔ infinite bookkeeping

`kraft_inequality_infinite` bridges finite sums and `tsum`. The trick: bound every finite partial sum by 1 (via the finite `kraft_inequality`), conclude `Summable` via `summable_of_sum_le`, then use `h_summable.tsum_le_of_sum_le`. `Kraft.lean:69–97` is worth pointing at as a pattern for other "convergent by finite subsums" results.

---

## 4. AI interaction

Three assistants were involved, with very different weights:

- **ChatGPT (GPT-5.2 era)** — the primary tool. Most day-to-day proof drafting, refactoring and golfing ran through it.
- **Gemini 3** — a secondary opinion, consulted when ChatGPT stalled. Sometimes it agreed with ChatGPT in a way that turned out to be wrong.
- **Aristotle (Harmonic)** — used once, for one critical step, with outsized impact (see below).

A coding agent was **not** part of the normal workflow; any contribution was limited to minor polish at the very end.

### 4.1 The Aristotle episode

On 2026-01-08, stuck on the auxiliary "find a prefix whose D-adic weights sum to exactly 1" lemma that the converse depends on, I asked Aristotle for a proof. ChatGPT and Gemini, consulted in parallel, both insisted the approach Aristotle proposed was wrong and should be discarded in favour of theirs.

I committed Aristotle's proof anyway: `1208162` *"aristotle, but cleaned and readable"* (612 lines) and `a8ee271` *"more kraft_aristotle"* (+202). It turned out to need only small gaps filled. Later the same day: `16e37f6` *"almost all sorrys removed"*, `165bee2` *"kraft_inequality_tight"* — the converse was closed. The generalized form of the lemma survives today as `exists_prefix_sum_eq_one_of_sorted` (post-generalization commit `53b24d7`).

**Lesson:** "both mainstream models agree this is wrong" is not authoritative. Two frontier LLMs confidently dismissing a proof is at most weak evidence. If the goals close, the proof is right.

### 4.2 Where AI was strong

- **Bookkeeping-heavy algebra.** Rearranging `(∑ μ x)^r = ∑ μ(prodTuple w)` (`KraftGeneralized.lean:80`), cancellations like `D^(N-c) · (D^N)⁻¹ = (D⁻¹)^c` (`:93`). Tedious and mechanical; AI drafts were usually right after one or two revisions.
- **Golfing.** Commits *"simpler / golfier / simpler still"* (`909e419`, `6e08ac3`, `0fae010`) came from "can this be shorter" prompts.
- **Naming.** `WeightModel`, `ExpBounded`, `prodTuple`, `kraftNumerator`, `kraftCodeword` — all AI-assisted, all survived mathlib review.
- **Boilerplate.** The finite↔infinite case split in `exists_code` and the alphabet-lift `transport_code`.

### 4.3 Where AI was weak — and the cleanup it triggered

The git log itself is the honest record:

- **Hallucinated lemma names.** Pervasive. The discipline that emerged: always search (grep / loogle / leansearch) before believing a name exists.
- **Over-reliance on closing tactics.** `grind`, `simp_all`, `aesop` routinely closed goals that then silently broke:
  - `aee5a3d`, `0d1df02`, `cc6779c`, `eb920e4` — all titled *"grind--"*.
  - `1bb4829` *"Finish all theorems, organize, remove brittle grind"*; `f20c1dd` *"no grind"*.
  - `199c631`, `f063ddb`, `4f766ca` — `simp_all` → `simp_all only`.
  - `eb44360` *"no aesop"*.
  - `fd392b2`, `062c26d`, `900f8e3` — removing `generalize_proofs` (leaked anonymous proof terms breaking refactors).
- **Premature abstraction.** Early drafts tried to land directly at monoid level and failed. The working order was: concrete binary proof, identify the 2–3 structural lemmas used, then generalize (`9722f44` "monoid", `c69e809` "genealization complete").

### 4.4 Division of labour and external review

Architecture (when to generalize, file layout, what to upstream), all review, and every final-commit decision were mine. AI drafted 2–50-line tactic blocks and proposed refactors; every block was read before commit, and dozens of "cleanup" / "simplify" commits are follow-ups on AI-produced proofs.

A useful external check came from the Mathlib PR (#34108). Reviewers (vlad902 on style, dupuisf as maintainer, sgouezel and YuvalFilmus chiming in) requested only stylistic changes — calc-block indentation, inlining of intermediate type annotations, rewording to `Fin r → List α`. No mathematical revisions. The AI-assisted proofs survived human review on their mathematical content.

---

## 5. Upstream contributions

### Mathlib PR #34108 (MERGED via Bors, +240 lines)

Title: *feat(InformationTheory/Coding): Kraft-McMillan inequality for uniquely decodable codes*.

Contents:

- New: `Mathlib/InformationTheory/Coding/UniquelyDecodable.lean` (+57) — definition + `epsilon_not_mem`.
- New: `Mathlib/InformationTheory/Coding/KraftMcMillan.lean` (+165) — `kraft_mcmillan_inequality`.
- Touched: `Mathlib/Data/Fintype/BigOperators.lean` (+16) — supporting `Finset.card_filter_length_eq_le` and `sum_pow_length_filter_eq_le_card_mul`.
- Touched: `Mathlib.lean` (+2) — import registration.

Establishes a new `InformationTheory.Coding` namespace in Mathlib, intended as a home for further coding-theory results (the local project has infinite Kraft–McMillan, the full converse, and the source coding lower bound still to offer upstream — `YuvalFilmus` flagged exactly the first two as natural follow-ups in the PR review).

**Review summary.** Three rounds of style back-and-forth with `vlad902` (golf, indentation, inlining) and `metakunt`; maintainer `dupuisf` guided the PR to completion with "starting to look very good"; `sgouezel` and `dupuisf` both issued `bors r+`. No mathematical revisions were requested — the math was correct on first submission.

### Lean 4 PR #12108 (MERGED, +8 lines)

Title: *feat: add prefix and suffix map injectivity lemmas*.

Adds `prefix_map_iff_of_injective` and `suffix_map_iff_of_injective` to `Init/Data/List/Nat/Sublist.lean`: for injective `f`, `l₁.map f <+: l₂.map f ↔ l₁ <+: l₂`. Surfaced while proving the converse; `transport_code` (the alphabet-embedding step) needs exactly this. CI nitpicks only; approved by `Rob23oba` and merged. Small, but reusable enough to justify upstreaming.

---

## 6. Advice for future students

1. **Start from a tight spec.** `kraft.tex` was 360 lines and a huge asset. Without it the project would have spent weeks disagreeing with itself about conventions (ℓ vs. |w|, base 2 vs. base D, `Fin k` vs. `ℕ`).
2. **Budget a generalization pass.** The first end-to-end proof is rarely the one you keep. Plan for at least one "now do it over a monoid" rewrite; it often simplifies the concrete case too.
3. **Keep `ℕ` and `ℝ` apart.** Subtraction and division break differently in each. The split between `KraftNatural.lean` (pure ℕ counting) and `KraftGeneralized.lean` (ℝ≥0 + limits) was a late but decisive refactor.
4. **Prefer explicit rewrites over `grind`/`simp_all`/`aesop`** in any proof you expect to survive a Mathlib bump. These tactics are fine for quick sketches; they are not fine as the final proof of a public theorem.
5. **`lean_local_search` before you guess.** Every hallucinated lemma name costs an edit-compile cycle. Every correct guess saves one.
6. **Upstream utility lemmas as you find them.** The Lean-4 PR was 8 lines and took one afternoon. It would have been a permanent local hack otherwise.
7. **Split finite and infinite cleanly.** `Summable` + `tsum` + `HasSum` give a clean story; don't try to prove the infinite case by "passing to the limit" inside a finite proof.
8. **Let Mathlib do the heavy lifting.** `Nat.digits`, `klDiv`, `tendsto_self_mul_const_pow_of_abs_lt_one`, `Prod.Lex` — using each of these saved ≥ 100 lines of bespoke machinery. If a concept has a classical name, grep for it before rolling your own.

---

## 7. References

- `kraft.tex` — mathematical exposition of the four theorems this project formalizes.
- Cover & Thomas, *Elements of Information Theory*, Chapter 5.
- Kraft, L.G. (1949), *A device for quantizing, grouping, and coding amplitude-modulated pulses*.
- McMillan, B. (1956), *Two inequalities implied by unique decipherability*.
- Mathlib 4 (v4.26.0); Lean 4 (v4.26.0).

---

## Open questions / gaps to flag before compiling to PDF

1. **Course / supervisor info** — should the header include a course number, instructor name, institution?
2. **Length preference** — current content naturally fills ~4 pages. Trim to 2–3 if preferred?
3. **Lean code snippets** — should the report quote small Lean fragments (e.g. the `WeightModel` definition, or one of the `grind--` commits) or stay prose + theorem names only?
4. **Target format / style** — LaTeX article mirroring `kraft.tex`, or simpler (Markdown→PDF)? `pdflatex`/`xelatex` are available locally.
