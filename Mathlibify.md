# Mathlibifying `kraft`

Investigation note, 2026-08-05 (revised after review). Goal: **100% mathlib style/structure
compatibility** — not a subset filtered by what seems worth the effort. Everything identified
below gets done; the phases below are a sequencing of that work by risk and dependency, not a
triage of what to skip.

## Evidence base

1. **PR [#34108](https://github.com/leanprover-community/mathlib4/pull/34108)** (merged
   2026-02-17): this codebase's own `UniquelyDecodable.lean`/`KraftMcMillan.lean` went through
   full mathlib review once already, by `dupuisf` and `vlad902`. This is the single most
   relevant data source — it's *this project's* code being held to *this exact* standard, not a
   generic style guide.
2. **Official docs**: [naming conventions](https://leanprover-community.github.io/contribute/naming.html)
   and [style guide](https://leanprover-community.github.io/contribute/style.html) on the
   community website (not vendored locally — fetched directly).
3. **Automated linters actually enforced on mathlib**, read from the pinned
   `.lake/packages/mathlib/Mathlib/Tactic/Linter/Style.lean` and `Header.lean`: exact
   thresholds, not folklore.
4. **A census of the pinned mathlib snapshot itself** (`.lake/packages/mathlib`, `v4.32.2`), to
   check which conventions are actually followed at scale, including how often mathlib's own
   *stated* preferences (e.g. subscripts) diverge from its *practiced* norms — see the
   hypothesis-naming finding below, which changes what "compatible" means for one of the gaps.

## What the PR review actually said

Filtered to substance (style-bot autoformatting nits like "indent this block two spaces"
omitted — those are mechanical and already enforced by CI, not useful signal):

- **`dupuisf`** pushed back on `Fin r → S` with `S : Set (List α)` as "a strange choice... why
  not simply `Fin r → List α`?" — resolved by keeping the public `UniquelyDecodable : Set (List
  α) → Prop` interface (needed for `Set.range`/infinite compatibility) but making the *internal*
  `concatFn`/`concatFn_injective_of_uniquelyDecodable` machinery `Finset`-based, coercing to
  `Set` only at the point of applying the hypothesis. **This split — `Set` at the public
  boundary, `Finset` internally where sums/cardinality are needed — is now the sanctioned
  upstream pattern and needs no further action here.**
- **`vlad902`**, repeatedly: prefer subscripts (`L₁ L₂`, not `L1 L2`) for indexed mathematical
  objects; prefer `have h (a : A) : ...` over `have : ∀ a, ...` (saves an `intro`); prefer
  `.mp`/`.mpr` projections over `.1`/`.2` on `Iff`; a proof that's a single `by refine`/`by
  exact`/`by apply` should just be the term; get rid of explicit types where Lean can infer them;
  100-char line limit is real and enforced (one suggestion literally just rewraps a line that
  fit).
- **`dupuisf`**: split `public import`s from private `import`s, matching the module-system
  convention (the merged file's own `public import` block is *not* alphabetized — `List.Basic,
  Finset.Basic, Real.Basic, BigOperators.Pi, Fintype.Card, Fintype.BigOperators,
  UniquelyDecodable` — so alphabetization is not itself an enforced norm, see gap #6 below); a
  broadly useful private lemma should move to a more general file
  (`Mathlib.Data.Fintype.BigOperators`) and become public, `Finset`-namespaced — the merged name
  is **`Finset.card_filter_length_eq_le`**.
- **`YuvalFilmus`** (non-style): suggested TODOs for infinite Kraft–McMillan and the converse —
  both already exist in this repo (`KraftConverse.lean`, `KraftGeneralized.lean`), unmerged.

None of this is about *this repo's* current content being wrong — it's about the shape mathlib
expects, which the rest of this document checks the other 18 files against.

## Gap census (this repo, 20 `.lean` files, ~5015 lines, checked 2026-08-05)

| # | Gap | Scope | Notes |
|---|---|---|---|
| 1 | No file uses the `module` / `public import` header | **0/20 files** (mathlib `Mathlib/` subtree: **8264/8264, 100%**) | Biggest single structural gap. First census run undercounted mathlib at 8194/8264 by matching `^module$` exactly and missing lines like `module -- shake: keep-all`; corrected via prefix match. |
| 2 | Lines over 100 chars | **19 lines across 7 files**: `Construction.lean` (7), `KraftConverse.lean` (4), `SourceCodingLowerBound.lean` (2), `PrefixFree.lean` (2), `Codeword.lean` (2), `Uniform.lean` (1), `KraftGeneralized.lean` (1) | Mechanical. |
| 3 | `open scoped BigOperators` (vestigial: notation is global) | 4/20 files (mathlib: 13/8264 — proportionally ~600x rarer there) | Mechanical, verified safe to delete. |
| 4 | `open scoped Classical` unscoped at file level | 1 file (`Divergence/Tensorization.lean`) | Exact target of the `openClassical` linter. |
| 5 | ASCII-digit **object** indices (`L1 L2`, `w1 w2`, `j1 j2`, `A0`, `x0`, `l1`) instead of subscripts | Almost entirely `KraftConverse.lean` (28/28 digit-suffixed identifiers are object-level, 0 hypotheses) and `ConstructionHelpers/Codeword.lean` (7/7 object-level); `Construction.lean` is mixed (5 object / 8 hypothesis) | This is the real target of `vlad902`'s repeated review comment — genuine mathematical-object indices, not hypothesis names. See gap #6b for why hypothesis names are a *separate* question with the opposite answer. |
| 6a | Import alphabetization | All 20 files | **Demoted from "gap" to optional polish**: the merged, review-approved `KraftMcMillan.lean` itself is not alphabetized (see PR notes above), so this isn't an enforced norm even on this project's own upstreamed code. Do it for tidiness, not compatibility. |
| 6b | Hypothesis-name digit suffixes (`hp0`/`hp1`/`hq0`/`hq1`, ~217 occurrences concentrated in `Pinsker.lean` (167/168 digit-suffixed identifiers), `ChainRule.lean` (50/50), `Binary.lean`) | Widespread | **Do not subscript these.** Mathlib's own style guide names `h, h₁` as the example, but a direct census of `.lake/packages/mathlib/Mathlib` shows ASCII `h0`/`h1` outnumbering subscript `h₀`/`h₁` **4603 to 659** (≈7:1) in practice. Converting `hp0`→`hp₀` would move *away* from real mathlib usage, not toward it. Leave as-is; this is compatibility, correctly resolved by inaction. |
| 7 | No local lint-style tooling | Repo-wide (no `lake exe lint-style` equivalent, no `#lint` wired into CI) | This is *how* mathlib enforces 1–5 continuously; without it, drift resumes immediately after a one-time pass. |
| 8 | Module docstrings (`Main definitions`/`Main results`/`References`), copyright headers | Already followed correctly everywhere | No action. |
| 9 | `Set`/`Finset` boundary pattern from the PR pushback | Already correctly inherited via the `Mathlib.InformationTheory.Coding.UniquelyDecodable` import | No action. |

## Plan

**Phase 0 — derisk the module-system move (½ day).** `module`/`public import` is a Lean
language feature, not a Mathlib-specific tool, so it should work unmodified in this project at
`v4.32.2` (confirmed: mathlib's own `lakefile.toml` sets no module-related options beyond what's
already in this repo's). Pilot it on `PrefixFree.lean` first — small, but not trivial: it
currently has **five** imports (`List.Basic`, `Set.Basic`, `Finset.Basic`, `Finset.Card`,
`InformationTheory.Coding.UniquelyDecodable`), all five plausibly `public` since `PrefixFree`
and `PrefixFree.uniquely_decodable` expose `List`/`Set`/`UniquelyDecodable` types in their
signatures — so the per-file classification work in Phase 2 is real work, not a rubber stamp,
even on a small file. Add `module`, convert all five to `public import`, verify `lake build`
still succeeds and downstream importers (`InformationTheory/Coding/Kraft.lean`,
`KraftConverse.lean`, the root `Kraft.lean` aggregator) still resolve `PrefixFree` correctly.

**Phase 1 — mechanical, low-risk, can be scripted (1 day).**
- Delete the 4 stale `open scoped BigOperators` lines; rebuild to confirm they were genuinely
  unused (expected, since the notation is global at this mathlib version).
- Rewrap the 19 long lines (7 files, see gap #2) to ≤100 chars.
- Replace `open scoped Classical` in `Tensorization.lean` with either the `classical` tactic
  locally in the proofs that need it, or `open scoped Classical in` scoped to just those
  declarations.

**Phase 2 — the module-system conversion, file by file (2–3 days for 20 files).** For each
file: add `module`; classify every import as public or private (a dependency is `public import`
if a *public* declaration in the file exposes a type from it in its signature — the common case
here, since almost nothing is currently `private` at the type level); decide `@[expose] public
section` vs granular `public theorem`/`public def` per declaration (mathlib uses the blanket
`@[expose] public section` in ~60% of files — appropriate here too, since `private` already does
the hiding job explicitly where it's used). Order: leaf files first (`PrefixFree`, `Codeword`,
`Helpers`, `Sum`, `ExtShift`, `Uniform`, `Basic`, `Binary`), then files that import them, ending
with the root `Kraft.lean` aggregator. Rebuild after each file, not at the end — a module-system
error in file 3 is much cheaper to diagnose than after 20 files are converted. Alphabetize
imports while touching each file's header anyway (gap #6a — free, since the header is already
being rewritten, even though it's not itself required).

**Phase 3 — object-index subscript pass (½ day, smaller than originally scoped).** Rename the
genuine object-level ASCII-digit indices from gap #5 to subscripts: `KraftConverse.lean` (all 28
occurrences: `j1 j2` etc.) and `Codeword.lean` (all 7: `l1 l2` etc.) are the real work;
`Construction.lean`'s 5 object-level occurrences (`e0` etc., out of its 13 total digit-suffixed
identifiers) round it out. **Explicitly skip** the hypothesis-name suffixes covered by gap
#6b — `hp0`/`hp1`/`hq0`/`hq1` and friends stay as-is, per the census above; touching them would
be a regression, not compatibility work.

**Phase 4 — wire up the tooling that makes 1–3 stick (1 day).** Mathlib's `lake exe lint-style`
and `#lint` (from Batteries, already a transitive dependency via mathlib) are what keep drift
from creeping back. Add a `lake exe lint-style` equivalent — either vendor mathlib's
`scripts/lint-style.py`/`lint-style.lean` invocation pattern, or write a thin project-local
script that runs Batteries' `#lint` over each file and checks line length / file length /
`module` presence — and note it in this project's `CLAUDE.md` as a required pre-commit or
pre-PR step, the same way `lake build` already is. This phase is what turns phases 0–3 from a
one-time cleanup into an actually-maintained invariant.

## Sequencing note

Phases 0–2 (module system) are independent of phase 3 and could run in parallel if desired, but
phase 2 touches every file's header, so doing the subscript pass (3) *after* 2 avoids merge
friction on the same lines twice. Phase 4 should land as soon as phase 1 is done (it doesn't
need to wait for 2–3), so that the module-system conversion itself is done under a lint gate
rather than being the thing that first establishes one.
