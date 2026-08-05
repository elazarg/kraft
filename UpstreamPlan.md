# Upstream order

Proposal, 2026-08-05. `UniquelyDecodable.lean`/`KraftMcMillan.lean` are already merged
([#34108](https://github.com/leanprover-community/mathlib4/pull/34108)). This proposes an order
for the rest, scored on the four things a mathlib reviewer actually reacts to — confirmed
against how #34108 itself went (dupuisf and vlad902 pushed on: minimal-necessary imports, no
redundant proofs of the same fact sitting in the library, and PR size — that review ran a full
month, Jan 18 to Feb 17, for ~400 lines with heavy back-and-forth):

- **Dependency** — can't go up before its prerequisites are merged (or bundled with them).
- **Reusability** — does it fill a gap the wider ecosystem recognizes, or is it project-specific
  glue? (`Mathlib.InformationTheory` currently has only `Coding/`, `Hamming`, and
  `KullbackLeibler` — no Shannon entropy, no conditional entropy, no discrete KL divergence, no
  Pinsker. That's the gap map this plan works against.)
- **Self-containment** — does the chunk have a clear "this is the whole point" narrative on its
  own, or does it only make sense bundled with something else?
- **Size** — smaller, single-concept PRs review faster and build trust for the bigger ones.

## The map: two independent tracks plus one bridge

Dependency analysis (from this repo's own import graph) shows the remaining code splits into
two tracks that don't need each other, plus one file that bridges them, plus one track that's
been quietly orphaned:

```
Track A (coding theory, needs the merged PR):
  PrefixFree -> Kraft.lean -> SourceCodingLowerBound -> ConditionalEntropy + Uniform
                                                                |
Track B (divergence, needs nothing from A):                    |
  Basic -> Binary -> Pinsker -> Tensorization (partial)         |
                                                                |
Bridge: ChainRule needs ConditionalEntropy (A) AND Basic (B) ---+

Track C (converse, needs only PrefixFree from A):
  Sum + ExtShift + Helpers -> Codeword -> Construction -> KraftConverse

Orphaned: KraftNatural + KraftGeneralized (718 lines) — nothing outside themselves depends
on them anymore; see the note below before deciding whether to upstream these at all.
```

Tracks A and B can run **in parallel** with different reviewers/timing — that's a genuine
scheduling lever, not just an ordering nicety.

## Proposed order

### PR 1 — `PrefixFree` + `Kraft` (Track A, start) — ~253 lines

`PrefixFree.lean` (154) + `Coding/Kraft.lean` (99, `kraft_inequality` /
`kraft_inequality_infinite`). Zero new dependencies beyond the already-merged
`UniquelyDecodable`/`KraftMcMillan` — same "definition, then the named theorem" shape as
#34108, direct continuation of the same series. Lowest-risk PR in the whole plan; propose this
first regardless of what else is in flight.

### PR 2 — `Divergence.Basic` (Track B, start) — ~125 lines

`klFin` (finite KL divergence as a `Finset.sum`, not through measure-theoretic `klDiv`) plus the
mass-free Gibbs bound. Zero local dependencies. This is the highest-leverage single file in the
plan: everything else in Track B needs it, `ChainRule` needs it, and — see the prep-work note
below — `SourceCodingLowerBound` should be refactored to need it too. Independently motivated:
mathlib's own `KullbackLeibler.Basic` has no elementary `Finset.sum` sibling for the finite
case, which is exactly what most users reaching for KL divergence on a finite type actually
want.

### Prep work before PR 3 (not an upstream PR itself — do this locally first)

`SourceCodingLowerBound.lean`'s own `gibbs_sum_log_ratio_nonneg` goes through
`pmfMeasure`/measure-theoretic `klDiv` — heavier machinery than the file needs, and it now
duplicates `Divergence.Basic.klFin_nonneg` (proved elementarily, already generalizes the
measure-theoretic version's hypotheses). Refactor `SourceCodingLowerBound` to route through
`klFin_nonneg` before proposing it upstream: smaller PR, no `MeasureTheory.*` import weight, and
removes an internal duplication a reviewer would otherwise flag immediately (this is exactly the
kind of thing `dupuisf` pushed on in #34108 — "why do you need both of these").

### PR 3 — `SourceCodingLowerBound` (Track A) — ~300 lines after the refactor above

`entropy`, `pmfMeasure` (if still needed after the refactor), `source_coding_lower_bound`
(Shannon's source coding theorem, converse direction). Needs PR 1. High reusability — `entropy`
is the single most obviously-missing definition in `Mathlib.InformationTheory`. Note the file's
own TODO (relax `hp_pos : ∀ i, 0 < p i` to `0 ≤ p i`): worth doing before this PR too, since
`Entropy.ConditionalEntropy` (PR 4) already needed that relaxation for its own Gibbs use and the
technique is proven — inconsistent to upstream the stricter version now and relax it later.

### PR 4 — `Entropy.ConditionalEntropy` + `Entropy.Uniform` (Track A) — ~448 lines

The crown jewel of Track A: marginals, conditional entropy, chain rule, subadditivity, data
processing, relabeling invariance, max-entropy bound, vanishing on deterministic joints, plus
the uniform-law attainment corollary. Fills the largest documented gap outright — needs PR 3
only. At 448 lines this is the biggest "propose as one PR" chunk in the plan; if a reviewer
pushes back on size, it splits cleanly along its own section headers (marginals + condEntropy +
chain rule first, subadditivity + data-processing + max-entropy second) — flag this as the
fallback, don't preemptively split it, since the whole thing is one coherent concept and splitting
it first would just multiply review overhead for no reason.

### PR 5 — `Divergence.Binary` (Track B) — ~273 lines

`klBin`, Gibbs, the sharp-constant (`2`) binary Pinsker inequality via a genuine calculus
argument (second-derivative monotonicity), and the chi-squared upper bound. Zero local
dependencies — could in principle go up right after or even before PR 2, noted here only because
it's the natural lead-in to PR 6. Self-contained and independently citable (binary
hypothesis-testing bounds are standard), but the derivative-monotonicity proof is real analysis
machinery a reviewer will read carefully — budget more review time than the line count alone
suggests.

### PR 6 — `Divergence.Pinsker` (Track B) — ~546 lines

Total variation distance, the finite log-sum inequality, sharp-constant Pinsker, Hellinger
affinity, Bretagnolle-Huber, and the testing corollary. Needs PR 2 and PR 5. This is the largest
single file in the plan and the one most likely to draw a "please split this" request. Recommend
splitting preemptively along the file's own section breaks: `tvDist` + the log-sum engine +
`pinsker` itself as one PR (~300 lines, the headline result), Hellinger + Bretagnolle-Huber +
the testing corollary as a follow-up (~250 lines, builds on the first). Unlike PR 4, do split
this one going in — Pinsker's inequality is independently notable enough to merit its own PR
rather than being bundled with Bretagnolle-Huber, which is a distinct (if related) result.

### PR 7 — `Divergence.ChainRule` (bridge) — ~232 lines

The bridge: KL's chain rule, mirroring `ConditionalEntropy.chain_rule`. Needs PR 4 *and* PR 2 —
first point where the two tracks must have both landed. Natural, small, well-motivated
companion PR once both prerequisites exist.

### PR 8 — the tensorization identity only (Track B tail) — ~325 of `Tensorization.lean`'s 385 lines

`klFin_prod_two`, `productLaw`, `klFin_productLaw`, `klFin_mix_le_chiSq`, `pathBudget`. Needs PR
2 only — **not** PR 6, despite the file importing `Divergence.Pinsker` today. Checked directly:
`miss_add_falseAlarm_ge` (from Pinsker) is referenced exactly once in the file, inside
`detector_miss_of_pathBudget`, and nowhere else — the tensorization content itself is
Pinsker-independent. Split `detector_miss_of_pathBudget` off before proposing this upstream (see
below); the remainder is genuinely general (KL tensorizes over product laws, chi-squared
per-step bounds compose into a path budget) and worth having in mathlib on its own.

## Not recommended for upstreaming

**`detector_miss_of_pathBudget`** (the tail of `Tensorization.lean`, ~60 lines). Explicitly
framed in its own docstring as a "linear-debt/quadratic-information detection fence" — a
named-scenario, game-theoretic corollary, not a general-purpose result. Mathlib doesn't take
applied/scenario-specific theorems; this is exactly the kind of thing that stays in the
downstream `GameTheory` project that this repo already serves. Split it into its own local file
(or leave it where it is) rather than proposing it.

**`Example.lean`** (254 lines, Shannon-Fano worked example). Explicitly a pedagogical
demonstration, not a reusable building block — mathlib has no convention for merging narrative
example files outside `Archive/`, and this doesn't have the historical/expository weight
`Archive` entries usually do. Better used as motivating material *in the PR description* for
`KraftConverse` (PR 12 below) than as merged code.

**`KraftNatural.lean` + `KraftGeneralized.lean`** (408 + 310 = 718 lines, 14% of this repo).
Flagging this prominently because it changes the plan, not just a footnote: dependency-graph
check shows **nothing else in the codebase imports either file** except the root aggregator.
Both predate the merged `KraftMcMillan.lean` and were this project's own routes to the same
theorem (a natural-number counting argument, and an abstract `WeightModel`-over-monoids
generalization) — now that the real `KraftMcMillan.lean` is upstream and `KraftConverse.lean`
doesn't depend on either of these files, they're an orphaned parallel branch, not a load-bearing
part of the architecture. Upstreaming either would put a second proof of a theorem mathlib
already has right next to the first — precisely the "why do we need both" objection from
#34108's own review. Recommend against upstreaming; separately worth asking whether they should
stay in this repo at all (out of scope for an *upstream order* proposal, but flagging since the
dependency check makes it obvious).

### Track C — the converse (can run independently, start anytime after PR 1)

Track C only needs `PrefixFree` (PR 1), so it can start in parallel with Tracks A/B once that
lands. It's the biggest remaining chunk (~1493 lines across five files feeding one theorem) and
needs internal splitting; proposed order:

**PR 9 — `Sum` + `ExtShift`** (94 + 72 = 166 lines). Numeric prefix-sum and sequence-extension
lemmas. Not independently motivated (nobody wants these for their own sake), but small and
genuinely dependency-free, so a fine low-risk warm-up that de-risks the review relationship
before the bigger Track C PRs land.

**PR 10 — `Codeword` + `Helpers`** (297 + 43 = 340 lines). Explicit fixed-width base-`D` digit
encoding, with a clean 4-declaration public API (the file already documents this boundary
itself). Reasonably self-contained — "how do I build an explicit prefix code from an integer" is
a fine standalone question — and doesn't need `Construction.lean`.

**PR 11 — `Construction`** (573 lines, the single largest file in the repo). `kraftNumerator`,
`KraftOrder`, `kraftRank`, the reordering machinery. This is the technical core of the converse
and the hardest to split further — `KraftOrder`/`kraftNumerator`/`kraftRank` all serve one
purpose (reorder indices by length) and don't factor into independently-motivated pieces the way
`Entropy.ConditionalEntropy` did. Flag this as the highest-risk single PR in the entire plan:
573 lines of real-analysis-plus-order-theory is exactly the size where mathlib reviewers ask for
a design discussion before the code, not after. Consider opening a Zulip thread describing the
approach before submitting the PR, rather than leading with the diff.

**PR 12 — `KraftConverse`** (414 lines). The payoff: `exists_code_nat`, `exists_code_fin`,
`exists_code` — the full constructive converse of Kraft's inequality. This is also the result
`YuvalFilmus` explicitly asked for as follow-up work in #34108's review thread, which is
unusually strong pre-existing buy-in for a PR — worth citing in the PR description. Needs PRs
1, 9, 10, 11.

## Summary table

| PR | Content | Lines | Needs | Track |
|---|---|---|---|---|
| 1 | PrefixFree + Kraft | ~253 | merged PR only | A |
| 2 | Divergence.Basic | ~125 | — | B |
| — | *(prep: refactor SourceCodingLowerBound's Gibbs proof to reuse PR 2)* | | | |
| 3 | SourceCodingLowerBound | ~300 | 1, (2) | A |
| 4 | ConditionalEntropy + Uniform | ~448 | 3 | A |
| 5 | Divergence.Binary | ~273 | — | B |
| 6 | Divergence.Pinsker (split in two) | ~546 | 2, 5 | B |
| 7 | Divergence.ChainRule | ~232 | 4, 2 | bridge |
| 8 | Tensorization (minus the fence corollary) | ~325 | 2 | B |
| 9 | Sum + ExtShift | ~166 | 1 | C |
| 10 | Codeword + Helpers | ~340 | 1 | C |
| 11 | Construction | ~573 | 1, 9 | C |
| 12 | KraftConverse | ~414 | 1, 9, 10, 11 | C |

Not proposed: `detector_miss_of_pathBudget` (application-specific), `Example.lean`
(pedagogical), `KraftNatural.lean` + `KraftGeneralized.lean` (orphaned, redundant with the
already-merged `KraftMcMillan.lean`).
