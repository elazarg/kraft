# Upstream order

Proposal, 2026-08-05 (revised after proof mining on 2026-08-09).
`UniquelyDecodable.lean`/`KraftMcMillan.lean` are already merged
([#34108](https://github.com/leanprover-community/mathlib4/pull/34108)). This proposes an order
for the rest, scored on the four things a mathlib reviewer actually reacts to — confirmed
against how #34108 itself went (dupuisf and vlad902 pushed on: minimal-necessary imports, no
redundant proofs of the same fact sitting in the library, and PR size — that review ran a full
month, Jan 18 to Feb 17, for ~400 lines with heavy back-and-forth):

- **Dependency** — can't go up before its prerequisites are merged (or bundled with them).
- **Reusability** — does it fill a gap the wider ecosystem recognizes, or is it project-specific
  glue? (`Mathlib.InformationTheory` currently has only `Coding/`, `Hamming`, and
  `KullbackLeibler`, and there is no Shannon entropy anywhere in `Mathlib.Probability` either —
  no Shannon entropy, no conditional entropy, no discrete KL divergence, no Pinsker. That's the
  gap map this plan works against.)
- **Self-containment** — does the chunk have a clear "this is the whole point" narrative on its
  own, or does it only make sense bundled with something else?
- **Size** — smaller, single-concept PRs review faster and build trust for the bigger ones.

## The map

Checked directly against each file's actual `import`/`public import` lines, not inferred from
the docstrings. The remaining code splits into two tracks that don't need each other, one file
that bridges them, one track that's been quietly orphaned, and one accidental cross-track edge
worth removing before proposing anything:

```
Track A (coding theory, needs the merged PR):
  PrefixFree -> Kraft.lean
  Entropy.Basic (new, extracted below) -> SourceCodingLowerBound (shrunk)
                                        -> ConditionalEntropy + Uniform
                                        -> Entropy.PMF adapter
Track B (divergence, needs nothing from A):
  Basic -> Binary -> Pinsker
    |\-------------> Tensorization (partial, see below)
    \--------------> FiniteMeasure (`klFin`/`klDiv` bridge)

Bridge: ChainRule needs ConditionalEntropy (A) AND Basic (B)

Track C (converse, five independent inputs meeting only at the end):
  Sum + ExtShift          -\
  Helpers -> Codeword      \
  Construction             > KraftConverse (also needs PrefixFree from A)
  finite-fiber enumeration/

Orphaned: KraftNatural + KraftGeneralized (733 lines) — nothing outside themselves depends
on them anymore; see the note below before deciding whether to upstream these at all.
```

Corrections to the first draft of this map, verified directly against the files:

- **`Binary.lean` now intentionally depends on `Divergence.Basic`.** The bridge
  `klFin_bernoulli` identifies `klBin` with `klFin` on Bernoulli laws, and `klBin_nonneg` is a
  short corollary of the general finite Gibbs theorem instead of a second proof. This costs one
  dependency edge but gives the two divergence APIs the compatibility lemma a reviewer is
  likely to demand.
- **`Construction.lean` has no local dependencies.** It does not import either `Codeword` or
  `Sum`; numerator arithmetic, sum bounds, extension, codewords, and reordering are parallel
  inputs that meet only in `KraftConverse.lean`.
- **Track C is far less constrained than it looks.** Only `KraftConverse` itself needs
  `IsPrefixFree` (Track A). Every other Track C component can start immediately alongside PR 1
  and PR 2.

## The missing refactor: extract `Entropy.Basic` — done, 2026-08-05

`ConditionalEntropy.lean` and `Uniform.lean` imported all of `SourceCodingLowerBound.lean` — but
checked what they actually used: only `entropy` (previously defined in
`SourceCodingLowerBound.lean`) and the Gibbs lemma. Conditional entropy has no mathematical
dependence on a source-coding theorem; the edge existed purely because `entropy` happened to
live in a coding-theory file. A mathlib reviewer would not accept `entropy` — this plan's own
candidate for "the single most obviously-missing definition" — defined inside
`Coding/SourceCodingLowerBound.lean`. Done, in `InformationTheory/Entropy/Basic.lean`:

- `Entropy/Basic.lean` (~149 lines): `entropy`, `entropy_nonneg` (moved from
  `ConditionalEntropy.lean`), and `gibbs_sum_log_ratio_nonneg_of_ac` (moved from
  `SourceCodingLowerBound.lean`, rerouted through `Divergence.Basic.klFin_nonneg` — see below).
  It also includes the point-mass characterization and base-change theorem. Depends on
  `Divergence.Basic` only, not on any coding-theory file.
- `Entropy/PMF.lean` (~66 lines) is a separate adapter with `PMF.sum_toReal`, `entropyPMF`, and
  its nonnegativity and zero-entropy API, so `Entropy.Basic` does not import the PMF hierarchy.
- `SourceCodingLowerBound.lean` imports `Entropy.Basic` and now holds only generic
  `expectedLength` and `entropy_le_expectedLength`.
- `Divergence/FiniteMeasure.lean` holds `pmfMeasure` and the `klFin`/`klDiv` compatibility
  bridge, with no coding-theory dependency.
- `ConditionalEntropy.lean` and `Uniform.lean` import `Entropy.Basic` instead
  of `SourceCodingLowerBound`.

This decouples `ConditionalEntropy` (the crown jewel) from `SourceCodingLowerBound` entirely —
they're siblings depending on the same small base now, not a chain — and avoids what would
otherwise be a permanent, odd upstream layout: `Mathlib.InformationTheory.Entropy.*` importing
`Mathlib.InformationTheory.Coding.*` for a definition that has nothing to do with codes.

## Prep work before PR 4 — Gibbs reroute and compatibility bridges done

**Reroute the Gibbs proof — done.** `gibbs_sum_log_ratio_nonneg_of_ac` in `Entropy.Basic` is a
thin wrapper around the more general `klFin_nonneg`. The older strictly-positive
`gibbs_sum_log_ratio_nonneg` was removed after the bridge below was added: it was unused and
strictly subsumed by the zero-mass-tolerant theorem.

**The `klFin`/`klDiv` bridge lemma — done, 2026-08-05.** The instinct after the reroute above is
to drop `pmfMeasure` and `integral_llr_pmfMeasure` entirely, now that they're no longer feeding
`gibbs_sum_log_ratio_nonneg_of_ac`. That would have been a mistake: a reviewer will ask how
`klFin` relates to mathlib's existing `InformationTheory.KullbackLeibler.klDiv`, and
`integral_llr_pmfMeasure` was already most of the proof of exactly that compatibility lemma.
Added `toReal_klDiv_pmfMeasure_eq_klFin` (`Divergence/FiniteMeasure.lean`, right after
`integral_llr_pmfMeasure`): for equal-mass nonnegative `p`, `q` satisfying absolute continuity,
`(klDiv (pmfMeasure p) (pmfMeasure q)).toReal = klFin p q`, proved by combining
`pmfMeasure_eq_withDensity`, `toReal_klDiv_of_measure_eq` (mathlib), and
`integral_llr_pmfMeasure`. This turns
"here's a second KL divergence definition" — precisely the "why do you need both" objection this
plan already flags elsewhere — into "here's the finite/elementary API, linked to the
measure-theoretic one you already have."

**The `klBin`/`Real.binEntropy` note — still just a note, correctly.** Checked
`Real.binEntropy`'s actual definition (`Mathlib.Analysis.SpecialFunctions.BinaryEntropy`): it's
the Shannon entropy of a Bernoulli law, `-p log p - (1-p) log(1-p)`, not a divergence — there is
no clean equation directly relating it to `klBin` the way `klFin`/`klDiv` relate (entropy and
KL divergence are different quantities; relating them needs a reference distribution, which
`binEntropy` doesn't take). Confirms the original assessment: this stays a documentation note
for the `Divergence.Binary` PR description ("here's the related mathlib definition, and here's
why it's not the same thing"), not a lemma to force into existence.

## Proposed order

Grouped into waves by what's actually ready to go, not a strict 1-through-13 sequence — several
of these can run in parallel with different reviewers.

### Wave 1 — no dependencies beyond the merged PR

**PR 1 — `PrefixFree` + `Kraft`** (Track A) — ~160 lines. `PrefixFree.lean` (85) +
`Coding/Kraft.lean` (74, `IsPrefixFree.finsetSum_one_div_card_pow_length_le_one` /
`summable_one_div_card_pow_length` / `tsum_one_div_card_pow_length_le_one`). Same
"definition, then the named theorem" shape as #34108, direct continuation of the same series.
Lowest-risk PR in the whole plan.

**PR 2 — `Divergence.Basic`** (Track B) — ~137 lines. The highest-leverage single file in the
plan: `Entropy.Basic`, every other file in Track B, and `ChainRule` all need it.

**PR 3 — `Sum` + `ExtShift`** (Track C) — 82 + 54 = 136 lines. Numeric prefix-sum and
sequence-extension lemmas. Not independently motivated on their own, but small and genuinely
dependency-free — a fine low-risk warm-up that de-risks the review relationship before the
bigger Track C PRs land. (`ExtShift` is used only by `KraftConverse` in the end, so it could
equally well ride along with PR 13 instead — either placement is fine.)

**PR 4 — `Codeword` + `Helpers`** (Track C) — 278 + 42 = 320 lines. Explicit fixed-width base-`D`
digit encoding, with a clean 4-declaration public API the file already documents itself.
Independent of PR 3 — genuinely parallel, not sequential, despite both being "Track C."

**PR 7a — finite-fiber monotone enumeration** (generic order theory) — ~229 lines, no local
dependencies. The public API includes `exists_equiv_nat_monotone_of_finite_fibers` and a wrapper
using mathlib's existing `Northcott` abstraction; the private `KraftOrder`/rank machinery is only
their implementation. Upstream this should be renamed and placed in a general order/countability
file, not presented as coding theory.

**PR 7b — Kraft numerator arithmetic** (Track C) — ~160 lines, no local dependencies.
`kraftNumerator.div_pow_eq_sum` and the positive interval-separation invariant
`kraftNumerator.add_one_mul_pow_le` are the core results. The latter replaced an unused
50-line closed form plus a long negative-only separation proof.

### Wave 2 — one prerequisite each

**PR 2b — `Divergence.FiniteMeasure`** (Track B) — ~134 lines. Needs PR 2. This is the isolated
compatibility layer between elementary `klFin` and mathlib's measure-theoretic `klDiv`; keeping
it separate avoids forcing measure theory on every finite-divergence or source-coding user.

**PR 6 — `Entropy.Basic`** (Track A, new) — ~149 lines, already extracted locally (see above).
Needs PR 2 only. Ships `entropy` itself, which makes this arguably the PR to lead with once PR 2
lands — it's small, it's the plan's own headline gap-filler, and nothing about it is
coding-theory-specific.

**PR 6b — `Entropy.PMF`** (Track A) — ~66 lines. Needs PR 6. This is deliberately separate from
the elementary finite-sum API and supplies the adapter downstream probability developments need.

**PR 5 — `Divergence.Binary`** (Track B) — ~260 lines. Needs PR 2. `klFin_bernoulli` connects
the binary and finite APIs; the file then proves the sharp-constant (`2`) binary Pinsker
inequality via a real second-derivative-monotonicity argument and the chi-squared upper bound.
The derivative proof is real analysis a reviewer will read carefully; budget more review time
than the line count suggests.

**PR 8 — `Divergence.Pinsker`** (Track B) — 546 lines, split in two. Needs PR 2 and PR 5. Largest
file in the plan and the one most likely to draw a "please split this" request — split
preemptively along the file's own section breaks: `tvDist` + the log-sum engine + `pinsker`
itself first (~300 lines, the headline result), Hellinger + Bretagnolle-Huber + the testing
corollary as a follow-up (~250 lines). Unlike `ConditionalEntropy` below, split this one going
in — Pinsker's inequality is independently notable enough to merit its own PR rather than being
bundled with Bretagnolle-Huber.

**PR 9 — Tensorization identity only** (Track B) — ~325 of `Tensorization.lean`'s 385 lines:
`klFin_prod_two`, `productLaw`, `klFin_productLaw`, `klFin_mix_le_chiSq`, `pathBudget`. Needs PR
2 only — **not** Pinsker, despite the file importing it today. Checked directly:
`miss_add_falseAlarm_ge` (from Pinsker) is referenced exactly once in the file, at line 377,
inside `detector_miss_of_pathBudget`, and nowhere else — the tensorization content itself is
Pinsker-independent. Split `detector_miss_of_pathBudget` off first (see "not recommended"
below); the remainder is genuinely general and worth having on its own.

### Wave 3 — two prerequisites

**PR 10 — `SourceCodingLowerBound`, shrunk** (Track A) — ~174 lines after the extraction
(`expectedLength`, `entropy_le_expectedLength`). Needs PR 1 and PR 6. The theorem now assumes only
`0 ≤ p i`: the normalized Kraft weights are strictly positive, so the zero-mass-tolerant Gibbs
lemma from `Entropy.Basic` handles vanishing source probabilities directly.

**PR 11 — `ConditionalEntropy` + `Uniform`** (Track A) — ~448 lines. Needs PR 6 *only* — after
the extraction, this no longer waits on PR 10 at all, which is the main scheduling win of the
refactor above. Marginals, conditional entropy, chain rule, subadditivity, data processing,
relabeling invariance, max-entropy bound, vanishing on deterministic joints, plus the
uniform-law attainment corollary. Fills the largest documented gap outright. At 448 lines this
is the biggest "propose as one PR" chunk in the plan; if a reviewer pushes back on size, it
splits cleanly along its own section headers (marginals + condEntropy + chain rule first,
subadditivity + data-processing + max-entropy second) — flag this as the fallback, don't
preemptively split it, since the whole thing is one coherent concept.

**PR 12 — `Divergence.ChainRule`** (bridge) — 232 lines. Needs PR 11 *and* PR 2 — first point
where Tracks A and B both have to have landed. Small, well-motivated companion PR mirroring
`entropy_chain_rule` once both prerequisites exist.

### Wave 4 — the payoff

**PR 13 — `KraftConverse`** (Track C) — 414 lines. `exists_code_nat`, `exists_code_fin`,
`exists_code` — the full constructive converse of Kraft's inequality. Needs PR 1, PR 3, PR 4,
and PR 7. This is also the result `YuvalFilmus` explicitly asked for as follow-up work in
#34108's own review thread — unusually strong pre-existing buy-in, worth citing in the PR
description.

## Not recommended for upstreaming

**`detector_miss_of_pathBudget`** (the tail of `Tensorization.lean`, ~60 lines). Explicitly
framed in its own docstring as a "linear-debt/quadratic-information detection fence" — a
named-scenario, game-theoretic corollary, not a general-purpose result. Mathlib doesn't take
applied/scenario-specific theorems; this is exactly the kind of thing that stays in the
downstream `GameTheory` project this repo already serves. Split it into its own local file (or
leave it where it is) rather than proposing it.

**`Example.lean`** (254 lines, Shannon-Fano worked example). Explicitly a pedagogical
demonstration, not a reusable building block — mathlib has no convention for merging narrative
example files outside `Archive/`, and this doesn't have the historical/expository weight
`Archive` entries usually do. Better used as motivating material *in the PR description* for
`KraftConverse` (PR 13) than as merged code.

**`KraftNatural.lean` + `KraftGeneralized.lean`** (416 + 317 = 733 lines, ~14% of this repo).
Flagging this prominently because it changes the plan, not just a footnote: dependency-graph
check shows **nothing else in the codebase imports either file** except the root aggregator.
Both predate the merged `KraftMcMillan.lean` and were this project's own routes to the same
theorem (a natural-number counting argument, and an abstract `WeightModel`-over-monoids
generalization) — now that the real `KraftMcMillan.lean` is upstream and `KraftConverse.lean`
doesn't depend on either of these files, they're an orphaned parallel branch, not a load-bearing
part of the architecture. Upstreaming either would put a second proof of a theorem mathlib
already has right next to the first — precisely the "why do we need both" objection from
#34108's own review. Recommend against upstreaming; each file's own docstring now records that
they're kept locally on purpose (see the note added there), not because upstreaming was
overlooked.

## Summary table

| PR | Content | Lines | Needs | Track | Wave |
|---|---|---|---|---|---|
| 1 | PrefixFree + Kraft | ~160 | merged PR only | A | 1 |
| 2 | Divergence.Basic | ~137 | — | B | 1 |
| 2b | Divergence.FiniteMeasure | ~134 | 2 | B | 2 |
| 3 | Sum + ExtShift | ~136 | — | C | 1 |
| 4 | Codeword + Helpers | ~320 | — | C | 1 |
| 5 | Divergence.Binary | ~260 | 2 | B | 2 |
| 6 | Entropy.Basic (extracted, done locally) | ~149 | 2 | A | 2 |
| 6b | Entropy.PMF | ~66 | 6 | A | 2 |
| 7a | Finite-fiber monotone enumeration | ~229 | — | generic | 1 |
| 7b | Kraft numerator arithmetic | ~160 | — | C | 1 |
| 8 | Divergence.Pinsker (split in two) | ~546 | 2, 5 | B | 2 |
| 9 | Tensorization (minus the fence corollary) | ~325 | 2 | B | 2 |
| 10 | SourceCodingLowerBound, shrunk | ~174 | 1, 6 | A | 3 |
| 11 | ConditionalEntropy + Uniform | ~448 | 6 | A | 3 |
| 12 | Divergence.ChainRule | ~232 | 11, 2 | bridge | 3 |
| 13 | KraftConverse | ~398 | 1, 3, 4, 7a, 7b | C | 4 |

Not proposed: `detector_miss_of_pathBudget` (application-specific), `Example.lean`
(pedagogical), `KraftNatural.lean` + `KraftGeneralized.lean` (orphaned, redundant with the
already-merged `KraftMcMillan.lean`).
