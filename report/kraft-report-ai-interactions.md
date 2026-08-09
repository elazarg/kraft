# AI Interactions — Source Notes

Concrete observations from git history, the deleted `old/kraft_aristotle.lean`, and the Mathlib / Lean PR discussions. Used as raw material for §4 ("AI interaction") of the report.

---

## Who was used, and how much

- **ChatGPT (GPT-5.2 era)** — primary assistant throughout the project. Most of the day-to-day proof drafting, refactoring suggestions, and "can this be shorter" iterations went through it.
- **Gemini 3** — used opportunistically as a second opinion, especially when ChatGPT got stuck. Sometimes agreed with ChatGPT in a way that turned out to be wrong (see Aristotle episode below).
- **Aristotle (Harmonic)** — used for one critical step: producing a Lean proof of Kraft's inequality and the auxiliary "subset-sum equals 1" lemma. Not used for day-to-day work; invoked when the other two agents kept going in circles.
- **Coding agent (Claude Code or similar)** — essentially **not used**, except possibly a small amount of polish near the very end. The prior draft of the report overstated this; correct.

(Acknowledgments line in README currently lists all three assistants; this is accurate, but the relative weights are very uneven — ChatGPT did most, Gemini a distant second, Aristotle one decisive contribution.)

---

## The Aristotle episode (worth a named anecdote in the report)

**Timeline.**

- **2025-12-09 → 2026-01-07:** Student works on the converse (the hardest part), building `Theorem 3.1` and `Theorem 3.2` from `kraft.tex`. Commits: `972397e` ("Theorem 3.1 complete"), `58c22f4` ("Theorem 3.2 done").
- **2026-01-08:** Stuck on the auxiliary "find a prefix whose sum is exactly 1" lemma. ChatGPT and Gemini both propose an approach; both agree Aristotle's alternative proof is the wrong direction and should be discarded.
- **2026-01-08 `1208162`:** Student commits Aristotle's proof anyway — 612 lines — under `Kraft/kraft_aristotle.lean`, titled *"aristotle, but cleaned and readable"*.
- **2026-01-08 `a8ee271`:** *"more kraft_aristotle"* — +202 −49. The proof is being filled in. It was "almost ready" — the remaining gaps were small, contrary to the other agents' assessment.
- **2026-01-08 `16e37f6`:** *"almost all sorrys removed"* — later the same day.
- **2026-01-08 `165bee2`:** *"kraft_inequality_tight"* — the converse is closed.
- **2026-01-13 `5ccba45`:** *"remove old/"* — the 819-line Aristotle file (moved to `old/` at some point) is deleted. By then the main library has absorbed what was learned and the raw Aristotle file is no longer needed.

**What was in the Aristotle file** (reconstructed from the deletion diff):

- `kraft_inequality` proved directly for `List Bool` via the disjoint-cylinder argument (the "counting" proof from `kraft.tex`, Theorem 1).
- `pairwise_monotone`: a utility lemma.
- `exists_prefix_sum_eq_one_of_sorted`: this is the key one — the constructive subset-sum lemma underpinning the converse. Uses `Nat.find` to locate the minimal prefix whose sum exceeds 1, then algebraic manipulation to show equality. It is **the lemma the other agents said wouldn't work**, and it is the lemma that, in generalized form, survives as `exists_prefix_sum_eq_one_of_sorted` in the current codebase (commit `53b24d7`: "generalize exists_prefix_sum_eq_one_of_sorted").

**Lesson.** The two most widely used assistants jointly dismissed a proof that was almost complete. Don't take "both models agree this is wrong" as authoritative — check it by trying to close the goals. In this case the "dismissed" proof became the foundation of the converse.

---

## Concrete patterns observed during the project

### Where the AI-drafted work held up well

- **Bookkeeping-heavy algebraic manipulation.** Rearranging `(∑ μ x)^r = ∑ ∏ μ(w i) = ∑ μ(prodTuple w)` (`KraftGeneralized.lean:80–91`); rewriting `D^(N-c) · (D^N)⁻¹ = (D⁻¹)^c` (`KraftGeneralized.lean:93–116`). Tedious but mechanical; AI drafts were usually right after 1–2 revisions.
- **Golfing passes.** Many commits titled "simpler", "golfer", "simpler still" (`909e419`, `6e08ac3`, `0fae010`) came from "can this be shorter".
- **Naming suggestions** — `WeightModel`, `ExpBounded`, `prodTuple`, `kraftNumerator`, `kraftCodeword`. All survived review.
- **Transport and plumbing.** The finite↔infinite case split in `exists_code` and `transport_code` (alphabet lift) were assembled mostly from AI-drafted pieces.

### Where the AI-drafted work was unreliable

- **Hallucinated lemma names.** Pervasive. Any `exact Mathlib.Foo.bar_of_baz`-style suggestion had to be grep-verified before compiling. The discipline that emerged: search (`grep`, loogle, leansearch) *before* believing a name exists.
- **Over-reliance on closing tactics.** `grind`, `simp_all`, `aesop` routinely closed goals that then silently broke on Mathlib bumps. The git log shows the full cleanup arc:
  - `aee5a3d`, `0d1df02`, `cc6779c`, `eb920e4` — all titled *"grind--"* (grind being removed).
  - `1bb4829` — *"Finish all theorems, organize, remove brittle grind"*.
  - `f20c1dd` — *"no grind"*.
  - `199c631`, `f063ddb`, `4f766ca` — `simp_all` → `simp_all only`.
  - `eb44360` — *"no aesop"*.
  - `fd392b2`, `062c26d`, `900f8e3` — removing `generalize_proofs` because anonymous proof terms leak and break on refactor.
- **Premature abstraction.** Early AI drafts tried to land directly in monoid-level statements. It didn't work. The productive order was: concrete binary proof first, then identify the 2–3 structural lemmas actually used, then generalize. The monoid / `ℝ≥0` layering (`9722f44`, `c69e809`, `c8727a6`) was done **after** the concrete list proof was green.
- **Joint dismissal of a correct proof.** The Aristotle episode above.

### Review feedback (external, post-facto)

The Mathlib PR review (#34108) was the first time the code met non-AI reviewers. Interesting signals:

- Style review from **vlad902** ("not a maintainer, focusing on style"): multiple rounds of golf/indentation. Representative comment, referring to an earlier draft over sets of lists:
  > *"This looks a lot better with `Fin r → List α`!"*
  — the AI-suggested reformulation (cast up front to `Fin r → S`) was the right move.
- `dupuisf` (maintainer, merged it): *"It's starting to look very good!"* after the third round. Routine back-and-forth on calc-block indentation and inlining types.
- `YuvalFilmus` suggested two TODOs for follow-up: infinite Kraft–McMillan, and the full converse (both of which are in fact proved in the local project but were not upstreamed in this PR).
- Process: merged via Bors (`dupuisf`, `sgouezel` both `bors r+`). No mathematical revisions — style only.

**Takeaway:** the AI-assisted proofs survived human review with only stylistic changes. The mathematical content was correct on first submission. This is a data point for "AI-assisted Lean formalization can pass mathlib review" — with the caveats above about automation brittleness.

### Lean 4 PR #12108

Much smaller (+8 lines, `prefix_map_iff_of_injective` / `suffix_map_iff_of_injective`). CI nitpicks only, no substantive review; approved by `Rob23oba` and merged. Noted here only because the lemma was extracted in the course of the converse proof — a good example of "upstream the small utility as you find it".

---

## Headline points for the report

1. Primary assistant was **ChatGPT**, with **Gemini** as occasional second opinion and **Aristotle** as one decisive contribution. A coding agent was not a meaningful part of the workflow.
2. The Aristotle episode — "both mainstream models agreed the proof was worthless; it was almost ready" — is the single most instructive AI-interaction lesson from the project.
3. The git log's own language (`grind--`, `no aesop`, `no simp_all`, `no generalize_proofs`) is the honest record of which automation shortcuts had to be walked back.
4. External Mathlib review treated the code as unremarkable — style fixes only, no math bugs — which is itself a useful signal about the state of AI-assisted Lean formalization as of early 2026.

---

## Repo URL (confirmed)

- `https://github.com/elazarg/kraft` (from `git remote -v`).

Used in report links.
