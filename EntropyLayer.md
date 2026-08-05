# The enabling layer: finite conditional entropy on top of `entropy`

Requirements note, 2026-08-05. Written from the consumer side: the
`GameTheory` uniform-equilibrium program consumes this repo as a pinned
provisional dependency (`require InformationTheory from git … @ c937feb`,
toolchain and mathlib both `v4.32.2`) and needs exactly the layer described
here to convert three currently-blocked claims from experiment-grade to
theorem-grade. Everything below is finite (`Fintype`), elementary, and — by
direct verification against the pinned mathlib — lands in empty space:
`Mathlib.InformationTheory` contains only `Coding/`, `Hamming`, and
`KullbackLeibler`; `Analysis.SpecialFunctions.Log.NegMulLog` provides the
scalar building block and `BinaryEntropy` only the scalar binary function.
There is no Shannon entropy of a distribution, no conditional entropy, and no
chain rule anywhere in mathlib. The layer is therefore simultaneously the
consumer's unblock and the natural next slice of the mathlib contribution.

## What exists here already

- `entropy (D : ℕ) (p : I → ℝ) : ℝ := (∑ i, Real.negMulLog (p i)) / log D`
  over `{I : Type*} [Fintype I] [Nonempty I]` — base-`D` via nats/`log D`.
- `gibbs_sum_log_ratio_nonneg` (discrete Gibbs / KL nonnegativity) and the
  `pmfMeasure` bridge to mathlib's measure-theoretic `klDiv`.
- `source_coding_lower_bound` as the existing consumer of `entropy`.
- Hypothesis style: per-theorem `(hp : …) (hsum : ∑ i, p i = 1)`, `hD : 1 < D`.

## Prerequisite: the zero-mass discipline

`SourceCodingLowerBound.lean` carries strict positivity `∀ i, 0 < p i` and
its own TODO about relaxing to `0 ≤ p i` with the `negMulLog 0 = 0`
convention. For this layer the relaxation is not optional: marginals and
conditional slices hit zero mass constantly (a deterministic stream has
almost all joint mass at zero), so every definition and lemma below must be
stated with `0 ≤ p i` and total functions with documented junk values
(mathlib style). `Real.negMulLog` already has the right convention; the
division in conditional weights needs the `p₁ i = 0 → term = 0` convention
made explicit at the definition. The discipline's one nontrivial deliverable
is the zero-mass-tolerant Gibbs inequality — stated as item 0 of the core
below, since four of the nine core items consume it and the current
strict-positivity form blocks them.

## Requested API — minimal core

Joint distributions are `p : I × J → ℝ` (with `[Fintype I] [Fintype J]`,
nonneg, sums to 1). All entropies base-`D` with `hD : 1 < D`.

0. **Zero-mass-tolerant Gibbs — step zero, plausibly the hardest single
   piece.** Generalize `gibbs_sum_log_ratio_nonneg` from strict positivity
   on both arguments to: `0 ≤ p`, `0 ≤ q`, `∑ p = 1`, `∑ q ≤ 1`, and
   absolute continuity `∀ i, q i = 0 → p i = 0`, with the junk-value
   conventions carrying the zero terms. Items 2, 3, 4, and 7 all consume
   this; the current strict-positivity form blocks them (item 4 compares
   against the marginal product, which can vanish; item 7 compares `p`
   itself, which can vanish, against uniform). The proof strategies are the
   ones already sketched in `SourceCodingLowerBound.lean`'s own TODO:
   truncate to the support `{i | 0 < p i}` as a finite type, or regularize
   `q` and pass to the limit. Note the a.c. hypothesis is automatically
   satisfied at both internal use sites: against the marginal product
   because `p (i, j) ≤ fst p i` termwise, and against uniform because
   uniform never vanishes.
1. **Marginals.** `fst p : I → ℝ := fun i => ∑ j, p (i, j)` and `snd p`;
   lemmas: nonneg, sums to 1, `fst`/`snd` of a product recover the factors.
2. **Conditional entropy.**
   `condEntropy D p : ℝ := (∑ q ∈ …, negMulLog-form …) / log D` — recommended
   definition directly as the joint sum
   `-∑ (i,j), p (i,j) * logb D (p (i,j) / fst p i)` written via `negMulLog`
   so that zero-mass rows contribute `0` — by the simp-level conventions
   (`negMulLog 0 = 0`, `logb b 0 = 0`, `x / 0 = 0`), not by defeq. Lemmas:
   nonneg; `condEntropy` of a product equals `entropy D (snd p)`.
3. **Chain rule (binary, arbitrary types).**
   `entropy D p = entropy D (fst p) + condEntropy D p`.
   The binary rule at arbitrary `I`, `J` suffices for the consumer: iterated
   forms over tuples follow by induction on the consumer side through the
   equivalence `(Fin (t+1) → A) ≃ (Fin t → A) × A`, provided item 6 holds.
4. **Conditioning reduces entropy / subadditivity.**
   `condEntropy D p ≤ entropy D (snd p)`, equivalently
   `entropy D p ≤ entropy D (fst p) + entropy D (snd p)` — via the Gibbs
   lemma already in this repo.
5. **Data processing, deterministic.** For `f : I → J` and the pushforward
   `push f p : J → ℝ := fun j => ∑ i ∈ {i | f i = j}, p i`:
   `entropy D (push f p) ≤ entropy D p`. The inequality is the need; the
   equality-iff-injective-on-support refinement is optional. Proof route
   from the other items, so no separate machinery is required: the joint of
   `(X, f X)` sits on the graph of `f`, so its entropy is `entropy D p`
   (item 9 + chain rule); swap the two coordinates (a bijection — item 6 as
   stated suffices, no injective widening needed); the chain rule in the
   swapped order gives `entropy D p = entropy D (push f p) + condEntropy`,
   and `condEntropy ≥ 0` (item 8) finishes. Alternatively a direct
   grouping/log-sum argument; either way, state the intended route.
6. **Relabeling invariance.** For `e : I ≃ J`:
   `entropy D (p ∘ e.symm) = entropy D p` (the special case of 5 used
   constantly for tuple reindexing; worth its own `simp`-friendly
   statement). Optional strengthening, nearly free since `negMulLog 0 = 0`:
   invariance under pushforward by any injective `f` (the extra fibers
   carry zero mass and vanish from the sum).
7. **Max-entropy bound.** `entropy D p ≤ Real.logb D (Fintype.card I)`,
   Gibbs against the uniform distribution.
8. **Nonnegativity.** `0 ≤ entropy D p` (needs `p i ≤ 1`, from nonneg + sum
   = 1) and `0 ≤ condEntropy D p`.
9. **Deterministic conditionals.** If the joint is supported on the graph of
   `g : I → J` (i.e. `p (i, j) ≠ 0 → j = g i`), then `condEntropy D p = 0`;
   equivalently `entropy D (jointOfGraph g q) = entropy D q`. This is the
   lemma the seed-budget argument actually pivots on.

## Nice-to-have (not blocking)

- `entropy_eq_zero_iff` (point mass characterization).
- A `PMF` adapter: `entropyPMF D (q : PMF I) := entropy D (fun i => (q i).toReal)`
  with hypothesis-transport lemmas — the consumer's game layer is
  `PMF`-valued throughout, and E55-style uniformity results would then feed
  chain-rule computations without manual `toReal` plumbing.
- Base-change: `entropy D p = entropy D' p * (log D' / log D)`.
- The strict-positivity relaxation of `source_coding_lower_bound` itself
  (the file's existing TODO) — same discipline, same techniques.

## Acceptance tests (the consumer's three statements)

The layer is complete when these are provable downstream; the first is the
primary test and could live here as the API's own worked example:

1. **Seed entropy budget** (upgrades experiment E33; crypto survey §5).
   Seed `S` with law `σ : Seed → ℝ`; deterministic stream `Y t := F t S`.
   Then for every horizon `T`, with `jointLaw T` the pushforward of `σ`
   under `s ↦ (fun t : Fin T => F t s)`:
   `entropy D (jointLaw T) ≤ entropy D σ ≤ Real.logb D (Fintype.card Seed)`,
   uniformly in `T` — items 5 and 7 compose directly. Contrast corollary
   via the chain rule: a stream with i.i.d.-uniform fresh contributions has
   `entropy D (jointLaw T) = T * Real.logb D (Fintype.card G)`.
2. **Entropy production** (physics survey §2). `EP(P, π) :=
   ∑ x, ∑ y, π x * P x y * Real.log ((π x * P x y) / (π y * P y x))`:
   nonneg (Gibbs, both orientations sum to 1), zero iff detailed balance.
   Needs only the zero-mass discipline plus the existing Gibbs lemma;
   listed here because it shares the discipline, not because it needs
   conditional entropy.
3. **Quadratic-fence composition** (already done downstream as the binary
   KL bounds; no new need — listed to bound scope).

## Out of scope, deliberately

Sequential/process-level statements (KL chain rule for kernels, anytime
detection, filtrations) — the next layer, not this one. Measure-theoretic
generality beyond `Fintype` — mathlib's `KullbackLeibler` side can absorb
that later; the consumer needs the finite case only.

## Constraints

Stay on toolchain/mathlib `v4.32.2` (the consumer's pin; bumps are fine if
coordinated — the consumer re-pins by hash). Mathlib naming and style
throughout, since this layer is the strongest part of the upstream case:
it fills a verified gap, arrives with a nontrivial consumer
(`source_coding_lower_bound`) already in place, and the acceptance tests
above give it independent motivation.
