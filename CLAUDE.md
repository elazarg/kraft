# CLAUDE.md

Project-specific guidance for `kraft`. See the parent workspace's `CLAUDE.md` for
general working rules; this file only records things specific to this repository.

## Style

This project is being brought in line with mathlib's own style and structure (see
`Mathlibify.md` for the investigation and phased plan). Before committing any `.lean` change,
run:

```
bash scripts/lint-style.sh
```

It checks line length (100 chars), file length (1500 lines), no `λ`/`$` (prefer `fun`/`<|`),
no unscoped `open Classical`, no stale `open scoped BigOperators`, trailing whitespace, and
copyright headers — the subset of `Mathlib.Tactic.Linter.Style` and `Header` (in the pinned
`.lake/packages/mathlib`) that applies to a downstream project. It must exit 0.

The script also reports `module`-header coverage as an informational count. Per
`Mathlibify.md` Phase 2, this should become a hard gate (edit the script to `fail=1` on any
file missing `module`) once every file has been converted — don't flip it early, or Phase 2's
incremental, rebuild-after-each-file approach breaks.
