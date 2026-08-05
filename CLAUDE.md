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
no unscoped `open Classical`, no stale `open scoped BigOperators`, trailing whitespace,
copyright headers, and (as of Phase 2 completing) that every file has a `module` header — the
subset of `Mathlib.Tactic.Linter.Style` and `Header` (in the pinned `.lake/packages/mathlib`)
that applies to a downstream project. It must exit 0.

New files must use `module` + `public import`/`import` (classified by whether the import is
needed in a *public* declaration's signature, not just used anywhere in the file — see
Mathlibify.md's Phase 2 notes for the reasoning and a couple of cases that don't work how they
first look) + either `@[expose] public section` (file is mostly-public) or per-declaration
`public def`/`public theorem` (file is mostly-private, mirroring the upstreamed
`KraftMcMillan.lean` precedent).
