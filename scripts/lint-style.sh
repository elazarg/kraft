#!/usr/bin/env bash
# Project-local style linter for kraft, mirroring the subset of mathlib's own style checks
# that matter here — see Mathlib/Tactic/Linter/Style.lean and Header.lean in the pinned
# mathlib (.lake/packages/mathlib) for the canonical definitions and thresholds this copies.
# Part of the "mathlibify" effort (Mathlibify.md): this is what keeps Phases 0-3's cleanup
# from silently drifting back out of style.
#
# Usage: scripts/lint-style.sh   (run from the repo root)

set -uo pipefail

fail=0
files=$(find InformationTheory -name "*.lean" 2>/dev/null; echo Kraft.lean)

for f in $files; do
  [ -f "$f" ] || continue

  # 1. Line length <= 100 chars (Style.lean: longLine)
  while IFS= read -r hit; do
    echo "$hit"
    fail=1
  done < <(awk -v f="$f" 'length > 100 { print f":"FNR": line exceeds 100 characters ("length")" }' "$f")

  # 2. File length <= 1500 lines (Style.lean: longFile)
  lines=$(wc -l < "$f")
  if [ "$lines" -gt 1500 ]; then
    echo "$f: file exceeds 1500 lines ($lines)"
    fail=1
  fi

  # 3. No `λ` syntax (Style.lean: lambdaSyntax) -- `fun` preferred
  if grep -q 'λ' "$f"; then
    echo "$f: uses 'λ', prefer 'fun'"
    fail=1
  fi

  # 4. No `$` pipe syntax (Style.lean: dollarSyntax) -- `<|` preferred
  if grep -qE ' \$( |$)' "$f"; then
    echo "$f: uses '\$', prefer '<|'"
    fail=1
  fi

  # 5. Unscoped `open Classical` / `open scoped Classical` at file level
  #    (matches the openClassical linter's target: must be scoped per-declaration with `in`)
  if grep -qE '^open (scoped )?Classical$' "$f"; then
    echo "$f: unscoped 'open Classical', scope with 'open scoped Classical in' per-declaration"
    fail=1
  fi

  # 6. No stale `open scoped BigOperators` / `open BigOperators` (notation is global)
  if grep -qE '^open (scoped )?BigOperators( |$)' "$f"; then
    echo "$f: stale 'open (scoped) BigOperators', notation is unconditionally available"
    fail=1
  fi

  # 7. No trailing whitespace
  if grep -qE ' +$' "$f"; then
    echo "$f: has trailing whitespace"
    fail=1
  fi

  # 8. Copyright header present (Header.lean, simplified: first line is the comment opener)
  if [ "$(head -1 "$f")" != "/-" ]; then
    echo "$f: missing copyright header"
    fail=1
  fi
done

# 9. `module` header coverage (Mathlibify.md Phase 2, completed): now a hard gate.
total=$(echo "$files" | wc -w)
withmod=$(grep -l '^module' $files 2>/dev/null | wc -l)
if [ "$withmod" -ne "$total" ]; then
  for f in $files; do
    [ -f "$f" ] || continue
    grep -q '^module' "$f" || { echo "$f: missing 'module' header"; fail=1; }
  done
fi
echo "module-header coverage: $withmod/$total files"

if [ "$fail" -ne 0 ]; then
  echo "lint-style: FAILED"
  exit 1
fi
echo "lint-style: OK ($total files checked)"
