#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

units_tmp="$(mktemp)"
missing_units_tmp="$(mktemp)"
assumptions_tmp="$(mktemp)"
missing_assumptions_tmp="$(mktemp)"
trap 'rm -f "$units_tmp" "$missing_units_tmp" "$assumptions_tmp" "$missing_assumptions_tmp"' EXIT

echo "[note-coverage] collecting candidate formalization units from stringbook notes..."
for f in docs/stringbook/notes/appendix-*.md docs/stringbook/notes/section-*.md; do
  awk '/## Candidate Formalization Units/{flag=1;next}/## Assumption Candidates/{flag=0}flag' "$f" \
    | rg -o '`[A-Z][A-Za-z0-9]*`' \
    | tr -d '`' || true
done | sort -u > "$units_tmp"

while IFS= read -r unit; do
  [[ -z "$unit" ]] && continue
  if ! rg -q "\\b${unit}\\b" PhysicsLogic; then
    echo "$unit" >> "$missing_units_tmp"
  fi
done < "$units_tmp"

echo "[note-coverage] collecting candidate assumption ids from stringbook notes..."
for f in docs/stringbook/notes/appendix-*.md docs/stringbook/notes/section-*.md; do
  awk '/## Assumption Candidates/{flag=1;next}/## Subsections/{flag=0}flag' "$f" \
    | rg -o '`[a-z][A-Za-z0-9_]*`' \
    | tr -d '`' || true
done | rg -v '^(assumptionRegistry)$' | sort -u > "$assumptions_tmp"

while IFS= read -r assumption_id; do
  [[ -z "$assumption_id" ]] && continue
  if ! rg -q "^def[[:space:]]+${assumption_id}[[:space:]]*:[[:space:]]*String" PhysicsLogic/Assumptions.lean; then
    echo "$assumption_id" >> "$missing_assumptions_tmp"
  fi
done < "$assumptions_tmp"

missing=0
unit_total="$(wc -l < "$units_tmp" | tr -d '[:space:]')"
assumption_total="$(wc -l < "$assumptions_tmp" | tr -d '[:space:]')"

if [[ -s "$missing_units_tmp" ]]; then
  echo "[note-coverage][fail] missing formalization-unit identifiers in PhysicsLogic:"
  sed 's/^/  - /' "$missing_units_tmp"
  missing=1
fi

if [[ -s "$missing_assumptions_tmp" ]]; then
  echo "[note-coverage][fail] missing assumption ids in PhysicsLogic/Assumptions.lean:"
  sed 's/^/  - /' "$missing_assumptions_tmp"
  missing=1
fi

if [[ "$missing" -eq 0 ]]; then
  echo "[note-coverage] OK (${unit_total} unit ids, ${assumption_total} assumption ids covered)"
fi

exit "$missing"
