#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

status=0

echo "[check] no explicit Lean axiom declarations"
if rg -n "^[[:space:]]*axiom[[:space:]]+" PhysicsLogic --glob '*.lean'; then
  echo "[fail] found axiom declarations"
  status=1
else
  echo "[ok] no axiom declarations"
fi

echo '[check] no non-Papers `True` placeholders in declaration signatures'
true_hits="$(
  {
    rg -n ":[[:space:]]*True([[:space:]]|$)" PhysicsLogic --glob '*.lean' || true
    rg -n "→[[:space:]]*True([[:space:]]|$)" PhysicsLogic --glob '*.lean' || true
  } | rg -v '^PhysicsLogic/Papers/' || true
)"
if [[ -n "$true_hits" ]]; then
  echo "$true_hits"
  echo '[fail] found non-Papers `True` placeholders in declaration signatures'
  status=1
else
  echo '[ok] no non-Papers `True` placeholders in declaration signatures'
fi

echo "[check] no trivially satisfiable existentials in non-Papers modules"
vacuous_exists_hits="$(rg -n "∃[^\n]*,[[:space:]]*True\\b" PhysicsLogic --glob '*.lean' \
  | rg -v '^PhysicsLogic/Papers/' || true)"
if [[ -n "$vacuous_exists_hits" ]]; then
  echo "$vacuous_exists_hits"
  echo "[fail] found vacuous existentials in non-Papers modules"
  status=1
else
  echo "[ok] no vacuous existentials in non-Papers modules"
fi

echo '[check] no exact bare `field : Prop` in non-Papers structures'
bare_prop_hits="$(rg -n "^[[:space:]]+[A-Za-z_][A-Za-z0-9_']*[[:space:]]*:[[:space:]]*Prop([[:space:]]|$)" \
  PhysicsLogic --glob '*.lean' \
  | rg -v '^PhysicsLogic/Papers/' || true)"
if [[ -n "$bare_prop_hits" ]]; then
  echo "$bare_prop_hits"
  echo "[fail] found exact bare Prop fields in non-Papers modules"
  status=1
else
  echo "[ok] no exact bare Prop fields in non-Papers modules"
fi

echo "[check] stringbook appendix imports are complete and reachable"
if ./scripts/check_stringbook_appendix_imports.sh; then
  echo "[ok] appendix import coverage check"
else
  echo "[fail] appendix import coverage check"
  status=1
fi

echo "[check] stringbook note candidate coverage (units + assumptions)"
if ./scripts/check_stringbook_note_coverage.sh; then
  echo "[ok] stringbook note candidate coverage check"
else
  echo "[fail] stringbook note candidate coverage check"
  status=1
fi

echo "[check] string-theory semantic typing guardrails"
if ./scripts/check_string_semantic_types.sh; then
  echo "[ok] string semantic type checks"
else
  echo "[fail] string semantic type checks"
  status=1
fi

echo "[check] qft semantic typing guardrails"
if ./scripts/check_qft_semantic_types.sh; then
  echo "[ok] qft semantic type checks"
else
  echo "[fail] qft semantic type checks"
  status=1
fi

echo "[check] no approximate decimal literals in non-Papers core code"
if ./scripts/check_no_approx_decimals_core.sh; then
  echo "[ok] no approximate decimal literals in non-Papers core code"
else
  echo "[fail] approximate decimal literal check"
  status=1
fi

echo "[check] no hard-coded critical-dimension definitions in non-Papers core code"
if ./scripts/check_no_hardcoded_critical_dimension_defs.sh; then
  echo "[ok] no hard-coded critical-dimension definitions"
else
  echo "[fail] hard-coded critical-dimension definition check"
  status=1
fi

echo "[check] global semantic typing guardrails (non-Papers)"
if ./scripts/check_global_semantic_types.sh; then
  echo "[ok] global semantic typing checks"
else
  echo "[fail] global semantic typing checks"
  status=1
fi

exit "$status"
