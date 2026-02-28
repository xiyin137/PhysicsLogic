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
vacuous_exists_hits="$(rg -n "∃[[:space:]]*\\([^)]*\\),[[:space:]]*True\\b" PhysicsLogic --glob '*.lean' \
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

exit "$status"
