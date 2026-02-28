#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

echo "[check] no raw string literal ids in non-Papers PhysicsAssumption uses"

raw_id_hits="$(
  rg -n '(PhysicsLogic\.)?PhysicsAssumption[[:space:]]*"' PhysicsLogic --glob '*.lean' \
    | rg -v '^PhysicsLogic/Papers/' || true
)"

if [[ -n "$raw_id_hits" ]]; then
  echo "$raw_id_hits"
  echo "[fail] found raw string literal PhysicsAssumption ids in non-Papers modules"
  echo "[hint] use AssumptionId.* constants from PhysicsLogic/Assumptions.lean"
  exit 1
fi

echo "[ok] no raw string literal ids in non-Papers PhysicsAssumption uses"
