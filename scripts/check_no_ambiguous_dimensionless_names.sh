#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

echo "[dimensionless-naming-check] no banned ambiguous dimensionless field names in non-Papers modules"

hits="$(
  rg -n --pcre2 \
    "^[[:space:]]+[A-Za-z_][A-Za-z0-9_']*(turningPointEnergy|shortStringEnergyAtPole|spacetimeEnergy|spacetimeAngularMomentum|cylinderLength|spatialLength|globalAdSEnergy)[A-Za-z0-9_']*[[:space:]]*:" \
    PhysicsLogic --glob '*.lean' \
    | rg -v '^PhysicsLogic/Papers/' || true
)"

if [[ -n "$hits" ]]; then
  echo "$hits"
  echo "[fail] found ambiguous dimensionless field names in non-Papers modules"
  exit 1
fi

echo "[ok] no banned ambiguous dimensionless field names"
