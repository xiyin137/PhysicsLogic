#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

echo "[critical-dimension-check] no hard-coded critical-dimension definitions in non-Papers modules"

hits="$(
  rg -n --pcre2 \
    "^[[:space:]]*(def|abbrev)[[:space:]]+[A-Za-z_][A-Za-z0-9_']*[Cc]ritical[A-Za-z0-9_']*[Dd]imension[A-Za-z0-9_']*[[:space:]]*(?::[^:=]*)?:=[[:space:]]*\\(?[[:space:]]*[0-9]+([[:space:]]*:[[:space:]]*(Nat|Int|Real|ℕ|ℤ|ℝ))?[[:space:]]*\\)?[[:space:]]*$" \
    PhysicsLogic --glob '*.lean' \
    | rg -v '^PhysicsLogic/Papers/' || true
)"

if [[ -n "$hits" ]]; then
  echo "$hits"
  echo "[fail] found hard-coded critical-dimension definitions"
  exit 1
fi

echo "[ok] no hard-coded critical-dimension definitions"
