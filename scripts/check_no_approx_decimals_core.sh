#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

echo "[check] no approximate decimal literals in non-Papers core code"

# Guardrail: block decimal approximations in executable/core statements.
# We scope to non-Papers modules and filter out comment/doc-comment lines.
hits="$(
  rg -n -g '*.lean' -g '!PhysicsLogic/Papers/**' \
    '(=|≤|≥|<|>|\+|-|\*|/|\(|,|:)[[:space:]]*[0-9]+\.[0-9]+' PhysicsLogic \
  | rg -v '/--|--|/-!' || true
)"

if [[ -n "$hits" ]]; then
  echo "$hits"
  echo "[fail] found approximate decimal literals in non-Papers core code"
  echo "[hint] use exact symbolic forms (e.g. 33/2, 1 - 1/sqrt(2)) or parameter fields"
  exit 1
fi

echo "[ok] no approximate decimal literals in non-Papers core code"
