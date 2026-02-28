#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

echo "[check] physics assumptions are defined and registered"

defs_tmp="$(mktemp)"
defs_with_values_tmp="$(mktemp)"
registry_tmp="$(mktemp)"
registry_block_tmp="$(mktemp)"
uses_tmp="$(mktemp)"
trap 'rm -f "$defs_tmp" "$defs_with_values_tmp" "$registry_tmp" "$registry_block_tmp" "$uses_tmp"' EXIT

rg -n --no-filename '^def[[:space:]]+[A-Za-z0-9_]+[[:space:]]*:[[:space:]]*String[[:space:]]*:=' PhysicsLogic/Assumptions.lean \
  | sed -E 's/^[0-9]+:def[[:space:]]+([A-Za-z0-9_]+).*/\1/' \
  | sort -u > "$defs_tmp"

# Keep name/value pairs to detect duplicate id strings.
rg -n --no-filename '^def[[:space:]]+[A-Za-z0-9_]+[[:space:]]*:[[:space:]]*String[[:space:]]*:=[[:space:]]*"[^"]+"' PhysicsLogic/Assumptions.lean \
  | sed -E 's/^[0-9]+:def[[:space:]]+([A-Za-z0-9_]+)[[:space:]]*:[[:space:]]*String[[:space:]]*:=[[:space:]]*"([^"]+)".*/\1\t\2/' \
  | sort -u > "$defs_with_values_tmp"

# Restrict registry extraction to the assumptionRegistry block.
awk '
  /^def assumptionRegistry/ {in_registry = 1}
  in_registry {print}
  in_registry && /^[[:space:]]*\]$/ {exit}
' PhysicsLogic/Assumptions.lean > "$registry_block_tmp"

rg -o --no-filename 'AssumptionId\.[A-Za-z0-9_]+' "$registry_block_tmp" \
  | sed 's/AssumptionId\.//' \
  | sort -u > "$registry_tmp"

rg -o --no-filename 'AssumptionId\.[A-Za-z0-9_]+' PhysicsLogic --glob '*.lean' \
  | sed 's/AssumptionId\.//' \
  | sort -u > "$uses_tmp"

missing_defs="$(comm -23 "$uses_tmp" "$defs_tmp" || true)"
if [[ -n "$missing_defs" ]]; then
  echo "$missing_defs"
  echo "[fail] some AssumptionId references are not defined in PhysicsLogic/Assumptions.lean"
  exit 1
fi

missing_registry="$(comm -23 "$defs_tmp" "$registry_tmp" || true)"
if [[ -n "$missing_registry" ]]; then
  echo "$missing_registry"
  echo "[fail] some defined AssumptionId values are not listed in assumptionRegistry"
  exit 1
fi

duplicate_values="$(cut -f2 "$defs_with_values_tmp" | sort | uniq -d || true)"
if [[ -n "$duplicate_values" ]]; then
  while IFS= read -r value; do
    [[ -z "$value" ]] && continue
    awk -F '\t' -v v="$value" '$2 == v { printf "%s -> \"%s\"\n", $1, $2 }' "$defs_with_values_tmp"
  done <<< "$duplicate_values"
  echo "[fail] duplicate AssumptionId string payloads detected"
  exit 1
fi

duplicate_registry_ids="$(
  rg -o --no-filename 'AssumptionId\.[A-Za-z0-9_]+' "$registry_block_tmp" \
    | sed 's/AssumptionId\.//' \
    | sort \
    | uniq -d || true
)"
if [[ -n "$duplicate_registry_ids" ]]; then
  echo "$duplicate_registry_ids"
  echo "[fail] duplicate AssumptionId entries found in assumptionRegistry"
  exit 1
fi

echo "[ok] physics assumptions are defined and registered"
