#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

status=0

extract_name() {
  sed -E "s/^[^:]+:[0-9]+:[[:space:]]*([A-Za-z_][A-Za-z0-9_']*)[[:space:]]*:.*$/\\1/"
}

is_physical_keyword_name() {
  local name="$1"
  local lower
  lower="$(printf "%s" "$name" | tr '[:upper:]' '[:lower:]')"
  [[ "$lower" == *mass* || "$lower" == *coupling* || "$lower" == *radius* || \
     "$lower" == *tension* || "$lower" == *energy* || "$lower" == *momentum* || \
     "$lower" == *scale* || "$lower" == *length* || "$lower" == *frequency* || \
     "$lower" == *action* || "$lower" == *state* || "$lower" == *operator* || \
     "$lower" == *functional* || "$lower" == *theta* || "$lower" == *angle* ]]
}

echo "[global-semantic-check] no raw scalar-typed physical fields in non-Papers modules"
raw_scalar_hits="$(
  rg -n "^[[:space:]]+[A-Za-z_][A-Za-z0-9_']*[[:space:]]*:[[:space:]]*(ℂ|Complex|ℝ|Real)([[:space:]]|$)" \
    PhysicsLogic --glob '*.lean' \
  | rg -v '^PhysicsLogic/Papers/' \
  | while IFS= read -r line; do
      name="$(printf "%s" "$line" | extract_name)"
      if is_physical_keyword_name "$name"; then
        printf "%s\n" "$line"
      fi
    done
)"
if [[ -n "$raw_scalar_hits" ]]; then
  echo "$raw_scalar_hits"
  echo "[fail] found raw scalar-typed physical fields in non-Papers modules"
  status=1
else
  echo "[ok] no raw scalar-typed physical fields in non-Papers modules"
fi

echo "[global-semantic-check] no raw scalar-domain physical maps in non-Papers modules"
raw_scalar_domain_hits="$(
  rg -n "^[[:space:]]+[A-Za-z_][A-Za-z0-9_']*[[:space:]]*:[[:space:]]*(ℂ|Complex|ℝ|Real)[[:space:]]*→" \
    PhysicsLogic --glob '*.lean' \
  | rg -v '^PhysicsLogic/Papers/' \
  | while IFS= read -r line; do
      name="$(printf "%s" "$line" | extract_name)"
      if is_physical_keyword_name "$name"; then
        printf "%s\n" "$line"
      fi
    done
)"
if [[ -n "$raw_scalar_domain_hits" ]]; then
  echo "$raw_scalar_domain_hits"
  echo "[fail] found raw scalar-domain physical maps in non-Papers modules"
  status=1
else
  echo "[ok] no raw scalar-domain physical maps in non-Papers modules"
fi

echo "[global-semantic-check] no raw scalar-codomain action/functionals in non-Papers modules"
raw_scalar_action_codomain_hits="$(
  rg -n "^[[:space:]]+[A-Za-z_][A-Za-z0-9_']*[[:space:]]*:[[:space:]].*→[[:space:]]*(ℂ|Complex|ℝ|Real)[[:space:]]*$" \
    PhysicsLogic --glob '*.lean' \
  | rg -v '^PhysicsLogic/Papers/' \
  | while IFS= read -r line; do
      name="$(printf "%s" "$line" | extract_name)"
      lower="$(printf "%s" "$name" | tr '[:upper:]' '[:lower:]')"
      if [[ "$lower" == *actionfunctional* || "$lower" == *action*functional* || "$lower" == *lagrangianfunctional* ]]; then
        printf "%s\n" "$line"
      fi
    done
)"
if [[ -n "$raw_scalar_action_codomain_hits" ]]; then
  echo "$raw_scalar_action_codomain_hits"
  echo "[fail] found raw scalar-codomain action/functionals in non-Papers modules"
  status=1
else
  echo "[ok] no raw scalar-codomain action/functionals in non-Papers modules"
fi

echo "[global-semantic-check] ActionFunctional fields use explicit functional structures"
raw_action_functional_arrow_hits="$(
  rg -n "^[[:space:]]+[A-Za-z_][A-Za-z0-9_']*[Aa]ction[Ff]unctional[[:space:]]*:[[:space:]].*→" \
    PhysicsLogic --glob '*.lean' \
  | rg -v '^PhysicsLogic/Papers/' || true
)"
if [[ -n "$raw_action_functional_arrow_hits" ]]; then
  echo "$raw_action_functional_arrow_hits"
  echo "[fail] found raw arrow-typed ActionFunctional fields in non-Papers modules"
  status=1
else
  echo "[ok] ActionFunctional fields are explicit functional structures in non-Papers modules"
fi

echo "[global-semantic-check] no raw scalar-codomain action maps in non-Papers modules"
raw_scalar_action_map_hits="$(
  rg -n "^[[:space:]]+[A-Za-z_][A-Za-z0-9_']*[[:space:]]*:[[:space:]].*→[[:space:]]*(ℂ|Complex|ℝ|Real)[[:space:]]*$" \
    PhysicsLogic --glob '*.lean' \
  | rg -v '^PhysicsLogic/Papers/' \
  | while IFS= read -r line; do
      name="$(printf "%s" "$line" | extract_name)"
      lower="$(printf "%s" "$name" | tr '[:upper:]' '[:lower:]')"
      if [[ "$lower" == *action* ]]; then
        if [[ "$lower" == *value* || "$lower" == *scale* || "$lower" == *difference* || \
              "$lower" == *variation* || "$lower" == *bound* || "$lower" == *contraction* || \
              "$lower" == *coefficient* || "$lower" == *amplitude* || "$lower" == *ratio* ]]; then
          continue
        fi
        printf "%s\n" "$line"
      fi
    done
)"
if [[ -n "$raw_scalar_action_map_hits" ]]; then
  echo "$raw_scalar_action_map_hits"
  echo "[fail] found raw scalar-codomain action maps in non-Papers modules"
  status=1
else
  echo "[ok] no raw scalar-codomain action maps in non-Papers modules"
fi

echo "[global-semantic-check] no raw scalar base scale aliases in non-Papers modules"
raw_scale_alias_hits="$(
  rg -n "^[[:space:]]*(abbrev|def)[[:space:]]+Scale[[:space:]]*:=[[:space:]]*(ℝ|Real)" \
    PhysicsLogic --glob '*.lean' \
  | rg -v '^PhysicsLogic/Papers/' || true
)"
if [[ -n "$raw_scale_alias_hits" ]]; then
  echo "$raw_scale_alias_hits"
  echo "[fail] found raw scalar base scale aliases in non-Papers modules"
  status=1
else
  echo "[ok] no raw scalar base scale aliases in non-Papers modules"
fi

exit "$status"
