#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

status=0

echo "[qft-semantic-check] no scalar-typed state fields in QFT data structures"
state_hits="$(rg -n \
  "^[[:space:]]+[A-Za-z_][A-Za-z0-9_']*[Ss]tate[[:space:]]*:[[:space:]]*(ℂ|Complex|ℝ|Real)([[:space:]]|$)" \
  PhysicsLogic/QFT --glob '*.lean' || true)"
if [[ -n "$state_hits" ]]; then
  echo "$state_hits"
  echo "[fail] found scalar-typed state fields in QFT"
  status=1
else
  echo "[ok] no scalar-typed state fields in QFT"
fi

echo "[qft-semantic-check] no scalar-typed operator fields in QFT data structures"
operator_hits="$(rg -n \
  "^[[:space:]]+[A-Za-z_][A-Za-z0-9_']*[Oo]perator[[:space:]]*:[[:space:]]*(ℂ|Complex|ℝ|Real)([[:space:]]|$)" \
  PhysicsLogic/QFT --glob '*.lean' || true)"
if [[ -n "$operator_hits" ]]; then
  echo "$operator_hits"
  echo "[fail] found scalar-typed operator fields in QFT"
  status=1
else
  echo "[ok] no scalar-typed operator fields in QFT"
fi

echo "[qft-semantic-check] no scalar-typed fields ending in Functional in QFT"
functional_hits="$(rg -n \
  "^[[:space:]]+[A-Za-z_][A-Za-z0-9_']*[Ff]unctional[[:space:]]*:[[:space:]]*(ℂ|Complex|ℝ|Real)([[:space:]]|$)" \
  PhysicsLogic/QFT --glob '*.lean' || true)"
if [[ -n "$functional_hits" ]]; then
  echo "$functional_hits"
  echo "[fail] found scalar-typed Functional fields in QFT"
  status=1
else
  echo "[ok] no scalar-typed Functional fields in QFT"
fi

echo "[qft-semantic-check] ActionFunctional domains must be configuration spaces (not ℝ/ℂ)"
action_functional_domain_hits="$(rg -n \
  "^[[:space:]]+[A-Za-z_][A-Za-z0-9_']*[Aa]ction[Ff]unctional[[:space:]]*:[[:space:]]*(ℂ|Complex|ℝ|Real)[[:space:]]*→" \
  PhysicsLogic/QFT --glob '*.lean' || true)"
if [[ -n "$action_functional_domain_hits" ]]; then
  echo "$action_functional_domain_hits"
  echo "[fail] found ActionFunctional fields with scalar domains in QFT"
  status=1
else
  echo "[ok] ActionFunctional domains are non-scalar in QFT"
fi

echo "[qft-semantic-check] scalar action fields in QFT must be explicitly named"
action_hits="$(
  rg -n "^[[:space:]]+[A-Za-z_][A-Za-z0-9_']*[[:space:]]*:[[:space:]]*(ℂ|Complex|ℝ|Real)([[:space:]]|$)" \
    PhysicsLogic/QFT --glob '*.lean' \
  | while IFS= read -r line; do
      name="$(printf "%s" "$line" | sed -E "s/^[^:]+:[0-9]+:[[:space:]]*([A-Za-z_][A-Za-z0-9_']*)[[:space:]]*:.*$/\\1/")"
      lower="$(printf "%s" "$name" | tr '[:upper:]' '[:lower:]')"
      if [[ "$name" =~ (^action|_action|Action) ]]; then
        if [[ "$lower" != *actionvalue* && "$lower" != *action_value* \
              && "$lower" != *actionscale* && "$lower" != *action_scale* \
              && "$lower" != *actiondifference* && "$lower" != *action_difference* \
              && "$lower" != *actionvariation* && "$lower" != *action_variation* \
              && "$lower" != *actionbound* && "$lower" != *action_bound* \
              && "$lower" != *actioncontraction* && "$lower" != *action_contraction* ]]; then
          printf "%s\n" "$line"
        fi
      fi
    done
)"

if [[ -n "$action_hits" ]]; then
  echo "$action_hits"
  echo "[fail] found ambiguous scalar action fields in QFT"
  status=1
else
  echo "[ok] scalar action fields in QFT are explicit"
fi

exit "$status"
