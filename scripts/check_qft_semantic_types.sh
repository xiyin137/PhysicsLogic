#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

status=0

echo "[qft-semantic-check] scalar action fields in QFT must be explicitly named"
action_hits="$(
  rg -n "^[[:space:]]+[A-Za-z_][A-Za-z0-9_']*[[:space:]]*:[[:space:]]*(ℂ|Complex|ℝ|Real)([[:space:]]|$)" \
    PhysicsLogic/QFT --glob '*.lean' \
  | while IFS= read -r line; do
      name="$(printf "%s" "$line" | sed -E "s/^[^:]+:[0-9]+:[[:space:]]*([A-Za-z_][A-Za-z0-9_']*)[[:space:]]*:.*$/\\1/")"
      lower="$(printf "%s" "$name" | tr '[:upper:]' '[:lower:]')"
      if [[ "$lower" == *interaction* ]]; then
        continue
      fi
      if [[ "$lower" == *action* ]]; then
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
