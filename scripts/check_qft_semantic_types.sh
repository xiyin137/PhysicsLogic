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

echo "[qft-semantic-check] no scalar-typed residual/equation fields in QFT"
residual_equation_hits="$( {
  rg -n \
    "^[[:space:]]+[A-Za-z_][A-Za-z0-9_']*(Residual|residual|equationResidual|brstTerm|higherBracketTerm)[A-Za-z0-9_']*[[:space:]]*:[[:space:]]*(ℂ|Complex|ℝ|Real)([[:space:]]|$)" \
    PhysicsLogic/QFT --glob '*.lean' || true
  rg -n \
    "^[[:space:]]+[A-Za-z_][A-Za-z0-9_']*(Residual|residual|equationResidual|brstTerm|higherBracketTerm)[A-Za-z0-9_']*[[:space:]]*:[[:space:]].*→[[:space:]]*(ℂ|Complex|ℝ|Real)([[:space:]]|$)" \
    PhysicsLogic/QFT --glob '*.lean' || true
} | sort -u )"
if [[ -n "$residual_equation_hits" ]]; then
  echo "$residual_equation_hits"
  echo "[fail] found scalar-typed residual/equation fields in QFT"
  status=1
else
  echo "[ok] residual/equation fields are non-scalar in QFT"
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

echo "[qft-semantic-check] no scalar-valued Virasoro mode/commutator declaration maps"
virasoro_mode_hits="$(
  {
    rg -n \
      "\([[:space:]]*L[[:space:]]*:[[:space:]]*ℤ[[:space:]]*→[[:space:]]*(ℂ|Complex|ℝ|Real)\)" \
      PhysicsLogic/QFT --glob '*.lean' || true
    rg -n \
      "\([[:space:]]*commutator[[:space:]]*:[[:space:]]*ℤ[[:space:]]*→[[:space:]]*ℤ[[:space:]]*→[[:space:]]*(ℂ|Complex|ℝ|Real)\)" \
      PhysicsLogic/QFT --glob '*.lean' || true
    rg -n \
      "^[[:space:]]+[A-Za-z_][A-Za-z0-9_']*[Mm]ode[[:space:]]*:[[:space:]]*ℤ[[:space:]]*→[[:space:]]*(ℂ|Complex|ℝ|Real)([[:space:]]|$)" \
      PhysicsLogic/QFT --glob '*.lean' || true
  } | sort -u
)"
if [[ -n "$virasoro_mode_hits" ]]; then
  echo "$virasoro_mode_hits"
  echo "[fail] found scalar-valued Virasoro mode/commutator maps in QFT"
  status=1
else
  echo "[ok] no scalar-valued Virasoro mode/commutator maps in QFT"
fi

echo "[qft-semantic-check] no raw scalar-valued mode maps in QFT data structures"
raw_mode_hits="$(rg -n \
  "^[[:space:]]+[A-Za-z_][A-Za-z0-9_']*[Mm]ode[A-Za-z0-9_']*[[:space:]]*:[[:space:]]*.*→[[:space:]]*(ℂ|Complex|ℝ|Real)([[:space:]]|$)" \
  PhysicsLogic/QFT --glob '*.lean' \
  | rg -v "(Eigenvalue|Value|Coefficient|Amplitude)" || true)"
if [[ -n "$raw_mode_hits" ]]; then
  echo "$raw_mode_hits"
  echo "[fail] found scalar-valued raw mode maps in QFT"
  status=1
else
  echo "[ok] no scalar-valued raw mode maps in QFT"
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

echo "[qft-semantic-check] no raw scalar-typed physical scale fields (mass/coupling/radius/tension/energy/momentum/scale/length)"
physical_scale_hits="$(
  rg -n "^[[:space:]]+[A-Za-z_][A-Za-z0-9_']*[[:space:]]*:[[:space:]]*(ℂ|Complex|ℝ|Real)([[:space:]]|$)" \
    PhysicsLogic/QFT --glob '*.lean' \
  | while IFS= read -r line; do
      name="$(printf "%s" "$line" | sed -E "s/^[^:]+:[0-9]+:[[:space:]]*([A-Za-z_][A-Za-z0-9_']*)[[:space:]]*:.*$/\\1/")"
      lower="$(printf "%s" "$name" | tr '[:upper:]' '[:lower:]')"
      if [[ "$lower" == *mass* || "$lower" == *coupling* || "$lower" == *radius* \
            || "$lower" == *tension* || "$lower" == *energy* || "$lower" == *momentum* \
            || "$lower" == *scale* || "$lower" == *length* ]]; then
        printf "%s\n" "$line"
      fi
    done
)"
if [[ -n "$physical_scale_hits" ]]; then
  echo "$physical_scale_hits"
  echo "[fail] found raw scalar-typed physical scale fields in QFT"
  status=1
else
  echo "[ok] no raw scalar-typed physical scale fields in QFT"
fi

exit "$status"
