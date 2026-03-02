#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

status=0

echo "[semantic-check] no scalar-typed state fields in StringTheory data structures"
state_hits="$(rg -n \
  "^[[:space:]]+[A-Za-z_][A-Za-z0-9_']*[Ss]tate[[:space:]]*:[[:space:]]*(ℂ|Complex|ℝ|Real)([[:space:]]|$)" \
  PhysicsLogic/StringTheory --glob '*.lean' || true)"
if [[ -n "$state_hits" ]]; then
  echo "$state_hits"
  echo "[fail] found scalar-typed state fields"
  status=1
else
  echo "[ok] no scalar-typed state fields"
fi

echo "[semantic-check] no scalar-typed closed-SFT EOM/operator residual fields"
eom_operator_hits="$(rg -n \
  "^[[:space:]]+(brstComponent|higherBracketComponent|equationResidual|linearizedContribution|nestedBracketContribution|homotopyBalance)[[:space:]]*:[[:space:]]*.*→[[:space:]]*(ℂ|Complex|ℝ|Real)([[:space:]]|$)" \
  PhysicsLogic/StringTheory --glob '*.lean' || true)"
if [[ -n "$eom_operator_hits" ]]; then
  echo "$eom_operator_hits"
  echo "[fail] found scalar-typed closed-SFT EOM/operator residual fields"
  status=1
else
  echo "[ok] closed-SFT EOM/operator residual fields are non-scalar"
fi

echo "[semantic-check] no scalar-typed residual/equation fields in StringTheory"
residual_equation_hits="$( {
  rg -n \
    "^[[:space:]]+[A-Za-z_][A-Za-z0-9_']*(Residual|residual|equationResidual|brstTerm|higherBracketTerm)[A-Za-z0-9_']*[[:space:]]*:[[:space:]]*(ℂ|Complex|ℝ|Real)([[:space:]]|$)" \
    PhysicsLogic/StringTheory --glob '*.lean' || true
  rg -n \
    "^[[:space:]]+[A-Za-z_][A-Za-z0-9_']*(Residual|residual|equationResidual|brstTerm|higherBracketTerm)[A-Za-z0-9_']*[[:space:]]*:[[:space:]].*→[[:space:]]*(ℂ|Complex|ℝ|Real)([[:space:]]|$)" \
    PhysicsLogic/StringTheory --glob '*.lean' || true
} | sort -u )"
if [[ -n "$residual_equation_hits" ]]; then
  echo "$residual_equation_hits"
  echo "[fail] found scalar-typed residual/equation fields"
  status=1
else
  echo "[ok] residual/equation fields are non-scalar"
fi

echo "[semantic-check] no scalar-typed operator fields in StringTheory data structures"
operator_hits="$(rg -n \
  "^[[:space:]]+[A-Za-z_][A-Za-z0-9_']*[Oo]perator[[:space:]]*:[[:space:]]*(ℂ|Complex|ℝ|Real)([[:space:]]|$)" \
  PhysicsLogic/StringTheory --glob '*.lean' || true)"
if [[ -n "$operator_hits" ]]; then
  echo "$operator_hits"
  echo "[fail] found scalar-typed operator fields"
  status=1
else
  echo "[ok] no scalar-typed operator fields"
fi

echo "[semantic-check] no scalar-typed functional fields ending in 'Functional'"
functional_hits="$(rg -n \
  "^[[:space:]]+[A-Za-z_][A-Za-z0-9_']*[Ff]unctional[[:space:]]*:[[:space:]]*(ℂ|Complex|ℝ|Real)([[:space:]]|$)" \
  PhysicsLogic/StringTheory --glob '*.lean' || true)"
if [[ -n "$functional_hits" ]]; then
  echo "$functional_hits"
  echo "[fail] found scalar-typed fields ending in Functional"
  status=1
else
  echo "[ok] no scalar-typed fields ending in Functional"
fi

echo "[semantic-check] ActionFunctional domains must be configuration spaces (not ℝ/ℂ)"
action_functional_domain_hits="$(rg -n \
  "^[[:space:]]+[A-Za-z_][A-Za-z0-9_']*[Aa]ction[Ff]unctional[[:space:]]*:[[:space:]]*(ℂ|Complex|ℝ|Real)[[:space:]]*→" \
  PhysicsLogic/StringTheory --glob '*.lean' || true)"
if [[ -n "$action_functional_domain_hits" ]]; then
  echo "$action_functional_domain_hits"
  echo "[fail] found ActionFunctional fields with scalar domains"
  status=1
else
  echo "[ok] ActionFunctional domains are non-scalar"
fi

echo "[semantic-check] no scalar-typed raw vertex fields (unless explicitly *Value/*Amplitude/*Coefficient/*Kinematic*)"
vertex_hits="$(rg -n \
  "^[[:space:]]+[A-Za-z_][A-Za-z0-9_']*[Vv]ertex[[:space:]]*:[[:space:]]*(ℂ|Complex|ℝ|Real)([[:space:]]|$)" \
  PhysicsLogic/StringTheory --glob '*.lean' \
  | rg -v "(Value|Amplitude|Coefficient|Kinematic)" || true)"
if [[ -n "$vertex_hits" ]]; then
  echo "$vertex_hits"
  echo "[fail] found scalar-typed raw vertex fields"
  status=1
else
  echo "[ok] no scalar-typed raw vertex fields"
fi

echo "[semantic-check] scalar action fields must be explicitly marked as Value/Scale/Difference/Variation/Bound/Contraction"
action_hits="$(
  rg -n "^[[:space:]]+[A-Za-z_][A-Za-z0-9_']*[[:space:]]*:[[:space:]]*(ℂ|Complex|ℝ|Real)([[:space:]]|$)" \
    PhysicsLogic/StringTheory --glob '*.lean' \
  | while IFS= read -r line; do
      name="$(printf "%s" "$line" | sed -E "s/^[^:]+:[0-9]+:[[:space:]]*([A-Za-z_][A-Za-z0-9_']*)[[:space:]]*:.*$/\\1/")"
      if [[ "$name" == *Action* || "$name" == action* ]]; then
        if [[ "$name" != *ActionValue* && "$name" != *ActionScale* \
              && "$name" != *ActionDifference* && "$name" != *ActionVariation* \
              && "$name" != *ActionBound* && "$name" != *ActionContraction* ]]; then
          printf "%s\n" "$line"
        fi
      fi
    done
)"
if [[ -n "$action_hits" ]]; then
  echo "$action_hits"
  echo "[fail] found ambiguous scalar action field names"
  status=1
else
  echo "[ok] scalar action field names are explicit"
fi

echo "[semantic-check] no raw scalar-typed physical scale fields (mass/coupling/radius/tension/energy/momentum/scale/length)"
physical_scale_hits="$(
  rg -n "^[[:space:]]+[A-Za-z_][A-Za-z0-9_']*[[:space:]]*:[[:space:]]*(ℂ|Complex|ℝ|Real)([[:space:]]|$)" \
    PhysicsLogic/StringTheory --glob '*.lean' \
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
  echo "[fail] found raw scalar-typed physical scale fields in StringTheory"
  status=1
else
  echo "[ok] no raw scalar-typed physical scale fields in StringTheory"
fi

exit "$status"
