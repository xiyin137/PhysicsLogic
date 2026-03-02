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

echo "[global-semantic-check] no raw arrow-typed Action fields with ActionScale/ComplexActionValue codomain"
raw_action_arrow_hits="$(
  {
    rg -n "^[[:space:]]+[A-Za-z_][A-Za-z0-9_']*[Aa]ction[A-Za-z0-9_']*[[:space:]]*:[[:space:]].*→[[:space:]]*(ActionScale|ComplexActionValue)([[:space:]]|$)" \
      PhysicsLogic --glob '*.lean' \
    | rg -v '^PhysicsLogic/Papers/' \
    | while IFS= read -r line; do
        name="$(printf "%s" "$line" | extract_name)"
        lower="$(printf "%s" "$name" | tr '[:upper:]' '[:lower:]')"
        if [[ "$lower" == *actiondifference* || "$lower" == *actionvariation* || \
              "$lower" == *actionbound* || "$lower" == *actionvalue* || \
              "$lower" == *actionscale* || "$lower" == *actioncoefficient* || \
              "$lower" == *actionamplitude* || "$lower" == *actionratio* ]]; then
          continue
        fi
        printf "%s\n" "$line"
      done
  } || true
)"
if [[ -n "$raw_action_arrow_hits" ]]; then
  echo "$raw_action_arrow_hits"
  echo "[fail] found raw arrow-typed Action fields with ActionScale/ComplexActionValue codomain"
  status=1
else
  echo "[ok] no raw arrow-typed Action fields with ActionScale/ComplexActionValue codomain"
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

echo "[global-semantic-check] central-charge fields use CentralCharge aliases"
raw_central_charge_hits="$(
  rg -n "^[[:space:]]+[A-Za-z_][A-Za-z0-9_']*CentralCharge[[:space:]]*:[[:space:]]*(ℝ|Real)([[:space:]]|$)" \
    PhysicsLogic --glob '*.lean' \
  | rg -v '^PhysicsLogic/Papers/' || true
)"
if [[ -n "$raw_central_charge_hits" ]]; then
  echo "$raw_central_charge_hits"
  echo "[fail] found raw ℝ/Real central-charge fields in non-Papers modules"
  status=1
else
  echo "[ok] central-charge fields use semantic aliases in non-Papers modules"
fi

echo "[global-semantic-check] spin/conformal-weight fields use ScalingDimension aliases"
raw_spin_weight_hits="$(
  {
    rg -n "^[[:space:]]+[A-Za-z_][A-Za-z0-9_']*[Ss]pin[A-Za-z0-9_']*[[:space:]]*:[[:space:]]*(ℝ|Real)([[:space:]]|$)" \
      PhysicsLogic --glob '*.lean'
    rg -n "^[[:space:]]+[A-Za-z_][A-Za-z0-9_']*conformalWeight[A-Za-z0-9_']*[[:space:]]*:[[:space:]]*(ℝ|Real)([[:space:]]|$)" \
      PhysicsLogic --glob '*.lean'
    rg -n "^[[:space:]]+[A-Za-z_][A-Za-z0-9_']*twist[A-Za-z0-9_']*[[:space:]]*:[[:space:]]*(ℝ|Real)([[:space:]]|$)" \
      PhysicsLogic --glob '*.lean'
  } | rg -v '^PhysicsLogic/Papers/' || true
)"
if [[ -n "$raw_spin_weight_hits" ]]; then
  echo "$raw_spin_weight_hits"
  echo "[fail] found raw ℝ/Real spin or conformal-weight fields in non-Papers modules"
  status=1
else
  echo "[ok] spin/conformal-weight fields use semantic aliases in non-Papers modules"
fi

echo "[global-semantic-check] conformal-block weight fields use ConformalWeight aliases"
raw_block_weight_hits="$(
  rg -n "^[[:space:]]+(external_weights|internal_weight)[[:space:]]*:[[:space:]].*(ℝ|Real)" \
    PhysicsLogic/QFT/CFT/TwoDimensional/ConformalBlocks.lean || true
)"
if [[ -n "$raw_block_weight_hits" ]]; then
  echo "$raw_block_weight_hits"
  echo "[fail] found raw ℝ/Real conformal-block weight fields"
  status=1
else
  echo "[ok] conformal-block weight fields use semantic aliases"
fi

echo "[global-semantic-check] AdS3 spectral-weight fields use ScalingDimension aliases"
raw_ads3_weight_hits="$(
  rg -n "^[[:space:]]+(jDiscrete|jReflected|jContinuousRealPart|continuousParameter|alphaParameter|mQuantum|currentDescendantLevel|virasoroDescendantLevel|adsDescendantLevel|suDescendantLevel|internalWeight|j0Three|flowedLZero|poleExcitationNumber|muOrderTwoCorrectionDenominator|slBosonicLevel|suBosonicLevel|slPower|suPower)[[:space:]]*:[[:space:]]*(ℝ|Real)([[:space:]]|$)" \
    PhysicsLogic/StringTheory/AdS3CFT2.lean \
    PhysicsLogic/QFT/CFT/TwoDimensional/CurrentAlgebras.lean || true
)"
if [[ -n "$raw_ads3_weight_hits" ]]; then
  echo "$raw_ads3_weight_hits"
  echo "[fail] found raw ℝ/Real AdS3 spectral-weight fields in core modules"
  status=1
else
  echo "[ok] AdS3 spectral-weight fields use semantic aliases in core modules"
fi

echo "[global-semantic-check] AdS3 OPE/normalization coefficients use semantic aliases"
raw_ads3_ope_hits="$(
  rg -n "^[[:space:]]+(cSuHalfHalfOne|cSlMinusHalfMinusHalfMinusOne|suIdentityOpeCoefficient|slIdentityOpeCoefficient|cSuLargeKAsymptoticValue|cSlLargeKAsymptoticValue|overallCoefficient)[[:space:]]*:[[:space:]]*(ℝ|Real)([[:space:]]|$)" \
    PhysicsLogic/StringTheory/AdS3CFT2.lean \
    PhysicsLogic/QFT/CFT/TwoDimensional/CurrentAlgebras.lean || true
)"
if [[ -n "$raw_ads3_ope_hits" ]]; then
  echo "$raw_ads3_ope_hits"
  echo "[fail] found raw ℝ/Real AdS3 OPE/normalization coefficient fields in core modules"
  status=1
else
  echo "[ok] AdS3 OPE/normalization coefficient fields use semantic aliases in core modules"
fi

echo "[global-semantic-check] core coefficient/normalization fields use semantic aliases"
raw_core_coeff_hits="$(
  rg -n "^[[:space:]]+(stressTensorTrace|measureNormalization|harmonicCoefficient|canonicalPrefactor|microcanonicalPrefactor|boostFactor|zeta3Coefficient|gammaKernelLeadingPole|gammaKernelConstantTerm|sphereNormalization|ghostMeasureWeight)[[:space:]]*:[[:space:]]*(ℝ|Real)([[:space:]]|$)" \
    PhysicsLogic --glob '*.lean' \
  | rg -v '^PhysicsLogic/Papers/' || true
)"
if [[ -n "$raw_core_coeff_hits" ]]; then
  echo "$raw_core_coeff_hits"
  echo "[fail] found raw ℝ/Real core coefficient/normalization fields in non-Papers modules"
  status=1
else
  echo "[ok] core coefficient/normalization fields use semantic aliases in non-Papers modules"
fi

echo "[global-semantic-check] core complex coefficient/amplitude labels use semantic aliases"
raw_core_complex_coeff_hits="$(
  rg -n "^[[:space:]]+(qgPartitionValue|cftCorrelatorValue|leftOPECoefficient|rightOPECoefficient|tSecondPoleCoeff|tSimplePoleCoeff|tBarSecondPoleCoeff|tBarSimplePoleCoeff)[[:space:]]*:[[:space:]]*(ℂ|Complex)([[:space:]]|$)" \
    PhysicsLogic --glob '*.lean' \
  | rg -v '^PhysicsLogic/Papers/' || true
)"
if [[ -n "$raw_core_complex_coeff_hits" ]]; then
  echo "$raw_core_complex_coeff_hits"
  echo "[fail] found raw ℂ/Complex core coefficient/amplitude labels in non-Papers modules"
  status=1
else
  echo "[ok] core complex coefficient/amplitude labels use semantic aliases in non-Papers modules"
fi

echo "[global-semantic-check] AdSCFT stress-tensor trace is operator-valued"
raw_ads_trace_scalar_hits="$(
  rg -n "^[[:space:]]+stressTensorTrace[[:space:]]*:[[:space:]]*(ScalingDimension|ConformalWeight|DimensionlessCoefficient|ℝ|Real|ComplexAmplitude|ℂ|Complex)([[:space:]]|$)" \
    PhysicsLogic/StringTheory/AdSCFT.lean || true
)"
if [[ -n "$raw_ads_trace_scalar_hits" ]]; then
  echo "$raw_ads_trace_scalar_hits"
  echo "[fail] found scalar-typed AdSCFT stress-tensor trace fields"
  status=1
else
  echo "[ok] AdSCFT stress-tensor trace is operator-valued"
fi

echo "[global-semantic-check] AdSCFT dictionary uses source-dependent functionals"
legacy_ads_dictionary_value_hits="$(
  rg -n "^[[:space:]]+(qgPartitionValue|cftCorrelatorValue)[[:space:]]*:" \
    PhysicsLogic/StringTheory/AdSCFT.lean || true
)"
if [[ -n "$legacy_ads_dictionary_value_hits" ]]; then
  echo "$legacy_ads_dictionary_value_hits"
  echo "[fail] found legacy scalar-valued AdSCFT dictionary fields"
  status=1
else
  echo "[ok] AdSCFT dictionary fields are functional interfaces"
fi

echo "[global-semantic-check] AdSCFT Hawking-Page coupling/action labels are semantic"
legacy_ads_hawking_hits="$(
  {
    rg -n "^[[:space:]]+kappaFive[[:space:]]*:[[:space:]](ℝ|Real)([[:space:]]|$)" \
      PhysicsLogic/StringTheory/AdSCFT.lean
    rg -n "^[[:space:]]+logPartitionShift[[:space:]]*:" \
      PhysicsLogic/StringTheory/AdSCFT.lean
  } || true
)"
if [[ -n "$legacy_ads_hawking_hits" ]]; then
  echo "$legacy_ads_hawking_hits"
  echo "[fail] found legacy AdSCFT Hawking-Page scalar labels/types"
  status=1
else
  echo "[ok] AdSCFT Hawking-Page coupling/action labels use semantic types"
fi

echo "[global-semantic-check] AdSCFT Hawking-Page Euclidean action shift uses ActionScale"
ads_hawking_action_shift_hits="$(
  rg -n "^[[:space:]]+euclideanActionShift[[:space:]]*:[[:space:]]ActionScale([[:space:]]|$)" \
    PhysicsLogic/StringTheory/AdSCFT.lean || true
)"
if [[ -z "$ads_hawking_action_shift_hits" ]]; then
  echo "[fail] missing `euclideanActionShift : ActionScale` in AdSCFT Hawking-Page data"
  status=1
else
  echo "[ok] AdSCFT Hawking-Page Euclidean action shift uses ActionScale"
fi

echo "[global-semantic-check] LSZ field-strength renormalization uses semantic alias"
raw_field_strength_hits="$(
  rg -n "^[[:space:]]+field_strength_Z[[:space:]]*:[[:space:]]*(ℝ|Real)([[:space:]]|$)" \
    PhysicsLogic --glob '*.lean' \
  | rg -v '^PhysicsLogic/Papers/' || true
)"
if [[ -n "$raw_field_strength_hits" ]]; then
  echo "$raw_field_strength_hits"
  echo "[fail] found raw ℝ/Real field_strength_Z declarations in non-Papers modules"
  status=1
else
  echo "[ok] LSZ field-strength renormalization uses semantic alias in non-Papers modules"
fi

echo "[global-semantic-check] RG partition-function maps avoid raw ℝ/Real codomain"
raw_partition_function_hits="$(
  rg -n "^[[:space:]]+Z[[:space:]]*:[[:space:]]Cutoff[[:space:]]*→[[:space:]]*(ℝ|Real)([[:space:]]|$)" \
    PhysicsLogic --glob '*.lean' \
  | rg -v '^PhysicsLogic/Papers/' || true
)"
if [[ -n "$raw_partition_function_hits" ]]; then
  echo "$raw_partition_function_hits"
  echo "[fail] found raw ℝ/Real partition-function maps in non-Papers modules"
  status=1
else
  echo "[ok] RG partition-function maps use semantic aliases in non-Papers modules"
fi

echo "[global-semantic-check] Wilsonian path-integral effective actions use functional records"
raw_effective_map_hits="$(
  rg -n "^[[:space:]]+effective_at_scale[[:space:]]*:[[:space:]]UVCutoff[[:space:]]*→[[:space:]]*\\(F[[:space:]]*→[[:space:]]*(ActionScale|ComplexActionValue)\\)" \
    PhysicsLogic/QFT/RG/EffectiveAction.lean || true
)"
if [[ -n "$raw_effective_map_hits" ]]; then
  echo "$raw_effective_map_hits"
  echo "[fail] found raw map-typed Wilsonian effective actions in path-integral interfaces"
  status=1
else
  echo "[ok] Wilsonian path-integral effective actions use explicit functional records"
fi

echo "[global-semantic-check] LG polynomial couplings use semantic aliases"
raw_lg_coupling_hits="$(
  rg -n "^[[:space:]]+coupling[[:space:]]*:[[:space:]]ℕ[[:space:]]*→[[:space:]](ℝ|Real)([[:space:]]|$)" \
    PhysicsLogic/QFT/RG/TwoDimensionalFlows.lean || true
)"
if [[ -n "$raw_lg_coupling_hits" ]]; then
  echo "$raw_lg_coupling_hits"
  echo "[fail] found raw ℝ/Real LG polynomial couplings"
  status=1
else
  echo "[ok] LG polynomial couplings use semantic aliases"
fi

exit "$status"
