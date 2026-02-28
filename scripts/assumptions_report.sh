#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

out_file="${1:-}"

defs_tmp="$(mktemp)"
desc_tmp="$(mktemp)"
refs_raw_tmp="$(mktemp)"
refs_tmp="$(mktemp)"
total_tmp="$(mktemp)"
core_tmp="$(mktemp)"
papers_tmp="$(mktemp)"
rows_tmp="$(mktemp)"
summary_tmp="$(mktemp)"
report_tmp="$(mktemp)"
trap 'rm -f "$defs_tmp" "$desc_tmp" "$refs_raw_tmp" "$refs_tmp" "$total_tmp" "$core_tmp" "$papers_tmp" "$rows_tmp" "$summary_tmp" "$report_tmp"' EXIT

# Assumption ids and stable payloads.
rg -n --no-filename '^def[[:space:]]+[A-Za-z0-9_]+[[:space:]]*:[[:space:]]*String[[:space:]]*:=[[:space:]]*"[^"]+"' PhysicsLogic/Assumptions.lean \
  | sed -E 's/^[0-9]+:def[[:space:]]+([A-Za-z0-9_]+)[[:space:]]*:[[:space:]]*String[[:space:]]*:=[[:space:]]*"([^"]+)".*/\1\t\2/' \
  | sort -u > "$defs_tmp"

# Human-readable descriptions from the registry block.
awk '
  /^def assumptionRegistry/ {in_registry = 1}
  in_registry {
    if ($0 ~ /AssumptionId\.[A-Za-z0-9_]+/) {
      id = $0
      sub(/.*AssumptionId\./, "", id)
      sub(/[^A-Za-z0-9_].*/, "", id)
      current = id
    }
    if (current != "" && $0 ~ /"[^"]+"/) {
      desc = $0
      sub(/^[^"]*"/, "", desc)
      sub(/".*$/, "", desc)
      print current "\t" desc
      current = ""
    }
    if ($0 ~ /^[[:space:]]*\]$/) exit
  }
' PhysicsLogic/Assumptions.lean | sort -u > "$desc_tmp"

# All AssumptionId references outside the registry source file.
rg -n -o 'AssumptionId\.[A-Za-z0-9_]+' PhysicsLogic --glob '*.lean' > "$refs_raw_tmp" || true
if [[ -s "$refs_raw_tmp" ]]; then
  awk -F ':' '
    $1 != "PhysicsLogic/Assumptions.lean" {
      id = $3
      sub(/^AssumptionId\./, "", id)
      print $1 "\t" id
    }
  ' "$refs_raw_tmp" > "$refs_tmp"
else
  : > "$refs_tmp"
fi

if [[ -s "$refs_tmp" ]]; then
  cut -f2 "$refs_tmp" \
    | sort \
    | uniq -c \
    | awk '{print $2 "\t" $1}' > "$total_tmp"

  awk -F '\t' '$1 !~ /^PhysicsLogic\/Papers\//' "$refs_tmp" \
    | cut -f2 \
    | sort \
    | uniq -c \
    | awk '{print $2 "\t" $1}' > "$core_tmp"

  awk -F '\t' '$1 ~ /^PhysicsLogic\/Papers\//' "$refs_tmp" \
    | cut -f2 \
    | sort \
    | uniq -c \
    | awk '{print $2 "\t" $1}' > "$papers_tmp"
else
  : > "$total_tmp"
  : > "$core_tmp"
  : > "$papers_tmp"
fi

awk -F '\t' -v summary_path="$summary_tmp" '
  FNR == 1 {file_idx += 1}
  file_idx == 1 {desc[$1] = $2; next}
  file_idx == 2 {total[$1] = $2; next}
  file_idx == 3 {core[$1] = $2; next}
  file_idx == 4 {papers[$1] = $2; next}
  file_idx == 5 {
    id = $1
    payload = $2
    description = (id in desc) ? desc[id] : "(missing description)"
    gsub(/\|/, "\\|", description)
    total_refs = (id in total) ? total[id] : 0
    core_refs = (id in core) ? core[id] : 0
    papers_refs = (id in papers) ? papers[id] : 0
    registered += 1
    if (core_refs > 0) used_in_core += 1
    if (total_refs == 0) unused += 1
    printf("| `%s` | `%s` | %d | %d | %d | %s |\n",
      id, payload, core_refs, papers_refs, total_refs, description)
    next
  }
  END {
    printf("%d\t%d\t%d\n", registered, used_in_core, unused) > summary_path
  }
' "$desc_tmp" "$total_tmp" "$core_tmp" "$papers_tmp" "$defs_tmp" > "$rows_tmp"

IFS=$'\t' read -r registered_count used_in_core_count unused_count < "$summary_tmp"
generated_at="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"

{
  echo "# Physics Assumptions Report"
  echo
  echo "- Generated (UTC): \`$generated_at\`"
  echo "- Registered assumptions: \`$registered_count\`"
  echo "- Assumptions referenced in non-Papers modules: \`$used_in_core_count\`"
  echo "- Assumptions with zero references outside registry: \`$unused_count\`"
  echo
  echo "| AssumptionId | Payload | Core refs | Papers refs | Total refs | Description |"
  echo "| --- | --- | ---: | ---: | ---: | --- |"
  cat "$rows_tmp"
} > "$report_tmp"

if [[ -n "$out_file" ]]; then
  mkdir -p "$(dirname "$out_file")"
  cp "$report_tmp" "$out_file"
  echo "[ok] wrote assumptions report to $out_file"
else
  cat "$report_tmp"
fi
