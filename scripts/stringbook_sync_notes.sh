#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

TOC_FILE="references/stringbook/string notes.toc"
TEX_FILE="references/stringbook/string notes.tex"
PDF_FILE="references/stringbook/string notes.pdf"
BIB_FILE="references/stringbook/stringrefs.bib"
BOOK_ROOT="references/stringbook"

OUT_DIR="docs/stringbook"
DATA_DIR="$OUT_DIR/data"
NOTES_DIR="$OUT_DIR/notes"
FORCE_REWRITE="${STRINGBOOK_FORCE_REWRITE:-0}"

if [[ ! -f "$TOC_FILE" ]]; then
  echo "[fail] missing TOC: $TOC_FILE"
  exit 1
fi

mkdir -p "$DATA_DIR" "$NOTES_DIR"

sections_tsv="$DATA_DIR/sections.tsv"
subsections_tsv="$DATA_DIR/subsections.tsv"
subsubsections_tsv="$DATA_DIR/subsubsections.tsv"
notebooks_tsv="$DATA_DIR/notebooks.tsv"
index_md="$OUT_DIR/reading-index.md"
inventory_md="$OUT_DIR/inventory.md"

parse_toc_kind() {
  local kind="$1"
  local out="$2"
  rg "^\\\\contentsline \\{${kind}\\}\\{\\\\numberline \\{" "$TOC_FILE" \
    | sed -E "s/^\\\\contentsline \\{${kind}\\}\\{\\\\numberline \\{([^}]*)\\}(.+)\\}\\{([^}]*)\\}\\{[^}]*\\}%$/\\1\\t\\2\\t\\3/" \
    > "$out"
}

note_filename() {
  local id="$1"
  if [[ "$id" =~ ^[0-9]+$ ]]; then
    printf "section-%02d.md" "$id"
  else
    printf "appendix-%s.md" "$(printf "%s" "$id" | tr '[:upper:]' '[:lower:]')"
  fi
}

unit_label() {
  local id="$1"
  if [[ "$id" =~ ^[0-9]+$ ]]; then
    printf "Section %02d" "$id"
  else
    printf "Appendix %s" "$id"
  fi
}

lean_target() {
  local id="$1"
  if [[ "$id" =~ ^[0-9]+$ ]]; then
    printf "PhysicsLogic/StringTheory/Section%02d.lean" "$id"
  else
    printf "PhysicsLogic/StringTheory/Appendix%s.lean" "$id"
  fi
}

section_group() {
  local id="$1"
  if [[ "$id" =~ ^[0-9]+$ ]]; then
    local n="$id"
    if (( n >= 1 && n <= 5 )); then
      printf "Foundations"
    elif (( n >= 6 && n <= 10 )); then
      printf "Superstring Formalism"
    elif (( n >= 11 && n <= 16 )); then
      printf "D-branes and String Field Theory"
    elif (( n >= 17 && n <= 20 )); then
      printf "Dualities and AdS/CFT"
    elif (( n >= 21 && n <= 26 )); then
      printf "Holography and Integrability"
    else
      printf "Core"
    fi
  else
    printf "Appendices"
  fi
}

notebook_focus() {
  local path="$1"
  case "$path" in
    *"conifold geometry"*) echo "19.5 Conifold in string theory" ;;
    *"G2 conical geometry"*) echo "19.6.2 G2 holonomy and singularities" ;;
    *"mirror TBA and wrapping corrections"*) echo "24.3-24.7 Mirror TBA and quantum spectral curve" ;;
    *"BES equation"*) echo "23.8 BES equation and cusp anomalous dimension" ;;
    *"su(2|2) spin chain"*) echo "23.4-23.5 Integrable spin chains and symmetries" ;;
    *"Conformal blocks and bootstrap demo"*) echo "E.6-E.7 Conformal blocks and bootstrap methods" ;;
    *"Liouville CFT"*) echo "I.5 Liouville CFT; 19.4 double-scaled LST links" ;;
    *"Type II torus 4-graviton amplitude check"*) echo "8.2 One-loop amplitudes; 14.1 superstring perturbation" ;;
    *"Type II basic worldsheet calculations"*) echo "6.1-6.6 Quantization of superstrings" ;;
    *"GS kappa symmetry"*) echo "9.3 Green-Schwarz formulation; 14.5.1 kappa symmetry" ;;
    *"2D superspace"*) echo "J.1 (1,1) superspace; J.3 (2,2) superspace" ;;
    *"4D superspace"*) echo "M.2 4D N=1 superspace" ;;
    *"gamma matrices"*) echo "L Spinor conventions in general dimensions" ;;
    *"spinfield cocycles"*) echo "6.4 NS/R sectors and GSO projection" ;;
    *"Instanton and anomalies"*) echo "16 D-instantons; O Anomalies" ;;
    *"string coupling conventions"*) echo "A Frequently used formulae and conventions" ;;
    *"special geometry"*) echo "N.5.1 Special Kahler geometry" ;;
    *"JS.nb"*) echo "Figure-generation notebook (cross-reference with chapter figures)" ;;
    *"TDL figures.nb"*) echo "Figure-generation notebook (defect/orbifold sections)" ;;
    *"generating figures.nb"*) echo "General figure generation support notebook" ;;
    *)
      echo "Unmapped: inspect manually"
      ;;
  esac
}

write_note_if_missing() {
  local unit_id="$1"
  local unit_title="$2"
  local start_page="$3"
  local note_file="$NOTES_DIR/$(note_filename "$unit_id")"
  local label
  local lean_file

  label="$(unit_label "$unit_id")"
  lean_file="$(lean_target "$unit_id")"

  {
    echo "# ${label}: ${unit_title}"
    echo
    echo "- Status: not started"
    echo "- Source page start: ${start_page}"
    echo "- Source files: \`${TEX_FILE}\`, \`${PDF_FILE}\`, \`${BIB_FILE}\`"
    echo "- Draft Lean target: \`${lean_file}\`"
    echo
    echo "## Reading Summary"
    echo "- TODO"
    echo
    echo "## Candidate Formalization Units"
    echo "- TODO"
    echo
    echo "## Assumption Candidates"
    echo "- TODO"
    echo
    echo "## Subsections"
    awk -F '\t' -v unit="$unit_id" '
      {
        split($1, parts, /\./)
      }
      parts[1] == unit {
        printf("- [ ] %s %s (p.%s)\n", $1, $2, $3)
        found = 1
      }
      END {
        if (!found) print "- (none listed in TOC)"
      }
    ' "$subsections_tsv"
    echo
    echo "## Subsubsections"
    awk -F '\t' -v unit="$unit_id" '
      {
        split($1, parts, /\./)
      }
      parts[1] == unit {
        printf("- [ ] %s %s (p.%s)\n", $1, $2, $3)
        found = 1
      }
      END {
        if (!found) print "- (none listed in TOC)"
      }
    ' "$subsubsections_tsv"
    echo
    echo "## Extraction Checklist"
    echo "- [ ] Definitions and notation captured"
    echo "- [ ] Main claims and equations extracted"
    echo "- [ ] Dependency chain to prior sections identified"
    echo "- [ ] Candidate Lean declarations drafted"
    echo "- [ ] Assumptions mapped to \`PhysicsLogic/Assumptions.lean\`"
  } > "$note_file"
}

parse_toc_kind "section" "$sections_tsv"
parse_toc_kind "subsection" "$subsections_tsv"
parse_toc_kind "subsubsection" "$subsubsections_tsv"

find "$BOOK_ROOT" -type f \( -name '*.nb' -o -name '*.wl' -o -name '*.m' \) \
  | sed "s#^${BOOK_ROOT}/##" \
  | sort > "$notebooks_tsv"

touched_notes=0
while IFS=$'\t' read -r unit_id unit_title start_page; do
  note_path="$NOTES_DIR/$(note_filename "$unit_id")"
  if [[ ! -f "$note_path" || "$FORCE_REWRITE" == "1" ]]; then
    write_note_if_missing "$unit_id" "$unit_title" "$start_page"
    touched_notes=$((touched_notes + 1))
  fi
done < "$sections_tsv"

sections_count="$(wc -l < "$sections_tsv" | tr -d ' ')"
subsections_count="$(wc -l < "$subsections_tsv" | tr -d ' ')"
subsubsections_count="$(wc -l < "$subsubsections_tsv" | tr -d ' ')"
notebooks_count="$(wc -l < "$notebooks_tsv" | tr -d ' ')"
notes_count="$(
  find "$NOTES_DIR" -type f \( -name 'section-*.md' -o -name 'appendix-*.md' \) \
    | wc -l \
    | tr -d ' '
)"

{
  echo "# String Book Inventory"
  echo
  echo "- Generated: $(date '+%Y-%m-%d %H:%M:%S %Z')"
  echo "- Source TOC: \`${TOC_FILE}\`"
  echo "- Sections (incl. appendices): ${sections_count}"
  echo "- Subsections: ${subsections_count}"
  echo "- Subsubsections: ${subsubsections_count}"
  echo "- Mathematica notebooks: ${notebooks_count}"
  echo "- Note files present: ${notes_count}"
  echo
  echo "## Source Artifacts"
  echo "- \`${TEX_FILE}\`"
  echo "- \`${PDF_FILE}\`"
  echo "- \`${BIB_FILE}\`"
  echo "- \`references/stringbook/Code repository/\`"
  echo "- \`references/stringbook/figures/\`"
} > "$inventory_md"

{
  echo "# String Book Reading Index"
  echo
  echo "- Regenerate with: \`./scripts/stringbook_sync_notes.sh\`"
  echo "- Note templates are created only when missing, so manual edits are preserved."
  echo
  echo "| Unit | Group | Title | Start Page | Notes |"
  echo "| --- | --- | --- | ---: | --- |"
  while IFS=$'\t' read -r unit_id unit_title start_page; do
    note_file="$(note_filename "$unit_id")"
    label="$(unit_label "$unit_id")"
    group="$(section_group "$unit_id")"
    printf "| %s | %s | %s | %s | [notes/%s](notes/%s) |\n" \
      "$label" "$group" "$unit_title" "$start_page" "$note_file" "$note_file"
  done < "$sections_tsv"
  echo
  echo "## Notebook Coverage"
  echo
  echo "| Notebook | Suggested Focus |"
  echo "| --- | --- |"
  while IFS= read -r notebook_path; do
    focus="$(notebook_focus "$notebook_path")"
    printf "| %s | %s |\n" "$notebook_path" "$focus"
  done < "$notebooks_tsv"
} > "$index_md"

echo "[ok] synced string book notes"
echo "[info] sections=${sections_count}, subsections=${subsections_count}, subsubsections=${subsubsections_count}"
echo "[info] notes=${notes_count}, touched_now=${touched_notes}, notebooks=${notebooks_count}"
