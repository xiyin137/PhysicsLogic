#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

notes_dir="docs/stringbook/notes"
status_file="docs/stringbook/appendix-import-status.md"

letters=(a b c d e f g h i j k l m n o p q r)
fail=0

trim() {
  local s="$1"
  s="${s#"${s%%[![:space:]]*}"}"
  s="${s%"${s##*[![:space:]]}"}"
  printf "%s" "$s"
}

echo "[appendix-check] validating appendix note files and targets..."
for letter in "${letters[@]}"; do
  note="${notes_dir}/appendix-${letter}.md"
  if [[ ! -f "$note" ]]; then
    echo "ERROR: missing note file: $note"
    fail=1
    continue
  fi

  target_line="$(sed -n 's/^- Draft Lean target: //p' "$note" | head -n1)"
  if [[ -z "$target_line" ]]; then
    echo "ERROR: missing Draft Lean target line in $note"
    fail=1
    continue
  fi

  target_line="${target_line//\`/}"
  IFS=',' read -r -a targets <<< "$target_line"
  for raw_target in "${targets[@]}"; do
    target="$(trim "$raw_target")"
    if [[ -z "$target" ]]; then
      continue
    fi

    if [[ "$target" == *"*"* ]]; then
      base="${target%\*}"
      base="${base%/}"
      if [[ ! -d "$base" ]]; then
        echo "ERROR: wildcard target directory missing: $target (from $note)"
        fail=1
        continue
      fi
      if ! find "$base" -maxdepth 5 -type f -name '*.lean' | grep -q .; then
        echo "ERROR: wildcard target has no Lean files: $target (from $note)"
        fail=1
      fi
      continue
    fi

    if [[ ! -f "$target" ]]; then
      echo "ERROR: target file missing: $target (from $note)"
      fail=1
      continue
    fi

    module="${target%.lean}"
    module="${module//\//.}"
    if ! rg -q "^import ${module}$" PhysicsLogic.lean PhysicsLogic; then
      echo "ERROR: target module is not imported anywhere: $module (from $note)"
      fail=1
    fi
  done
done

echo "[appendix-check] validating appendix status ledger coverage..."
if [[ ! -f "$status_file" ]]; then
  echo "ERROR: missing appendix status file: $status_file"
  fail=1
else
  for upper in {A..R}; do
    if ! rg -q "^\\| ${upper} \\|" "$status_file"; then
      echo "ERROR: appendix ${upper} missing from $status_file"
      fail=1
    fi
  done
fi

if [[ "$fail" -ne 0 ]]; then
  echo "[appendix-check] FAILED"
  exit 1
fi

echo "[appendix-check] OK"
