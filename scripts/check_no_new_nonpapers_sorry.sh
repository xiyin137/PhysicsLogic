#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

echo '[check] no newly added `sorry` in non-Papers Lean files'

if ! git rev-parse --is-inside-work-tree >/dev/null 2>&1; then
  echo "[skip] not in a git worktree; cannot compute diff baseline"
  exit 0
fi

base_commit=""
if [[ -n "${GITHUB_BASE_REF:-}" ]] && git rev-parse --verify "origin/${GITHUB_BASE_REF}" >/dev/null 2>&1; then
  base_commit="$(git merge-base HEAD "origin/${GITHUB_BASE_REF}")"
elif git rev-parse --verify HEAD^ >/dev/null 2>&1; then
  base_commit="HEAD^"
fi

if [[ -z "$base_commit" ]]; then
  echo "[skip] no baseline commit available for new-sorry check"
  exit 0
fi

echo "[info] diff baseline: $base_commit"

added_sorry_hits="$(
  git diff --unified=0 "$base_commit"...HEAD -- PhysicsLogic \
    | awk '
      /^+++ b\// {
        file = substr($0, 7)
        next
      }
      /^\+/ && $0 !~ /^\+\+\+/ {
        if (file ~ /^PhysicsLogic\/Papers\//) next
        if (file !~ /\.lean$/) next
        line = substr($0, 2)
        if (line ~ /(^|[^[:alnum:]_])sorry([^[:alnum:]_]|$)/) {
          print file ":" line
        }
      }
    '
)"

if [[ -n "$added_sorry_hits" ]]; then
  echo "$added_sorry_hits"
  echo '[fail] found newly added `sorry` in non-Papers Lean files'
  exit 1
fi

echo '[ok] no newly added `sorry` in non-Papers Lean files'
