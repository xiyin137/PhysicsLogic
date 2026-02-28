#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

echo '[check] non-Papers `sorry` count does not increase'

if ! git rev-parse --is-inside-work-tree >/dev/null 2>&1; then
  echo "[skip] not in a git worktree; cannot compute diff baseline"
  exit 0
fi

base_commit=""
if [[ -n "${SORRY_BUDGET_BASE:-}" ]] && git rev-parse --verify "${SORRY_BUDGET_BASE}" >/dev/null 2>&1; then
  base_commit="${SORRY_BUDGET_BASE}"
elif [[ -n "${GITHUB_BASE_REF:-}" ]] && git rev-parse --verify "origin/${GITHUB_BASE_REF}" >/dev/null 2>&1; then
  base_commit="$(git merge-base HEAD "origin/${GITHUB_BASE_REF}")"
fi

if [[ -z "$base_commit" ]]; then
  echo "[skip] no PR baseline available for sorry budget check"
  exit 0
fi

echo "[info] baseline: $base_commit"

base_count="$(
  git ls-tree -r --name-only "$base_commit" -- PhysicsLogic \
    | rg '\.lean$' \
    | rg -v '^PhysicsLogic/Papers/' \
    | while IFS= read -r file; do
        git show "${base_commit}:${file}" | rg -n '\bsorry\b' || true
      done \
    | wc -l \
    | tr -d ' '
)"

head_count="$(
  rg -n '\bsorry\b' PhysicsLogic --glob '*.lean' \
    | rg -v '^PhysicsLogic/Papers/' \
    | wc -l \
    | tr -d ' '
)"

echo "[info] non-Papers sorry lines: baseline=${base_count}, head=${head_count}"

if (( head_count > base_count )); then
  echo '[fail] non-Papers `sorry` count increased'
  exit 1
fi

echo '[ok] non-Papers `sorry` count did not increase'
