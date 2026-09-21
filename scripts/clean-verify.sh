#!/usr/bin/env bash
set -euo pipefail

repo_root=$(git rev-parse --show-toplevel)
clean_bin=${CLEAN_BIN:-clean}
report_path=${CLEAN_REPORT:-"$repo_root/.lake/clean/soundcalc-verification.json"}
init_cache_dir=${CLEAN_INIT_CACHE:-"$repo_root/.lake/clean/init-cache"}
parallelism=${CLEAN_PARALLEL:-1}
module_limit=${CLEAN_LIMIT:-}

if ! command -v "$clean_bin" >/dev/null 2>&1; then
  echo "Clean executable not found: $clean_bin" >&2
  echo "Set CLEAN_BIN to a Clean binary built from https://github.com/alabsystems/clean." >&2
  exit 127
fi

cd "$repo_root"
lake build Soundcalc

mkdir -p "$(dirname "$report_path")" "$init_cache_dir"

args=(
  olean verify-batch
  "$repo_root/.lake/build/lib/lean"
  --full-validation
  --parallel "$parallelism"
  --cache-dir "$init_cache_dir"
  --json-report "$report_path"
)

if [[ -n "$module_limit" ]]; then
  args+=(--limit "$module_limit")
fi

for package_path in "$repo_root"/.lake/packages/*/.lake/build/lib/lean; do
  if [[ -d "$package_path" ]]; then
    args+=(--init-path "$package_path")
  fi
done

"$clean_bin" "${args[@]}"

echo "Clean verification report: $report_path"
