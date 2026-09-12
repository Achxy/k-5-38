#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
project_root="$PWD"
workspace_root="$(dirname "$project_root")"
if [[ -f "$workspace_root/lean-workspace.json" && -f "$workspace_root/scripts/lean-workspace.py" ]]; then
  exec python3 "$workspace_root/scripts/lean-workspace.py" run "$project_root" -- "$@"
fi
# A source bundle remains a normal standalone Lake project.
if [[ -x "$project_root/.tools/elan/bin/lake" ]]; then
  export ELAN_HOME="$project_root/.tools/elan"
  export PATH="$ELAN_HOME/bin:$PATH"
fi
exec "$@"
