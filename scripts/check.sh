#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
scripts/with-lean.sh lake --wfail build
scripts/with-lean.sh lake env lean Audit.lean
scripts/with-lean.sh lake env lean Completion.lean
