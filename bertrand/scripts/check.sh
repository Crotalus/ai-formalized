#!/usr/bin/env bash
# Elaborate one Lean file (default Bertrand/Main.lean); report errors and remaining sorries.
set -uo pipefail
cd "$(dirname "$0")/.."
FILE="${1:-Bertrand/Main.lean}"
LOG=.last_check.log
lake env lean "$FILE" >"$LOG" 2>&1; status=$?
grep ': error' -A8 "$LOG" | head -100
echo "== sorry at:"; grep "declaration uses .sorry." "$LOG" | sed -E 's/^[^:]+:([0-9]+):.*/  line \1/'
echo "SUMMARY: exit=$status errors=$(grep -c ': error' "$LOG") sorries=$(grep -c "declaration uses .sorry." "$LOG")"
