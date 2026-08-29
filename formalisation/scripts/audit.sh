#!/usr/bin/env bash
# audit.sh — local audit gate for the FinShaRank2 formalization (task T02).
#
# Run from anywhere; operates on the Lake project containing this script.
# Exits 0 iff ALL of:
#   [1/3] `lake build` is green;
#   [2/3] no sorry/admit anywhere in FinShaRank2.lean + FinShaRank2/
#         (excluding FinShaRank2/Scratch/), modulo scripts/sorry-allowlist.txt;
#   [3/3] the axiom gate FinShaRank2/AxiomAudit.lean elaborates cleanly
#         (every audited decl uses only propext, Classical.choice, Quot.sound;
#         this also catches native_decide via Lean.ofReduceBool).
#
# Allowlist format: see scripts/sorry-allowlist.txt (path or decl per line).

set -u
cd "$(dirname "$0")/.." || exit 1

status=0

echo "=== [1/3] lake build ==="
if lake build; then
  echo "[1/3] OK: lake build green"
else
  echo "[1/3] FAIL: lake build failed"
  echo "AUDIT: FAIL"
  exit 1
fi

echo
echo "=== [2/3] sorry/admit scan (FinShaRank2/, excluding Scratch/) ==="
ALLOWLIST="scripts/sorry-allowlist.txt"
matches=$(grep -rnE --include='*.lean' '\b(sorry|admit)\b' FinShaRank2.lean FinShaRank2/ 2>/dev/null \
            | grep -v '^FinShaRank2/Scratch/' || true)

if [ -n "$matches" ]; then
  while IFS= read -r m; do
    [ -z "$m" ] && continue
    f="${m%%:*}"
    allowed=0
    if [ -f "$ALLOWLIST" ]; then
      while IFS= read -r entry || [ -n "$entry" ]; do
        entry="${entry%%#*}"
        entry=$(printf '%s' "$entry" | sed -e 's/^[[:space:]]*//' -e 's/[[:space:]]*$//')
        [ -z "$entry" ] && continue
        if [ "$f" = "$entry" ] || printf '%s' "$m" | grep -qF -- "$entry"; then
          allowed=1
          break
        fi
      done < "$ALLOWLIST"
    fi
    if [ "$allowed" -eq 1 ]; then
      echo "[2/3] allowlisted: $m"
    else
      echo "[2/3] DISALLOWED: $m"
      status=1
    fi
  done <<< "$matches"
fi
if [ "$status" -eq 0 ]; then
  echo "[2/3] OK: no disallowed sorry/admit"
else
  echo "[2/3] FAIL: disallowed sorry/admit found"
fi

echo
echo "=== [3/3] axiom audit (FinShaRank2/AxiomAudit.lean) ==="
if lake env lean FinShaRank2/AxiomAudit.lean; then
  echo "[3/3] OK: axiom whitelist holds for all audited decls"
else
  echo "[3/3] FAIL: axiom audit failed"
  status=1
fi

echo
if [ "$status" -eq 0 ]; then
  echo "AUDIT: PASS"
else
  echo "AUDIT: FAIL"
fi
exit "$status"
