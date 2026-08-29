#!/bin/bash
# refresh.sh -- regenerate every A5 deliverable from whatever raw outputs are on disk.
#
#   ./refresh.sh            regenerate, then print a summary
#   ./refresh.sh --check    change nothing; exit 2 if anything is out of date
#
# This is THE drill after a certificate run lands.  It is idempotent: running it
# twice changes nothing the second time, and it is safe to run when only some of
# the runs you are waiting on have finished -- primes with no cert_<p>.out simply
# read "not computed" everywhere, which is a gap and NOT a stop-the-line event.
#
# It does three things, in order, and none of them types a number by hand:
#   1. make_tables.py   raw cert_<p>.out  ->  code/data/tables.md + tables.tex
#   2. paste_tables.py  tables.tex        ->  the generated blocks in the fragments
#   3. splice_report.py tables.md         ->  docs/A5_REPORT.md status + tables
# then it prints a per-prime summary and flags anything that needs a human.

set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
DATA="$HERE/../data"
PRIMES="5 13 17 29 37 41"
CHECK=0
[ "${1:-}" = "--check" ] && CHECK=1

if [ "$CHECK" = "1" ]; then
  python3 "$HERE/make_tables.py" --quiet >/dev/null || exit 1
  python3 "$HERE/paste_tables.py" --check
  exit $?
fi

echo "=== 1/3  make_tables.py ==="
python3 "$HERE/make_tables.py" --quiet || exit 1
echo "=== 2/3  paste_tables.py ==="
python3 "$HERE/paste_tables.py" || exit 1
echo "=== 3/3  splice_report.py ==="
python3 "$HERE/splice_report.py" || exit 1

echo
echo "=== certificates on disk ==="
printf '%-4s %-10s %-24s %s\n' "p" "precision" "verdict" "file"
rc=0
for P in $PRIMES; do
  F="$DATA/cert_$P.out"
  if [ -f "$F" ]; then
    K="$(sed -n 's/^c_2 precision *: O(p^\([0-9][0-9]*\)).*/\1/p' "$F" | head -1)"
    V="$(sed -n 's/^RESULT  *: //p' "$F" | head -1)"
    printf '%-4s %-10s %-24s %s\n' "$P" "O($P^${K:-?})" "${V:-?}" "cert_$P.out"
    case "$V" in "ALL CHECKS PASS") ;; *) rc=1 ;; esac
  else
    printf '%-4s %-10s %-24s %s\n' "$P" "--" "not computed (a gap)" "--"
  fi
done

echo
echo "=== files needing a human, if any ==="
found=0
for F in "$DATA"/cert_*.FAILED.out; do
  [ -e "$F" ] || continue
  found=1; rc=1
  echo "  FAILED     $(basename "$F")   -- a run whose checks did not pass; read it."
done
for F in "$DATA"/cert_*.superseded.out; do
  [ -e "$F" ] || continue
  found=1
  echo "  superseded $(basename "$F")   -- passed, but LESS precise than the kept"
  echo "                                    certificate.  Harmless; delete when read."
done
[ "$found" = "0" ] && echo "  none"

echo
echo "=== stop-the-line check (from the generated tables) ==="
if grep -q "STOP THE LINE" "$DATA/tables.md"; then
  echo "  *** STOP THE LINE *** -- see code/data/tables.md.  Do not proceed;"
  echo "  a computed value disagrees with Appendix B, or a height side disagrees"
  echo "  with an L-side.  This is NOT what a missing certificate looks like."
  rc=1
else
  grep -A3 "^Overall:" "$DATA/tables.md" | sed 's/^/  /'
fi
exit $rc
