#!/bin/bash
# run.sh -- the control on the normalisation at the end of ssec:scan: the two
# sides of eq:padicbsd for E : y^2 = x^3 - D x, computed at a split ordinary p
# by disjoint methods and compared digit for digit.
#
#   ./run.sh <p> <n> [precT] [cap_seconds]
#   D=-39 ./run.sh 17 4
#
# The curve is the environment variable D, default 56; the saturated
# Mordell-Weil basis is read from ../data/family_bases.txt, and is that of
# tab:testbed for D = 56.  EXPECT_V is passed through to check_agreement.py and
# is the expected v_p(c_2(p)) of C6, default 0.
#
# Produces  ../data/cert_<p>.out for D = 56 and ../data/cert_D<D>_p<p>.out
# otherwise, containing, verbatim and in this order:
#   0. a header: date, host, exact commands, software versions;
#   1. ../gp/regulator.gp -- Reg_p and the height side by PARI/GP (implementation 1)
#   2. regulator.sage    -- Reg_p and the height side by Sage     (implementation 2)
#   3. certificates.sage -- L_p(E,T) by modular symbols at the level of E, the
#                           Stein-Wuthrich truncation bound achieved, v_p(c_2(p)),
#                           the digits of c_2(p), lambda_an / mu_an, and the
#                           digit-for-digit comparison of the two sides of
#                           eq:padicbsd;
#   4. check_agreement.py-- mechanical cross-checks C1-C7 over the MACHINE lines
#                           emitted by steps 1-3: the two Reg_p implementations,
#                           the Gram-determinant saturation check, the match
#                           between the two sides of eq:padicbsd, the L-side
#                           certificate v_p(c_2(p)) = 0, and the optional
#                           corroboration check against an LMFDB table.
#
# ATOMICITY.  Everything runs in a private scratch directory (a copy of the four
# scripts, so that concurrent runs at different primes cannot race on Sage's
# `<script>.sage.py` preparse artefact), and the result is moved into
# ../data/ only at the end:
#     step 4 fails            -> ../data/cert_<p>.FAILED.out
#     step 4 passes, more or
#       equal certified digits -> ../data/cert_<p>.out   (replaces)
#     step 4 passes, but FEWER
#       certified digits       -> ../data/cert_<p>.superseded.out
# In the last two cases an existing good ../data/cert_<p>.out is kept unless the new
# run is at least as precise, so neither a long ambitious run that hits its cap NOR a
# cheap low-n re-run can take away digits that have already been earned.  Precision is
# compared on the k in "c_2 precision : O(p^k)", the truncation bound actually
# achieved.  Consequence: the runner is safe to re-run at any n, in any order, any
# number of times.
#
# CAPS.  `timeout` is not on the local macOS PATH, so the cap is enforced inside
# Sage by alarm(): certificates.sage takes cap_seconds as its fourth argument and
# prints "CAP HIT" and exits 2 rather than running away.  The PARI and Sage
# regulator steps are seconds and are not capped.
#
# COST.  certificates.sage sums (p-1)*p^(n-1) modular symbols and certifies
# c_2(p) modulo p^(n-1).  Each extra certified digit multiplies the cost by p;
# n = 2 already suffices for v_p(c_2(p)) = 0.

set -u

P="${1:?usage: run.sh <p> <n> [precT] [cap_seconds]}"
N="${2:?usage: run.sh <p> <n> [precT] [cap_seconds]}"
PRECT="${3:-5}"
CAP="${4:-0}"
D="${D:-56}"
EXPECT_V="${EXPECT_V:-0}"

HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"      # the code/ directory
GPDIR="$ROOT/gp"
DATA="$ROOT/data"
SAGE="${SAGE:-/usr/local/bin/sage}"
GP="${GP:-/opt/homebrew/bin/gp}"
if [ "$D" = "56" ]; then
  LMFDB="${LMFDB:-$DATA/lmfdb_iwasawa.txt}"
  TAG="${P}"
  G="${G:-[[8,8],[9,15]]}"
else
  LMFDB="${LMFDB:-$DATA/lmfdb_iwasawa_D${D}.txt}"
  TAG="D${D}_p${P}"
  G="${G:-$(sed -n "s/^${D}|//p" "$DATA/family_bases.txt" | head -1)}"
fi
if [ -z "$G" ]; then
  echo "run.sh: no Mordell-Weil basis for D = $D in $DATA/family_bases.txt;" >&2
  echo "        set G=\"[[x1,y1],[x2,y2]]\" in the environment." >&2
  exit 2
fi
export D G EXPECT_V

# Repository-relative form of $LMFDB, for the header: the header is committed
# with the output and must not record one machine's absolute paths.
LMFDB_SHOW="$LMFDB"
case "$LMFDB" in "$ROOT"/*) LMFDB_SHOW="code/${LMFDB#"$ROOT"/}" ;; esac

# Every interpreter is checked before anything is written, so that a missing one
# reports itself instead of leaving a truncated output file behind.
have() { [ -x "$1" ] || command -v "$1" >/dev/null 2>&1; }
MISSING=0
if ! have "$GP"; then
  echo "run.sh: PARI/GP not found at '$GP'." >&2
  echo "        Set GP=/path/to/gp, or install PARI/GP; ../build.sh prints the" >&2
  echo "        install command for this platform." >&2
  MISSING=1
fi
if ! have "$SAGE"; then
  echo "run.sh: SageMath not found at '$SAGE'." >&2
  echo "        Set SAGE=/path/to/sage, or install SageMath; ../build.sh prints" >&2
  echo "        the install command for this platform.  Sage is needed for the" >&2
  echo "        L-side only; the PARI scripts run without it." >&2
  MISSING=1
fi
if ! have python3; then
  echo "run.sh: python3 not found on PATH." >&2
  MISSING=1
fi
for f in "$GPDIR/regulator.gp" "$HERE/regulator.sage" "$HERE/certificates.sage" \
         "$HERE/check_agreement.py"; do
  [ -f "$f" ] || { echo "run.sh: missing script $f" >&2; MISSING=1; }
done
[ "$MISSING" -eq 0 ] || exit 2

mkdir -p "$DATA"
WORK="$(mktemp -d "${TMPDIR:-/tmp}/cert_${TAG}_XXXXXX")"
cp "$GPDIR/regulator.gp" "$HERE/regulator.sage" "$HERE/certificates.sage" \
   "$HERE/check_agreement.py" "$WORK/"
TMPOUT="$WORK/cert_${TAG}.out"

{
  echo "==============================================================================="
  echo "eq:padicbsd CONTROL -- D = $D , p = $P"
  echo "E : y^2 = x^3 - ${D}x    Mordell-Weil basis $G"
  echo "==============================================================================="
  echo "date            : $(date -u '+%Y-%m-%d %H:%M:%S UTC')"
  echo "host            : $(hostname)  $(uname -srm)"
  echo "sage            : $SAGE  --  $($SAGE --version 2>&1 | head -1)"
  echo "gp              : $GP  --  PARI/GP $(echo 'print(version())' | $GP -q 2>/dev/null | tail -1)"
  echo "python3         : $(python3 --version 2>&1)"
  echo "generated by    : D=$D EXPECT_V=$EXPECT_V code/sage/run.sh $P $N $PRECT $CAP"
  echo "commands run    : (code/gp/regulator.gp and code/sage/*, copied to a scratch dir)"
  echo "    P=$P NPREC=14 gp -q regulator.gp"
  echo "    sage regulator.sage $P 14"
  echo "    sage certificates.sage $P $N $PRECT $CAP"
  echo "    python3 check_agreement.py $P cert_${P}.out $LMFDB_SHOW"
  echo "-------------------------------------------------------------------------------"
  echo
  echo "=== STEP 1/4 : Reg_p, implementation 1 of 2 -- PARI/GP ellpadicregulator ==="
  ( cd "$WORK" && P="$P" NPREC=14 "$GP" -q regulator.gp 2>&1 ); echo "exit status     : $?"
  echo
  echo "=== STEP 2/4 : Reg_p, implementation 2 of 2 -- Sage padic_regulator ==="
  ( cd "$WORK" && "$SAGE" regulator.sage "$P" 14 2>&1 ); echo "exit status     : $?"
  echo
  echo "=== STEP 3/4 : L-side, modular symbols by eclib (Stein-Wuthrich) ==="
  ( cd "$WORK" && "$SAGE" certificates.sage "$P" "$N" "$PRECT" "$CAP" 2>&1 ); echo "exit status     : $?"
  echo
} > "$TMPOUT" 2>&1

# Step 4 reads the file written so far and appends its verdict to it.
{
  echo "=== STEP 4/4 : mechanical cross-checks (check_agreement.py) ==="
  EXPECT_V="$EXPECT_V" python3 "$WORK/check_agreement.py" "$P" "$TMPOUT" "$LMFDB" 2>&1
  RC=$?
  echo "exit status     : $RC"
  echo
  echo "=== END p = $P ==="
} >> "$TMPOUT" 2>&1

# Number of certified base-p digits of c_2, i.e. the k in "c_2 precision : O(p^k)".
# Empty if absent.
digits_of() {
  [ -f "$1" ] || { echo ""; return; }
  sed -n 's/^c_2 precision *: O(p^\([0-9][0-9]*\)).*/\1/p' "$1" | head -1
}

CERT="$DATA/cert_${TAG}.out"
NEWK="$(digits_of "$TMPOUT")"
OLDK="$(digits_of "$CERT")"

if ! grep -q "^RESULT            : ALL CHECKS PASS" "$TMPOUT"; then
  mv "$TMPOUT" "$DATA/cert_${TAG}.FAILED.out"
  echo "FAIL       -> $DATA/cert_${TAG}.FAILED.out   (existing cert_${TAG}.out untouched)"
elif [ -z "$NEWK" ]; then
  # Checks passed but the precision line is unreadable: refuse to touch a good file.
  mv "$TMPOUT" "$DATA/cert_${TAG}.FAILED.out"
  echo "FAIL       -> $DATA/cert_${TAG}.FAILED.out   (checks passed but c_2 precision unparseable;"
  echo "              existing cert_${TAG}.out untouched)"
elif [ -z "$OLDK" ]; then
  mv "$TMPOUT" "$CERT"
  echo "PASS  new  -> $CERT   (O(${P}^${NEWK}), no previous certificate)"
elif [ "$NEWK" -gt "$OLDK" ]; then
  mv "$TMPOUT" "$CERT"
  echo "PASS  up   -> $CERT   (O(${P}^${OLDK}) -> O(${P}^${NEWK}))"
elif [ "$NEWK" -eq "$OLDK" ]; then
  mv "$TMPOUT" "$CERT"
  echo "PASS  same -> $CERT   (O(${P}^${NEWK}), reproduced at the same precision)"
else
  # A LOWER-PRECISION run must never replace a higher-precision certificate, even
  # though all its checks passed: that would silently give away certified digits.
  mv "$TMPOUT" "$DATA/cert_${TAG}.superseded.out"
  echo "PASS  low  -> $DATA/cert_${TAG}.superseded.out"
  echo "              O(${P}^${NEWK}) does not beat the O(${P}^${OLDK}) already in"
  echo "              $CERT, which is KEPT.  Nothing was lost; re-run with a larger n."
fi
grep -E "^RESULT|STOP THE LINE|CAP HIT" "$DATA/cert_${TAG}"*.out 2>/dev/null | tail -5
rm -rf "$WORK"
