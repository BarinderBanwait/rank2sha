#!/bin/bash
# build.sh -- environment check and smoke test for the computations of
# "Second derivatives of p-adic L-functions and the Shafarevich-Tate group of
# rank-two CM elliptic curves".
#
#   ./build.sh
#
# It checks nothing about the manuscript.  It reports whether this machine can
# run the scripts under code/, whether the committed data files are present, and
# whether a short recomputation reproduces the committed values.  It installs
# nothing: where a tool is missing it prints the install command for the
# detected platform and leaves the decision to the reader.
#
# The whole run takes about fifteen seconds.  It exits nonzero if any check
# fails, and prints a one-line summary last.
#
# WHAT NEEDS WHAT
#   PARI/GP >= 2.17 runs everything except one item: the horizontal regulator
#   scan (code/gp/scan.gp), the Eisenstein-Kronecker invariants
#   (code/gp/deltaE.gp) and the first of the two Reg_p implementations
#   (code/gp/regulator.gp).
#   SageMath >= 10.7 is needed only for the L-side of the p = 5, 13 control on
#   the normalisation: code/sage/certificates.sage computes L_p(E,T) from eclib
#   modular symbols at level 12544, and code/sage/regulator.sage is the second
#   Reg_p implementation.  A reader without Sage can still run the scan, the
#   Eisenstein-Kronecker computation and the PARI half of the control.
#   python3 runs code/sage/check_agreement.py, which needs no library.
#
# NOT RUN HERE, because of cost:
#   code/gp/scan.gp     1611 primes, about 12 minutes on eight cores
#   code/gp/deltaE.gp   209.7 s on the reference machine
#   code/sage/run.sh    the full control; 25 s at p = 5, 5778 s at p = 13
# The smoke test recomputes a sample of what those produce and compares it with
# the committed output.

set -u

HERE="$(cd "$(dirname "$0")" && pwd)"
DATA="$HERE/data"
GPDIR="$HERE/gp"
SAGEDIR="$HERE/sage"

SAGE="${SAGE:-/usr/local/bin/sage}"
GP="${GP:-/opt/homebrew/bin/gp}"

NPASS=0
NFAIL=0
NSKIP=0

verdict() {   # verdict <PASS|FAIL|SKIP> <label> [note]
  if [ -n "${3:-}" ]; then printf '  %-54s : %s  %s\n' "$2" "$1" "$3"
  else printf '  %-54s : %s\n' "$2" "$1"; fi
}
pass() { verdict PASS "$1" "${2:-}"; NPASS=$((NPASS + 1)); }
fail() { verdict FAIL "$1" "${2:-}"; NFAIL=$((NFAIL + 1)); }
skip() { verdict SKIP "$1" "${2:-}"; NSKIP=$((NSKIP + 1)); }
info() { if [ -n "${1:-}" ]; then printf '  %s\n' "$1"; else printf '\n'; fi; }
head2() { printf '\n%s\n' "$1"; printf -- '-------------------------------------------------------------------------------\n'; }

# Resolve a tool given either as an absolute path or as a name on PATH.
resolve() {
  if [ -x "$1" ]; then echo "$1"
  elif command -v "$1" >/dev/null 2>&1; then command -v "$1"
  else echo ""
  fi
}

# ver_ge A B -- 1 if dotted-numeric A >= B, else 0.
ver_ge() {
  awk -v a="$1" -v b="$2" 'BEGIN {
    na = split(a, A, "."); nb = split(b, B, ".");
    n = (na > nb ? na : nb);
    for (i = 1; i <= n; i++) {
      x = (i <= na ? A[i] + 0 : 0); y = (i <= nb ? B[i] + 0 : 0);
      if (x > y) { print 1; exit } if (x < y) { print 0; exit }
    }
    print 1 }'
}

WORK="$(mktemp -d "${TMPDIR:-/tmp}/build_smoke_XXXXXX")"
trap 'rm -rf "$WORK"' EXIT

echo "==============================================================================="
echo "code/build.sh -- environment check and smoke test"
echo "E : y^2 = x^3 - 56x   [0,0,0,-56,0]   conductor 12544 = 2^8 * 7^2"
echo "repository: $HERE"
echo "==============================================================================="

# ---------------------------------------------------------------------------
head2 "1. Platform"
# ---------------------------------------------------------------------------
UNAME_S="$(uname -s)"
DISTRO=""
case "$UNAME_S" in
  Darwin)
    OS="macOS"
    PARI_CMD="brew install pari"
    SAGE_CMD="brew install --cask sage    (or: conda install -c conda-forge sage)"
    ;;
  Linux)
    OS="Linux"
    if [ -r /etc/os-release ]; then
      # shellcheck disable=SC1091
      DISTRO="$(. /etc/os-release && echo "${ID:-} ${ID_LIKE:-}")"
    fi
    case "$DISTRO" in
      *debian*|*ubuntu*)
        PARI_CMD="sudo apt-get install pari-gp        (2.17 is not in every release; see the note below)"
        SAGE_CMD="sudo apt-get install sagemath       (or: conda install -c conda-forge sage)"
        ;;
      *fedora*|*rhel*|*centos*)
        PARI_CMD="sudo dnf install pari-gp"
        SAGE_CMD="sudo dnf install sagemath           (or: conda install -c conda-forge sage)"
        ;;
      *arch*)
        PARI_CMD="sudo pacman -S pari"
        SAGE_CMD="sudo pacman -S sagemath"
        ;;
      *)
        PARI_CMD="your distribution's pari-gp package"
        SAGE_CMD="conda install -c conda-forge sage"
        ;;
    esac
    ;;
  *)
    OS="$UNAME_S"
    PARI_CMD="build from source: https://pari.math.u-bordeaux.fr/download.html"
    SAGE_CMD="conda install -c conda-forge sage"
    ;;
esac
info "operating system : $OS   ($(uname -srm))"
[ -n "$DISTRO" ] && info "distribution     : $DISTRO"

# ---------------------------------------------------------------------------
head2 "2. Tools"
# ---------------------------------------------------------------------------
GP_BIN="$(resolve "$GP")"
[ -n "$GP_BIN" ] || GP_BIN="$(resolve gp)"
GPVER=""
if [ -n "$GP_BIN" ]; then
  GPVER="$(echo 'print(version())' | "$GP_BIN" -q 2>/dev/null \
           | tr -d '[]' | awk -F', *' '{printf "%s.%s.%s", $1, $2, $3}')"
  case "$GPVER" in
    [0-9]*) ;;
    *) GPVER="" ;;
  esac
fi
if [ -z "$GP_BIN" ]; then
  fail "PARI/GP present" "not found"
  info "install it with:  $PARI_CMD"
  info "or set GP=/path/to/gp"
elif [ -z "$GPVER" ]; then
  fail "PARI/GP version readable" "$GP_BIN did not answer version()"
elif [ "$(ver_ge "$GPVER" 2.17)" = 1 ]; then
  pass "PARI/GP >= 2.17" "$GPVER at $GP_BIN"
else
  fail "PARI/GP >= 2.17" "found $GPVER at $GP_BIN"
  info "install a newer PARI/GP with:  $PARI_CMD"
  info "The committed outputs were produced with 2.17.2; the scripts are not"
  info "run against earlier versions."
fi
if [ "$OS" = "Linux" ]; then
  case "$DISTRO" in
    *debian*|*ubuntu*)
      info "note: if the packaged pari-gp is older than 2.17, build from source:"
      info "      https://pari.math.u-bordeaux.fr/download.html"
      ;;
  esac
fi

SAGE_BIN="$(resolve "$SAGE")"
[ -n "$SAGE_BIN" ] || SAGE_BIN="$(resolve sage)"
SAGEVER=""
if [ -n "$SAGE_BIN" ]; then
  SAGEVER="$("$SAGE_BIN" --version 2>/dev/null | sed -n 's/.*version \([0-9][0-9.]*\).*/\1/p' | head -1)"
fi
if [ -z "$SAGE_BIN" ]; then
  skip "SageMath >= 10.7" "not found"
  info "install it with:  $SAGE_CMD"
  info "or set SAGE=/path/to/sage"
  info "Sage is needed only for the L-side of the p = 5, 13 control"
  info "(code/sage/certificates.sage) and for the second Reg_p implementation"
  info "(code/sage/regulator.sage).  Everything else is PARI/GP or python3."
elif [ -z "$SAGEVER" ]; then
  skip "SageMath >= 10.7" "$SAGE_BIN did not report a version"
elif [ "$(ver_ge "$SAGEVER" 10.7)" = 1 ]; then
  pass "SageMath >= 10.7" "$SAGEVER at $SAGE_BIN"
else
  skip "SageMath >= 10.7" "found $SAGEVER at $SAGE_BIN; the outputs were made with 10.7"
  info "install 10.7 or later with:  $SAGE_CMD"
fi

PY_BIN="$(resolve python3)"
if [ -n "$PY_BIN" ]; then
  pass "python3 present" "$(python3 --version 2>&1) at $PY_BIN"
else
  fail "python3 present" "not found on PATH"
fi

# ---------------------------------------------------------------------------
head2 "3. Data files"
# ---------------------------------------------------------------------------
check_file() {   # check_file <relative path> <role>
  if [ -s "$HERE/$1" ]; then
    pass "$1" "$2, $(wc -l < "$HERE/$1" | tr -d ' ') lines"
  elif [ -f "$HERE/$1" ]; then
    fail "$1" "present but empty"
  else
    fail "$1" "missing ($2)"
  fi
}
check_file data/all_primes_vreg.txt "output of gp/scan.gp, input to gp/deltaE.gp"
check_file data/lmfdb_iwasawa.txt   "input to sage/check_agreement.py, check C7"
check_file data/deltaE_phase2.txt   "output of gp/deltaE.gp"
check_file data/cert_5.out          "output of sage/run.sh at p = 5"
check_file data/cert_13.out         "output of sage/run.sh at p = 13"
check_file data/m2_w1.out           "output of gp/m2_w1.gp at p = 5, 13, 17"
check_file data/m2_w1_2937.out      "output of gp/m2_w1.gp at p = 29, 37"
check_file data/m2_msd.out          "output of sage/m2_msd.sage"
check_file data/m2_gtest.out        "output of gp/m2_gtest.gp at p = 13"

# ---------------------------------------------------------------------------
head2 "4. Smoke test"
# ---------------------------------------------------------------------------

# S1 -- PARI reproduces v_fp(Reg_fp) = 2, at the precisions of the scan.
if [ -n "$GP_BIN" ]; then
  cat > "$WORK/vreg.gp" <<'GPEOF'
{
my(E, G, ps, allok, p, n, v);
E = ellinit([0,0,0,-56,0]);
G = [[8,8],[9,15]];
ps = [5, 13, 101];
allok = 1;
for(i = 1, #ps,
  p = ps[i];
  n = if(p < 2000, 6, if(p < 10000, 5, 4));
  v = valuation(ellpadicregulator(E, p, n, G), p);
  if(v >= n-1, n += 4; v = valuation(ellpadicregulator(E, p, n, G), p));
  print("VREG ", p, " n=", n, " v=", v);
  if(v != 2, allok = 0));
print(if(allok, "VREGOK", "VREGBAD"));
}
quit
GPEOF
  VREGOUT="$("$GP_BIN" -q "$WORK/vreg.gp" 2>&1)"
  if echo "$VREGOUT" | grep -q "^VREGOK$"; then
    pass "S1 PARI v_fp(Reg_fp) = 2 at p = 5, 13, 101" "basis (8,8),(9,15)"
  else
    fail "S1 PARI v_fp(Reg_fp) = 2 at p = 5, 13, 101" "see below"
    echo "$VREGOUT" | sed 's/^/      /'
  fi
else
  skip "S1 PARI v_fp(Reg_fp) = 2 at p = 5, 13, 101" "no PARI/GP"
fi

# S2 -- the committed scan output parses, totals 1611 lines and is complete.
if [ -n "$PY_BIN" ]; then
  cat > "$WORK/checkscan.py" <<'PYEOF'
import sys, os
data = sys.argv[1]
EXPECTED, LO, HI = 1611, 5, 30000
def sieve(limit):
    f = bytearray([1]) * limit
    f[0] = f[1] = 0
    i = 2
    while i * i < limit:
        if f[i]:
            f[i*i::i] = bytearray(len(range(i*i, limit, i)))
        i += 1
    return f
IS_PRIME = sieve(HI)
path = os.path.join(data, "all_primes_vreg.txt")
if not os.path.exists(path):
    print("MISSING all_primes_vreg.txt"); sys.exit(1)
lines = [l.split() for l in open(path).read().split("\n") if l.strip()]
bad, flagged, allp = [], 0, []
for f in lines:
    if len(f) > 2:
        flagged += 1
        continue
    p, v = int(f[0]), int(f[1])
    allp.append(p)
    if p >= HI or not IS_PRIME[p]: bad.append("%d not a prime below %d" % (p, HI))
    if p % 4 != 1:                 bad.append("%d not 1 mod 4" % p)
    if v != 2:                     bad.append("v_fp(Reg_fp) = %d at p = %d" % (v, p))
if flagged: bad.append("%d escalation-flagged line(s)" % flagged)
if len(lines) != EXPECTED:
    bad.append("total %d lines, expected %d" % (len(lines), EXPECTED))
if allp != sorted(set(allp)):
    bad.append("primes are not strictly increasing")
expected = [p for p in range(LO, HI) if IS_PRIME[p] and p % 4 == 1]
if allp != expected:
    missing = sorted(set(expected) - set(allp))[:5]
    extra = sorted(set(allp) - set(expected))[:5]
    bad.append("range incomplete: missing %r extra %r" % (missing, extra))
if bad:
    for b in bad: print("BAD %s" % b)
    sys.exit(1)
print("SCANOK %d primes, %d to %d, every split prime below %d" %
      (len(allp), min(allp), max(allp), HI))
PYEOF
  SCANOUT="$(python3 "$WORK/checkscan.py" "$DATA" 2>&1)"
  if echo "$SCANOUT" | grep -q "^SCANOK"; then
    pass "S2 committed scan parses, 1611 lines, all v = 2" "${SCANOUT#SCANOK }"
  else
    fail "S2 committed scan parses, 1611 lines, all v = 2" ""
    echo "$SCANOUT" | sed 's/^/      /'
  fi
else
  skip "S2 committed scan parses, 1611 lines, all v = 2" "no python3"
fi

# S3 -- the recorded Eisenstein-Kronecker sums match the paper's table.
EXPECTED_SUMS="invariant sums: S01 0  S02 3584  S11/A 32  S03 225792  S12/A 0  S21/A^2 -144"
if [ -s "$DATA/deltaE_phase2.txt" ]; then
  GOT="$(grep -m1 '^invariant sums:' "$DATA/deltaE_phase2.txt")"
  if [ "$GOT" = "$EXPECTED_SUMS" ]; then
    pass "S3 deltaE_phase2.txt sums match the paper's table" ""
  else
    fail "S3 deltaE_phase2.txt sums match the paper's table" ""
    info "      expected: $EXPECTED_SUMS"
    info "      found   : $GOT"
  fi
else
  fail "S3 deltaE_phase2.txt sums match the paper's table" "file missing"
fi

# S4 -- gp/regulator.gp runs and reports the expected valuations.
if [ -n "$GP_BIN" ] && [ -f "$GPDIR/regulator.gp" ]; then
  cp "$GPDIR/regulator.gp" "$WORK/"
  R4="$(cd "$WORK" && P=5 NPREC=8 "$GP_BIN" -q regulator.gp 2>&1)"
  if echo "$R4" | grep -q "^v_p(Reg_p)        : 2" \
     && echo "$R4" | grep -q "^v_p(height side)  : 0" \
     && echo "$R4" | grep -q "^MW basis          : \[8, 8\], \[9, 15\]"; then
    pass "S4 gp/regulator.gp at p = 5" "v_p(Reg_p) = 2, v_p(height side) = 0"
  else
    fail "S4 gp/regulator.gp at p = 5" ""
    echo "$R4" | tail -8 | sed 's/^/      /'
  fi
elif [ ! -f "$GPDIR/regulator.gp" ]; then
  skip "S4 gp/regulator.gp at p = 5" "script not present"
else
  skip "S4 gp/regulator.gp at p = 5" "no PARI/GP"
fi

# S5 -- sage/regulator.sage runs, and its Gram determinant equals Reg_p.
if [ -n "$SAGE_BIN" ] && [ -f "$SAGEDIR/regulator.sage" ]; then
  cp "$SAGEDIR/regulator.sage" "$WORK/"
  R5="$(cd "$WORK" && "$SAGE_BIN" regulator.sage 5 8 2>&1)"
  if echo "$R5" | grep -q "^Gram det == Reg_p : True" \
     && echo "$R5" | grep -q "^MACHINE reg.sage v=2 "; then
    pass "S5 sage/regulator.sage at p = 5" "Gram determinant equals Reg_p, v = 2"
  else
    fail "S5 sage/regulator.sage at p = 5" ""
    echo "$R5" | tail -8 | sed 's/^/      /'
  fi
elif [ ! -f "$SAGEDIR/regulator.sage" ]; then
  skip "S5 sage/regulator.sage at p = 5" "script not present"
else
  skip "S5 sage/regulator.sage at p = 5" "no SageMath"
fi

# S6 -- sage/certificates.sage at the cheapest order that certifies v_5(c_2) = 0.
if [ -n "$SAGE_BIN" ] && [ -f "$SAGEDIR/certificates.sage" ]; then
  cp "$SAGEDIR/certificates.sage" "$WORK/"
  R6="$(cd "$WORK" && "$SAGE_BIN" certificates.sage 5 2 3 0 2>&1)"
  if echo "$R6" | grep -q "^v_p(c_2(p))       : 0" \
     && echo "$R6" | grep -q "^MATCH             : YES"; then
    pass "S6 sage/certificates.sage at p = 5, n = 2" "v_5(c_2) = 0, two sides match"
  else
    fail "S6 sage/certificates.sage at p = 5, n = 2" ""
    echo "$R6" | tail -10 | sed 's/^/      /'
  fi
elif [ ! -f "$SAGEDIR/certificates.sage" ]; then
  skip "S6 sage/certificates.sage at p = 5, n = 2" "script not present"
else
  skip "S6 sage/certificates.sage at p = 5, n = 2" "no SageMath"
fi

# S7 -- the committed cert_5.out still passes its own cross-checks.
if [ -n "$PY_BIN" ] && [ -f "$SAGEDIR/check_agreement.py" ] && [ -s "$DATA/cert_5.out" ]; then
  R7="$(python3 "$SAGEDIR/check_agreement.py" 5 "$DATA/cert_5.out" "$DATA/lmfdb_iwasawa.txt" 2>&1)"
  if echo "$R7" | grep -q "^RESULT            : ALL CHECKS PASS"; then
    pass "S7 check_agreement.py on committed cert_5.out" "C1-C7 pass"
  else
    fail "S7 check_agreement.py on committed cert_5.out" ""
    echo "$R7" | tail -12 | sed 's/^/      /'
  fi
elif [ ! -f "$SAGEDIR/check_agreement.py" ]; then
  skip "S7 check_agreement.py on committed cert_5.out" "script not present"
else
  skip "S7 check_agreement.py on committed cert_5.out" "no python3 or no cert_5.out"
fi

# S8 -- the same, on the committed cert_13.out.
if [ -n "$PY_BIN" ] && [ -f "$SAGEDIR/check_agreement.py" ] && [ -s "$DATA/cert_13.out" ]; then
  R8="$(python3 "$SAGEDIR/check_agreement.py" 13 "$DATA/cert_13.out" "$DATA/lmfdb_iwasawa.txt" 2>&1)"
  if echo "$R8" | grep -q "^RESULT            : ALL CHECKS PASS"; then
    pass "S8 check_agreement.py on committed cert_13.out" "C1-C7 pass"
  else
    fail "S8 check_agreement.py on committed cert_13.out" ""
    echo "$R8" | tail -12 | sed 's/^/      /'
  fi
elif [ ! -f "$SAGEDIR/check_agreement.py" ]; then
  skip "S8 check_agreement.py on committed cert_13.out" "script not present"
else
  skip "S8 check_agreement.py on committed cert_13.out" "no python3 or no cert_13.out"
fi

# S9, S10 -- the two pure-Python verification scripts.  Both are instant and
# both check the committed data rather than recomputing it, so they belong in
# the smoke test rather than in the list of things too costly to run.
if [ -n "$PY_BIN" ] && [ -f "$SAGEDIR/verify_scan.py" ]; then
  if (cd "$SAGEDIR" && python3 verify_scan.py >"$WORK/v.txt" 2>&1); then
    pass "S9 sage/verify_scan.py on the committed scan" "1611 primes, $(grep -c "\[PASS\]" "$WORK/v.txt") checks pass, 0 fail"
  else
    fail "S9 sage/verify_scan.py on the committed scan" ""
    sed -n 's/^/      /p' "$WORK/v.txt" | grep -i fail | head -8
  fi
else
  skip "S9 sage/verify_scan.py on the committed scan" "no python3 or script not present"
fi

if [ -n "$PY_BIN" ] && [ -f "$SAGEDIR/null_model.py" ]; then
  if (cd "$SAGEDIR" && python3 null_model.py >"$WORK/n.txt" 2>&1) \
     && grep -q "NULLMODELDONE" "$WORK/n.txt"; then
    pass "S10 sage/null_model.py reproduces Section 5.4" "lambda = $(awk '/lambda = sum 1\/p/ {print $5}' "$WORK/n.txt")"
  else
    fail "S10 sage/null_model.py reproduces Section 5.4" ""
  fi
else
  skip "S10 sage/null_model.py reproduces Section 5.4" "no python3 or script not present"
fi

# ---------------------------------------------------------------------------
head2 "5. Scripts not exercised here"
# ---------------------------------------------------------------------------
for s in gp/scan.gp:"1611 primes, every split prime below 30000; produces data/all_primes_vreg.txt" \
         gp/deltaE.gp:"209.7 s on the reference machine; produces data/deltaE_phase2.txt, and must be run from code/gp, its data paths being relative" \
         sage/run.sh:"the full control; 25 s at p = 5, 5778 s at p = 13" \
         gp/excluded_set.gp:"the discharge of S_E, Section 5.1; seconds" \
         gp/timings.gp:"the four per-prime timings of Section 5.3; about 10 s" \
         gp/independence.gp:"the independence bound eq:indep, Section 6.5; 2.4 s at three precisions" \
         gp/epsilon_check.gp:"the unit character over 3018 split primes, Section 6.2; under a second" \
         gp/reconstruction_artefact.gp:"the naive-reconstruction artefact of Section 6.7; 40 s" \
         gp/s01_check.gp:"S_{0,1} at five working precisions, Section 6.3; 2.6 minutes" \
         gp/m2_w1.gp:"the bracket B(fp) of Section 6.8; 25 s at p = 5, 13, 17 and about 18 min at p = 29, 37 (W1PRIMES=29,37 W1PREC=600)" \
         gp/m2_gtest.gp:"the collapse test of lem:collapse at p = 13, Section 6.8; 2.5 minutes" \
         sage/m2_msd.sage:"kappa(p) at fourteen split primes, the modular-symbol side of Section 6.8; 3 minutes"; do
  name="${s%%:*}"; why="${s#*:}"
  if [ -f "$HERE/$name" ]; then
    info "$name  present, not run: $why"
  else
    info "$name  NOT PRESENT"
  fi
done

# Anything else under gp/ and sage/ is listed but not run: this script knows
# only the files above, and other work may add more.
EXTRA=""
for f in "$GPDIR"/*.gp "$SAGEDIR"/*.sage "$SAGEDIR"/*.py "$SAGEDIR"/*.sh; do
  [ -e "$f" ] || continue
  case "${f#"$HERE"/}" in
    gp/regulator.gp|gp/scan.gp|gp/deltaE.gp) ;;
    gp/excluded_set.gp|gp/timings.gp|gp/independence.gp) ;;
    gp/epsilon_check.gp|gp/reconstruction_artefact.gp|gp/s01_check.gp) ;;
    gp/m2_w1.gp|gp/m2_gtest.gp) ;;
    sage/regulator.sage|sage/certificates.sage|sage/check_agreement.py|sage/run.sh) ;;
    sage/verify_scan.py|sage/null_model.py|sage/m2_msd.sage) ;;
    *) EXTRA="$EXTRA ${f#"$HERE"/}" ;;
  esac
done
if [ -n "$EXTRA" ]; then
  info ""
  info "not known to build.sh, neither checked nor run:$EXTRA"
fi

# ---------------------------------------------------------------------------
printf -- '\n-------------------------------------------------------------------------------\n'
if [ "$NFAIL" -eq 0 ]; then
  echo "SUMMARY: $NPASS passed, $NFAIL failed, $NSKIP skipped -- this machine reproduces the committed values."
  exit 0
fi
echo "SUMMARY: $NPASS passed, $NFAIL failed, $NSKIP skipped -- see the FAIL lines above."
exit 1
