#!/usr/bin/env bash
#
# run.sh -- run a Magma script on the shared remote compute host, politely.
#
# Etiquette enforced here (TASK_BOARD_SERIES.md, "remote-host etiquette"):
#   * single-threaded (Magma is single-threaded unless SetNthreads is called;
#     we never call it, and we export OMP_NUM_THREADS=1 for the linear algebra)
#   * nice -n 10
#   * a hard `timeout` on every job, default 600 s
#   * every remote file lives under $HOME/fsr2_descent
#   * one job at a time (use --bg + --poll if you must leave one running)
#
# Usage:
#   ./run.sh [options] SCRIPT.m [NAME:=VALUE ...]
#
# Options:
#   -o, --out FILE     local file to receive the output (default: stdout only)
#   -d, --dep FILE     also copy FILE to the remote dir (for Magma `load`);
#                      repeatable
#   -t, --timeout SEC  hard cap, default 600
#   -j, --job NAME     remote job name (default: basename of SCRIPT minus .m)
#       --bg           launch detached on the remote and return immediately
#       --poll NAME    poll a --bg job: report whether it is still running
#       --fetch NAME   copy a finished --bg job's output back (needs -o)
#       --host H       ssh host alias (default $FSR2_HOST or "remote-host")
#
# Output files carry a three-line header recording the exact command, the
# Magma version, and the date, as required for everything in code/data/.
#
set -euo pipefail

HOST="${FSR2_HOST:-remote-host}"
RDIR="$HOME/fsr2_descent"
MAGMA="/usr/local/bin/magma"
TIMEOUT=600
OUT=""
JOB=""
MODE="run"
POLLJOB=""
DEPS=()

while [[ $# -gt 0 ]]; do
  case "$1" in
    -o|--out)     OUT="$2"; shift 2 ;;
    -d|--dep)     DEPS+=("$2"); shift 2 ;;
    -t|--timeout) TIMEOUT="$2"; shift 2 ;;
    -j|--job)     JOB="$2"; shift 2 ;;
    --host)       HOST="$2"; shift 2 ;;
    --bg)         MODE="bg"; shift ;;
    --poll)       MODE="poll"; POLLJOB="$2"; shift 2 ;;
    --fetch)      MODE="fetch"; POLLJOB="$2"; shift 2 ;;
    -h|--help)    sed -n '2,30p' "$0"; exit 0 ;;
    *)            break ;;
  esac
done

case "$MODE" in
  poll)
    ssh -o BatchMode=yes "$HOST" "
      if [ -f $RDIR/$POLLJOB.pid ] && kill -0 \$(cat $RDIR/$POLLJOB.pid) 2>/dev/null; then
        echo 'RUNNING'
      elif [ -f $RDIR/$POLLJOB.rc ]; then
        echo \"DONE rc=\$(cat $RDIR/$POLLJOB.rc)\"
      else
        echo 'UNKNOWN'
      fi
      echo '--- tail of output ---'
      tail -n 20 $RDIR/$POLLJOB.out 2>/dev/null || true"
    exit 0 ;;
  fetch)
    [[ -n "$OUT" ]] || { echo "--fetch needs -o FILE" >&2; exit 2; }
    ssh -o BatchMode=yes "$HOST" "cat $RDIR/$POLLJOB.hdr 2>/dev/null; cat $RDIR/$POLLJOB.out" > "$OUT"
    echo "fetched -> $OUT"
    exit 0 ;;
esac

SCRIPT="$1"; shift
[[ -f "$SCRIPT" ]] || { echo "no such script: $SCRIPT" >&2; exit 2; }
BASE="$(basename "$SCRIPT")"
[[ -n "$JOB" ]] || JOB="${BASE%.m}"
PARAMS=("$@")

ssh -o BatchMode=yes "$HOST" "mkdir -p $RDIR"
scp -q "$SCRIPT" "$HOST:$RDIR/$BASE"
for d in ${DEPS+"${DEPS[@]}"}; do scp -q "$d" "$HOST:$RDIR/$(basename "$d")"; done

# NOTE: `set -u` makes a bare ${PARAMS[*]} an "unbound variable" error when the
# script takes no name:=value parameters at all (bash treats an empty array as
# unset).  The ${PARAMS[*]:-} form is required, not cosmetic.
CMD="nice -n 10 timeout $TIMEOUT $MAGMA -b ${PARAMS[*]:-} $RDIR/$BASE"
DATE="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"

# three-line provenance header, written on the remote so --fetch picks it up too
MVER="$(ssh -o BatchMode=yes "$HOST" "$MAGMA -b /dev/stdin" <<'MEOF'
a,b,c := GetVersion(); printf "V%o.%o-%o", a,b,c; quit;
MEOF
)"
RHOST="$(ssh -o BatchMode=yes "$HOST" hostname)"
ssh -o BatchMode=yes "$HOST" "cat > $RDIR/$JOB.hdr" <<EOF
# command : $CMD
# magma   : $MVER
# date    : $DATE (UTC), host $RHOST, timeout ${TIMEOUT}s, nice 10
EOF

if [[ "$MODE" == "bg" ]]; then
  ssh -o BatchMode=yes "$HOST" "cd $RDIR && rm -f $JOB.rc $JOB.prog && \
    OMP_NUM_THREADS=1 nohup sh -c '$CMD > $RDIR/$JOB.out 2>&1; echo \$? > $RDIR/$JOB.rc' \
      > /dev/null 2>&1 & echo \$! > $RDIR/$JOB.pid; echo launched job=$JOB pid=\$(cat $RDIR/$JOB.pid)"
  exit 0
fi

ssh -o BatchMode=yes "$HOST" "cd $RDIR && OMP_NUM_THREADS=1 $CMD" > /tmp/.fsr2run.$$ 2>&1 || RC=$? 
RC="${RC:-0}"
{
  ssh -o BatchMode=yes "$HOST" "cat $RDIR/$JOB.hdr"
  cat /tmp/.fsr2run.$$
  if [[ "$RC" == "124" ]]; then
    echo "# EXIT   : 124 -- KILLED BY timeout AT ${TIMEOUT}s (run did not complete)"
  else
    echo "# EXIT   : $RC"
  fi
} > /tmp/.fsr2out.$$
rm -f /tmp/.fsr2run.$$
if [[ -n "$OUT" ]]; then
  mkdir -p "$(dirname "$OUT")"
  cp /tmp/.fsr2out.$$ "$OUT"
  echo "wrote $OUT (exit $RC)"
fi
cat /tmp/.fsr2out.$$
rm -f /tmp/.fsr2out.$$
exit 0
