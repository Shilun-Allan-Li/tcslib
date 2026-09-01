#!/bin/zsh
# Fast shape regression for `#extract_haves_iter_decl`.
#
# WHY: a real grind is a ~40-50 minute feedback loop. Class #69 was a PARSE bug
# in the have-header split that this corpus catches in ~1 minute.
#
# SCOPE: parse/assembly-level only (header split, binders, callsite rewrite,
# naming, nesting). It does NOT reproduce semantic failures (`grind` failed,
# typeclass stuck, ladder blowup) — those need real Mathlib context.
# A green run is NECESSARY, NOT SUFFICIENT. It does not replace a window.
#
# Usage: zsh scripts/shape_regress.sh [--force]     (zsh only — uses zsh globs/arrays)
set -u
ROOT="${0:A:h}/.."
cd "$ROOT"

FIX=TCSlib/Tactics/ShapeFixtures.lean
DRIVER=TCSlib/Tactics/ShapeRegress.lean          # NOT Test.lean — never collide with a live window
OUTDIR=TCSlib/Tactics/.regress
SRC=TCSlib/Tactics/ExtractHavesFile.lean
OLEAN=.lake/build/lib/lean/TCSlib/Tactics/ExtractHavesFile.olean
DECLS=(s1_parameterized s1b_binderkinds s2_colon_newline s3_bullet \
       s4_untyped_anonymous s5_destructuring s6_nested s8_bracketed_binder_types)
# Expected have-count per shape. Asserted, not assumed: a corpus that silently
# stops finding haves (renamed decl, changed span logic) would otherwise report
# a perfect green while testing nothing.
typeset -A EXPECTED
EXPECTED=(
  s1_parameterized      8
  s1b_binderkinds       4
  s2_colon_newline      3
  s3_bullet             3
  s4_untyped_anonymous  3
  s5_destructuring      2
  s6_nested             4
  s8_bracketed_binder_types 4
)

LP=".lake/build/lib/lean"
for d in .lake/packages/*/.lake/build/lib/lean(N); do LP="$LP:$d"; done
export LEAN_PATH="$LP"
LEANBIN="$(which lean)"

# --- #69b guard -----------------------------------------------------------
# The driver imports ExtractHavesFile from its OLEAN, not from source. A stale
# olean makes this whole corpus test the OLD metaprogram and report a false
# green. Rebuild when stale — but never under a live grind.
if [ "$SRC" -nt "$OLEAN" ]; then
  if pgrep -f "bin/lean.*tcstcslib" >/dev/null 2>&1 && [ "${1:-}" != "--force" ]; then
    echo "REFUSING: $OLEAN is stale, but a lean run appears to be in flight."
    echo "Rebuilding it now could disturb that run. Wait for it, or pass --force."
    exit 2
  fi
  echo "==> ExtractHavesFile.olean is STALE — rebuilding (~22s)"
  "$LEANBIN" -o "$OLEAN" "$SRC" 2>&1 | grep -E ": error" && { echo "metaprogram FAILED to compile"; exit 1; }
else
  echo "==> olean current ($(date -r "$OLEAN" '+%m-%d %H:%M') >= src $(date -r "$SRC" '+%m-%d %H:%M'))"
fi

# --- fresh state ----------------------------------------------------------
# .progress files are cross-window memory (#66b stale-ladder). A regression run
# must start clean or a prior run's ladder history changes the routing.
rm -rf "$OUTDIR"; mkdir -p "$OUTDIR"

echo "==> building fixture olean"
"$LEANBIN" -o .lake/build/lib/lean/TCSlib/Tactics/ShapeFixtures.olean "$FIX" 2>&1 \
  | grep -E ": error" && { echo "FIXTURE does not compile"; exit 1; }

# --- driver ---------------------------------------------------------------
{
  echo "import Mathlib.Tactic.ExtractGoal"
  echo "import TCSlib.Tactics.ExtractHavesFile"
  echo "import TCSlib.Tactics.ShapeFixtures"
  echo ""
  echo "open ExtractHavesFile"
  echo ""
  for d in $DECLS; do
    echo "#extract_haves_iter_decl \"$FIX\" \"$OUTDIR/${d}_out.lean\" \"$d\""
  done
} > "$DRIVER"

echo "==> running corpus (${#DECLS} decls)"
START=$SECONDS
"$LEANBIN" "$DRIVER" > "$OUTDIR/driver.log" 2>&1
ELAPSED=$((SECONDS-START))

# --- tally ----------------------------------------------------------------
FAILED_TOTAL=0
printf "\n%-26s %6s %6s %6s %6s  %s\n" SHAPE HAVES LEMMA SWAP FAILED VERDICT
printf -- "------------------------------------------------------------------\n"
for d in $DECLS; do
  P="$OUTDIR/${d}_out.lean.progress"
  O="$OUTDIR/${d}_out.lean"
  if [ ! -f "$P" ]; then
    printf "%-26s %6s %6s %6s %6s  %s\n" "$d" - - - - "NO-RUN (driver error)"
    FAILED_TOTAL=$((FAILED_TOTAL+1)); continue
  fi
  LINE=$(grep "DONE-DECL" "$P" | tail -1)
  A=$(echo "$LINE" | sed -nE 's/.*attempts=([0-9]+).*/\1/p'); [ -z "$A" ] && A=?
  S=$(echo "$LINE" | sed -nE 's/.*succeeded=([0-9]+).*/\1/p'); [ -z "$S" ] && S=?
  F=$(grep -c "FAILED" "$P"); [ -z "$F" ] && F=0
  # 0 errors in the OUTPUT is the real gate — classes invisible to every probe
  # surface show up only here.
  if [ -f "$O" ]; then
    ERRS=$("$LEANBIN" "$O" 2>&1 | grep -c ": error")
  else
    ERRS=NO-OUTPUT
  fi
  # attempts=0 means the corpus tested NOTHING (wrong decl name, span lookup
  # missed, source moved). That is the most dangerous outcome available — it
  # looks identical to "everything passed" — so it is a HARD FAIL, and the
  # expected count is asserted per shape rather than merely "no failures".
  EXP=${EXPECTED[$d]}
  # ROUTE assertion. #69's symptom was NOT a FAILED — the extractor fell back to
  # LET-SWAPPED, which still counts as success and still yields a 0-error output.
  # A success-only gate is therefore INERT against it (cf. #31 inert verifier).
  # Every shape here must convert via real lemma extraction; any fallback to
  # let-swap is a regression in the assembly path.
  # EXTRACTED and TERM-EXTRACTED are BOTH real lemma-extraction routes (rung T
  # is the proof-term route, not a fallback). Only LET-SWAPPED is the
  # degradation #69 hid behind. Counting only " EXTRACTED" misses
  # "TERM-EXTRACTED" and flags rung T as a regression — it is not.
  EXTR=$(grep -cE '(^| )(TERM-)?EXTRACTED' "$P"); [ -z "$EXTR" ] && EXTR=0
  SWAP=$(grep -c 'LET-SWAPPED' "$P"); [ -z "$SWAP" ] && SWAP=0
  if [ "$A" = "0" ]; then
    V="FAIL — 0 haves found (tested nothing)"; FAILED_TOTAL=$((FAILED_TOTAL+1))
  elif [ "$A" != "$EXP" ]; then
    V="FAIL — found $A haves, expected $EXP"; FAILED_TOTAL=$((FAILED_TOTAL+1))
  elif [ "$SWAP" != "0" ]; then
    V="FAIL — $SWAP let-swap fallback(s); assembly path degraded"; FAILED_TOTAL=$((FAILED_TOTAL+1))
  elif [ "$EXTR" != "$EXP" ]; then
    V="FAIL — only $EXTR/$EXP via lemma extraction (EXTRACTED+TERM)"; FAILED_TOTAL=$((FAILED_TOTAL+1))
  elif [ "$A" = "$S" ] && [ "$F" = "0" ] && [ "$ERRS" = "0" ]; then
    V="PASS"
  else
    V="FAIL (errors=$ERRS)"; FAILED_TOTAL=$((FAILED_TOTAL+1))
  fi
  printf "%-26s %6s %6s %6s %6s  %s\n" "$d" "$A" "$EXTR" "$SWAP" "$F" "$V"
done
printf -- "------------------------------------------------------------------\n"
echo "elapsed ${ELAPSED}s   |   $( [ $FAILED_TOTAL -eq 0 ] && echo 'ALL SHAPES GREEN' || echo "$FAILED_TOTAL SHAPE(S) FAILING" )"
echo "(parse/assembly coverage only — a green run does NOT replace a real window)"
rm -f "$DRIVER"
exit $FAILED_TOTAL
