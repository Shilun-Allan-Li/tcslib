#!/usr/bin/env bash
# MIG-1 statement gate, round 2: rebuild every artifact and rerun every check; read-only on the
# worktree, the olean snapshot and the MIG-0b landing set.
#
# Usage: bash runall.sh <worktree> <olean snapshot> <leanelab.sh> <gate dir> <MIG-0b landing root>
# Environment: LOGPFX (default mig1-statements-r2) and LOGDIR (default <gate dir>/logs; an
# absolute path) name the logs $LOGDIR/$LOGPFX-*.log.
#
# Round 2 (finding 2): `set -euo pipefail`; every input is checked before anything is written
# (exit 2 if one is missing); `elab` returns the elaborator's status; every check compares its
# measured result with scripts/expected-r2.json and records a failure on any deviation; the
# identity negative control must give exactly its three expected failures (identity.py exits
# with the number of failures); the run exits 1 if any check failed, 0 otherwise, and says which.
set -euo pipefail
if [ "$#" -ne 5 ]; then
  echo "usage: bash runall.sh <worktree> <oleans> <leanelab.sh> <gate dir> <MIG-0b landing root>" >&2
  exit 2
fi
WT="$1"; OL="$2"; ELAB="$3"; G="$4"; M0B="$5"
LOGPFX="${LOGPFX:-mig1-statements-r2}"
LOGDIR="${LOGDIR:-$4/logs}"
P="python3 -I"

# ---- 0. Inputs (nothing is written before this passes) -----------------------------------
missing=()
need_dir() { [ -d "$1" ] || missing+=("$1 (directory)"); }
need_file() { [ -s "$1" ] || missing+=("$1"); }
need_dir "$WT"; need_dir "$OL"; need_file "$ELAB"; need_dir "$G"; need_dir "$M0B"
need_file "$WT/.git"; need_file "$WT/lean-toolchain"
need_file "$M0B/TCSlib/Complexity/TuringMachine/Finite.lean"
for d in parts probe-parts bridge-parts; do need_dir "$G/$d"; done
for f in 00-header 01-Simulation 02-Composition 03-Wrappers 04-Encoding 05-TimeConstructible \
         06-Loop 07-Primitives 08-Catalog; do need_file "$G/parts/$f.lean"; done
need_file "$G/probe-parts/90-SpecProbe.lean"; need_file "$G/probe-parts/91-SpecProbe2.lean"
need_file "$G/bridge-parts/00.lean"
for f in build_unit.py mkshim.py decls.py renames.json wraps.json cutcheck.py identity.py \
         identity-manifest.json gatenames.py namescreen.py namescreen_extra.py widths.py \
         campaign_style_lint.py consumers.py importgraph.py region.py region_r2.py fates.json \
         fates_r2.json fatetable.py r3check.py rowtotals.py build_overlay.py overlaycheck.py \
         retarget_checks.py retarget.py srecords.py expected-r2.json; do need_file "$G/scripts/$f"; done
for f in moved-names.json consumer-names.json r3-retirement.tsv deletion-plan-r1.tsv \
         consumers-r1.json r1/MIG1Statements.lean.txt r1/SpecProbe-tail.lean.txt \
         r1/BridgeProbe.lean.txt r1/AxiomProbe-tail.lean.txt; do need_file "$G/data/$f"; done
if [ "${#missing[@]}" -gt 0 ]; then
  printf 'runall.sh: missing input: %s\n' "${missing[@]}" >&2
  exit 2
fi

cd "$G"
mkdir -p "$LOGDIR" cuts work probes lintdir overlay checks
EXP=scripts/expected-r2.json
LOG="$LOGDIR/$LOGPFX-elaboration.log"
: > "$LOG"
FAILS=()
say() { printf '%s\n' "$*" | tee -a "$LOG"; }
fail() { FAILS+=("$1"); printf 'FAIL: %s\n' "$1" | tee -a "$LOG" >&2; }  # stderr: not into check outputs
exp() { $P -c 'import json, sys; print(json.load(open(sys.argv[1], encoding="utf-8"))[sys.argv[2]])' "$EXP" "$1"; }
expect() {  # expect <key> <measured>: compare with the expected value
  local want; want="$(exp "$1")"
  if [ "$2" == "$want" ]; then say "  ok   $1: $2"; else fail "$1: measured [$2], expected [$want]"; fi
}
count() { /usr/bin/grep -c -- "$1" "$2" || true; }
ELABSTAT=""
elab() {  # elab <file>: elaborate; sets ELABSTAT; returns the elaborator's exit status
  local out="work/$(basename "$1").out" e ne ns no
  set +e
  bash "$ELAB" "$WT" "$OL" "$G/$1" > "$out" 2>&1
  e=$?
  set -e
  ne=$(count ': error' "$out"); ns=$(count "declaration uses 'sorry'" "$out")
  no=$(( $(count ': warning' "$out") - ns ))
  ELABSTAT="exit $e; errors $ne; sorry $ns; other $no"
  say "elaborated $1 ($(wc -l < "$1" | tr -d ' ') lines): $ELABSTAT"
  return "$e"
}
run() {  # run <label> <command...>: run a check command; a nonzero status is a failure
  local e
  set +e; "${@:2}"; e=$?; set -e
  [ "$e" -eq 0 ] || fail "$1: exit status $e"
  return 0
}

say "# MIG-1 statement gate, round 2: elaboration and check log"
gitdir="$(sed -n 's/^gitdir: //p' "$WT/.git")"
say "worktree HEAD: $(cat "$gitdir/HEAD") (read from the git metadata file; no git command)"
say "olean snapshot: $OL; toolchain file: $(cat "$WT/lean-toolchain"); MIG-0b landing set: $M0B"
say ""

# ---- 1. Build ------------------------------------------------------------------------------
say "## 1. Build of the unit and the probes from their templates (scripts/build_unit.py)"
run "build unit" $P scripts/build_unit.py "$WT" parts MIG1Statements.lean --expect "$(exp templates.parts)"
run "build spec-probe tail" $P scripts/build_unit.py "$WT" probe-parts work/probe-tail.lean \
  --expect "$(exp templates.probe-parts)"
cat MIG1Statements.lean work/probe-tail.lean > probes/SpecProbe.lean
run "build bridge probe" $P scripts/build_unit.py "$WT" bridge-parts probes/BridgeProbe.lean \
  --expect "$(exp templates.bridge-parts)"
expect lines.unit "$(wc -l < MIG1Statements.lean | tr -d ' ')"
expect lines.specprobe "$(wc -l < probes/SpecProbe.lean | tr -d ' ')"
expect lines.bridgeprobe "$(wc -l < probes/BridgeProbe.lean | tr -d ' ')"
for pair in "MIG1Statements.lean:data/r1/MIG1Statements.lean.txt" "work/probe-tail.lean:data/r1/SpecProbe-tail.lean.txt" \
            "probes/BridgeProbe.lean:data/r1/BridgeProbe.lean.txt"; do
  if cmp -s "${pair%%:*}" "${pair#*:}"; then same=identical; else same=different; fi
  expect "r1identity.$(basename "${pair%%:*}")" "$same"
done
# finding 2: the builder refuses an empty template set and leaves its output untouched
mkdir -p work/empty-parts
printf 'sentinel\n' > work/refuse-target.lean
set +e; $P scripts/build_unit.py "$WT" work/empty-parts work/refuse-target.lean > work/refuse.out 2>&1
e=$?; set -e
if [ "$e" -eq 2 ] && [ "$(cat work/refuse-target.lean)" == "sentinel" ]; then
  say "  ok   build_unit.py refuses an empty template set (exit 2) and leaves its output untouched"
else fail "build_unit.py on an empty template set: exit $e, output $(head -c 40 work/refuse-target.lean)"; fi
say ""

# ---- 2. Elaboration ------------------------------------------------------------------------
say "## 2. Elaboration"
elab MIG1Statements.lean || true; expect elab.unit "$ELABSTAT"
elab probes/SpecProbe.lean || true; expect elab.specprobe "$ELABSTAT"
elab probes/BridgeProbe.lean || true; expect elab.bridgeprobe "$ELABSTAT"
say ""

# ---- 3. Cut checks -------------------------------------------------------------------------
say "## 3. Cut checks (scripts/cutcheck.py)"
CUTLOG="$LOGDIR/$LOGPFX-cutcheck.log"
mkdir -p cuts
for f in cuts/*.check.lean; do if [ -e "$f" ]; then mv "$f" "work/stale-$(basename "$f")"; fi; done
run "cutcheck.py" $P scripts/cutcheck.py MIG1Statements.lean "$WT" cuts > "$CUTLOG"
cat "$CUTLOG" >> "$LOG"
expect cut.importunion "$(head -1 "$CUTLOG")"
ncut=0
for f in cuts/*.check.lean; do
  ncut=$((ncut + 1))
  elab "$f" || true
  printf 'cut: %s -- %s\n' "$f" "$ELABSTAT" >> "$CUTLOG"
  m="$(basename "$f" .check.lean)"
  expect "cut.$m" "$ELABSTAT"
done
[ "$ncut" -eq 8 ] || fail "cut files: $ncut, expected 8"
say ""

# ---- 4. Identity and its negative control --------------------------------------------------
say "## 4. Identity (scripts/identity.py) and its negative control"
IDLOG="$LOGDIR/$LOGPFX-identity.log"
run "identity.py" $P scripts/identity.py "$WT" MIG1Statements.lean scripts/identity-manifest.json \
  work/probe-tail.lean probes/BridgeProbe.lean > "$IDLOG"
expect identity.summary "$(tail -1 "$IDLOG")"
$P - <<'EOF'
s = open('MIG1Statements.lean', encoding='utf-8').read()
for a, b in [("            controlAction .neg (some (.inr (.inr (.inl (b, true)))))",
              "            controlAction .pos (some (.inr (.inr (.inl (b, true)))))"),
             ("(prependTM w).ComputesFunInTime (fun x => w ++ x) (fun n => w.length + n + 1) := by",
              "(prependTM w).ComputesFunInTime (fun x => w ++ x) (fun n => w.length + n + 2) := by"),
             ("          | some _ => act 0 none (none, .neg) (none, .neg) none (some (ctrl 3))",
              "          | some _ => act 0 none (none, .neg) (none, .pos) none (some (ctrl 3))")]:
    assert s.count(a) == 1, a
    s = s.replace(a, b)
open('work/mutant.lean', 'w', encoding='utf-8').write(s)
EOF
set +e
$P scripts/identity.py "$WT" work/mutant.lean scripts/identity-manifest.json work/probe-tail.lean \
  probes/BridgeProbe.lean > work/identity-control.out
e=$?
set -e
expect identity.control.exit "$e"
expect identity.control.fails "$(/usr/bin/grep '^FAIL' work/identity-control.out | awk '{print $3}' | sort | tr '\n' ' ' | sed 's/ $//')"
{ echo; echo "## negative control (three single-token mutations; identity.py exit $e)"; \
  /usr/bin/grep '^FAIL' work/identity-control.out || true; } >> "$IDLOG"
say ""

# ---- 5. Axioms -----------------------------------------------------------------------------
say "## 5. Axioms (probes/AxiomProbe.lean: the unit, then #print axioms of its public declarations)"
$P scripts/gatenames.py MIG1Statements.lean --public > work/gate-public.txt
{ printf '\n/-! Axiom probe (not landed): every public declaration of the unit. -/\n\n'; \
  awk '{print "#print axioms " $4}' work/gate-public.txt; } > work/axiom-tail.lean
cat MIG1Statements.lean work/axiom-tail.lean > probes/AxiomProbe.lean
# the round-1 tail differs only in its header comment: compare the #print lines
if [ "$(/usr/bin/grep '^#print axioms' work/axiom-tail.lean)" == "$(/usr/bin/grep '^#print axioms' data/r1/AxiomProbe-tail.lean.txt)" ]; then
  same=identical; else same=different; fi
expect r1identity.axiom-tail.lean "$same"
elab probes/AxiomProbe.lean || fail "axiom probe: $ELABSTAT"
cp work/AxiomProbe.lean.out work/axioms.out
AXLOG="$LOGDIR/$LOGPFX-axioms.log"
$P - <<'EOF' > "$AXLOG"
import re
t = open('work/axioms.out', encoding='utf-8').read()
items = re.findall(r"'([^']+)' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", t, re.S)
std = {'propext', 'Classical.choice', 'Quot.sound'}
res = [(n, [a.strip() for a in ax.replace('\n', ' ').split(',') if a.strip()]) for n, _, ax in items]
print(f'declarations reported: {len(res)}')
print(f'non-standard axioms (other than propext, Classical.choice, Quot.sound, sorryAx): '
      f'{[n for n, a in res if set(a) - std - {"sorryAx"}]}')
print(f'with sorryAx: {sum(1 for _, a in res if "sorryAx" in a)}; '
      f'sorry-free: {sum(1 for _, a in res if "sorryAx" not in a)}')
print()
for n, a in res:
    print(f"{n}: {', '.join(a) if a else '(none)'}")
EOF
expect axioms.summary "$(head -3 "$AXLOG" | paste -sd'|' - | sed 's/|/ | /g')"
say ""

# ---- 6. Names ------------------------------------------------------------------------------
say "## 6. Names (scripts/namescreen.py; the MIG-0b landing set by namescreen_extra.py)"
NMLOG="$LOGDIR/$LOGPFX-names.log"
$P - <<'EOF'
import json
lines = open('MIG1Statements.lean', encoding='utf-8').read().split('\n')
json.dump({l.split()[2].split('.')[-1]: i for i, l in enumerate(lines, 1)
           if l.startswith('-- @landing ')}, open('work/part-lines.json', 'w', encoding='utf-8'))
EOF
run "namescreen.py" $P scripts/namescreen.py "$WT" work/gate-public.txt data/moved-names.json "$NMLOG" \
  > work/namescreen.out
expect names.summary "$(tail -1 work/namescreen.out)"
expect names.movedclash "$(/usr/bin/grep '^CLASH' "$NMLOG" | paste -sd'|' -)"
{ echo; echo "## 6. The MIG-0b round-2 landing set ($M0B)"; \
  $P scripts/namescreen_extra.py "$M0B" work/gate-public.txt data/moved-names.json; } > work/names-m0b.out
cat work/names-m0b.out >> "$NMLOG"
expect names.mig0b "$(tail -3 work/names-m0b.out | paste -sd'|' - | sed 's/|/ | /g')"
say ""

# ---- 7. Widths and style -------------------------------------------------------------------
say "## 7. Widths and style"
$P scripts/widths.py MIG1Statements.lean probes/SpecProbe.lean probes/BridgeProbe.lean > work/widths.out
expect widths "$(tail -1 work/widths.out)"
for f in lintdir/*.lean; do if [ -e "$f" ]; then mv "$f" "work/stale-lint-$(basename "$f")"; fi; done
cp MIG1Statements.lean probes/SpecProbe.lean probes/BridgeProbe.lean lintdir/
set +e; $P scripts/campaign_style_lint.py lintdir > work/lint.out 2>&1; e=$?; set -e
tail -6 work/lint.out | tee -a "$LOG" > /dev/null
[ "$e" -eq 0 ] || fail "campaign_style_lint.py exit $e"
expect lint "$(tail -1 work/lint.out)"
say ""

# ---- 8. Consumers and replay ---------------------------------------------------------------
say "## 8. Consumers of the rows (scripts/consumers.py, rowtotals.py) and replay (importgraph.py)"
COLOG="$LOGDIR/$LOGPFX-consumers.log"
run "consumers.py" $P scripts/consumers.py "$WT" data/consumer-names.json data/consumers.json > "$COLOG"
expect consumers.total "$(tail -1 "$COLOG")"
{ echo; echo "## per row, against the round-1 measurement (data/consumers-r1.json)"; \
  $P scripts/rowtotals.py data/consumer-names.json data/consumers.json data/consumers-r1.json; } \
  > work/rowtotals.out
cat work/rowtotals.out >> "$COLOG"
expect consumers.rows53 "$(/usr/bin/grep '^rows53:' work/rowtotals.out | sed 's/ (before.*//')"
expect consumers.rows34 "$(/usr/bin/grep '^rows34:' work/rowtotals.out | sed 's/ (before.*//')"
/usr/bin/grep -E 'CHANGED|new citation|gone citation|^rows' work/rowtotals.out | tee -a "$LOG" > /dev/null
T=TCSlib.Complexity
RPLOG="$LOGDIR/$LOGPFX-replay.log"
: > "$RPLOG"
for set in "whole MIG-1 (ten files):$T.TuringMachine.Simulation $T.TuringMachine.Composition $T.TuringMachine.Build.Wrappers $T.TuringMachine.Encoding $T.ClassP.TimeConstructible $T.TuringMachine.Build.Loop $T.TuringMachine.Build.Primitives $T.TuringMachine.Build.Catalog $T.TuringMachine.Build.CertShell $T.TuringMachine.CodeSimulator" \
           "PR S (statements):$T.TuringMachine.Simulation $T.TuringMachine.Composition $T.TuringMachine.Build.Wrappers $T.TuringMachine.Encoding $T.ClassP.TimeConstructible $T.TuringMachine.Build.Loop $T.TuringMachine.Build.Primitives $T.TuringMachine.Build.Catalog" \
           "F-A:$T.TuringMachine.Composition $T.TuringMachine.Simulation $T.TuringMachine.Build.Wrappers $T.TuringMachine.Encoding $T.ClassP.TimeConstructible" \
           "F-B:$T.TuringMachine.Build.Primitives" \
           "F-C:$T.TuringMachine.Build.Loop" \
           "F-D:$T.TuringMachine.Build.Catalog $T.TuringMachine.Build.CertShell $T.TuringMachine.CodeSimulator" \
           "F-D without CodeSimulator:$T.TuringMachine.Build.Catalog $T.TuringMachine.Build.CertShell"; do
  echo "== ${set%%:*}" >> "$RPLOG"
  # shellcheck disable=SC2086
  $P scripts/importgraph.py "$WT" replay ${set#*:} >> "$RPLOG"
done
expect replay "$(/usr/bin/grep -A1 '^==' "$RPLOG" | /usr/bin/grep -v '^--' | paste - - | sed -E 's/^== (.*)\tmodules: [0-9]+; replay closure: ([0-9]+).*/\1 \2/' | paste -sd'|' - | sed 's/|/ | /g')"
expect replay.modules "$(/usr/bin/grep -m1 'modules:' "$RPLOG" | sed -E 's/modules: ([0-9]+);.*/\1/')"
say ""

# ---- 9. Deletion plan ----------------------------------------------------------------------
say "## 9. Deletion plan: round-1 classifier (reproduction) and round-2 classifier (fates_r2.json)"
DPLOG="$LOGDIR/$LOGPFX-deletion-plan.log"
mkdir -p work/region-r1 work/region-r2
run "region.py" $P scripts/region.py "$WT" work/region-r1 > work/region-r1.out
if cmp -s work/region-r1/deletion-plan.tsv data/deletion-plan-r1.tsv; then r1=yes; else r1=no; fi
expect region.r1reproduces "$r1"
run "region_r2.py" $P scripts/region_r2.py "$WT" work/region-r2 scripts/fates_r2.json > work/region-r2.out
cmp -s work/region-r2/moved-names.json data/moved-names.json || fail "moved-names.json changed"
cp work/region-r2/deletion-plan.tsv work/region-r2/deletion-plan.json data/
{ echo "# round-1 classifier at the tip: reproduces data/deletion-plan-r1.tsv byte for byte: $r1"; \
  echo; echo "# round-2 classifier"; cat work/region-r2.out; echo; \
  echo "# rows that differ from round 1"; diff data/deletion-plan-r1.tsv data/deletion-plan.tsv || true; \
  echo; echo "# fate-count table (scripts/fatetable.py)"; $P scripts/fatetable.py data/deletion-plan.json; } > "$DPLOG"
expect region.unassigned "$(/usr/bin/grep '^UNASSIGNED' work/region-r2.out)"
expect fates.total "$(tail -1 "$DPLOG")"
expect fates.modified "$(/usr/bin/grep '^Delete: modified copy' "$DPLOG")"
expect fates.prepare "$(/usr/bin/grep '^Delete: `f2_loopHost_prepare`' "$DPLOG")"
expect fates.duplicates "$(/usr/bin/grep '^Delete: duplicates' "$DPLOG")"
expect fates.absorbed "$(/usr/bin/grep '^Absorbed' "$DPLOG")"
say ""

# ---- 10. R3 sites --------------------------------------------------------------------------
say "## 10. R3 retirement sites at the tip (scripts/r3check.py)"
R3LOG="$LOGDIR/$LOGPFX-r3.log"
run "r3check.py" $P scripts/r3check.py "$WT" data/r3-retirement.tsv > "$R3LOG"
expect r3 "$(tail -1 "$R3LOG")"
say ""

# ---- 11. The Loop overlay (finding 1) ------------------------------------------------------
say "## 11. The Loop overlay: finding 1's repair, elaborated in Loop's import closure"
OVLOG="$LOGDIR/$LOGPFX-overlay.log"
cp "$WT/TCSlib/Complexity/TuringMachine/Build/Loop.lean" work/LoopTip.lean
elab work/LoopTip.lean || true
expect baseline.loop "$(printf '%s' "$ELABSTAT" | sed 's/; other.*//')"
run "build_overlay.py" $P scripts/build_overlay.py "$WT" "$M0B/TCSlib/Complexity/TuringMachine/Finite.lean" \
  MIG1Statements.lean overlay > work/build-overlay.out
elab overlay/LoopOverlay.lean || fail "overlay elaboration: $ELABSTAT"
{ echo "# Loop overlay (overlay/LoopOverlay.lean), $(cat work/build-overlay.out)"; \
  echo "baseline (the tip's Loop.lean alone): $(/usr/bin/grep 'LoopTip' "$LOG" | tail -1)"; \
  echo "overlay: $ELABSTAT"; echo; echo "## checks (scripts/overlaycheck.py)"; } > "$OVLOG"
run "overlay check" $P scripts/overlaycheck.py overlay work/LoopOverlay.lean.out work/LoopTip.lean.out \
  "$(exp overlay.prints)" > work/overlaycheck.out
cat work/overlaycheck.out >> "$OVLOG"
say "  overlay check (0 errors, 0 sorries, the tip's warnings, $(exp overlay.prints) sorry-free prints): $(tail -1 work/overlaycheck.out)"
diff -u --label tip/TCSlib/Complexity/TuringMachine/Build/Loop.lean --label overlay/part1.lean \
  "$WT/TCSlib/Complexity/TuringMachine/Build/Loop.lean" overlay/part1.lean > overlay/part1-vs-tip.diff || true
diff -u --label unit/MIG1Statements.lean:799-1488 --label overlay/part2.lean \
  overlay/unit-loop-part.lean overlay/part2.lean > overlay/part2-vs-unit.diff || true
diff -u --label mig0b/Finite.lean:386-408 --label overlay/stand-in overlay/standin-source.lean \
  overlay/standin.lean > overlay/standin-vs-mig0b.diff || true
run "overlay diff" $P scripts/overlaycheck.py diff "$WT/TCSlib/Complexity/TuringMachine/Build/Loop.lean" \
  overlay/part1.lean "$(exp overlay.diff.added)" "$(exp overlay.diff.removed)" > work/overlaydiff.out
cat work/overlaydiff.out >> "$OVLOG"
say "  part-1 diff against the tip: $(head -1 work/overlaydiff.out); $(tail -1 work/overlaydiff.out)"
$P scripts/overlaycheck.py stmts "$WT/TCSlib/Complexity/TuringMachine/Build/Loop.lean" overlay/part1.lean \
  > work/overlay-stmts.out
cat work/overlay-stmts.out >> "$OVLOG"
expect overlay.stmts "$(/usr/bin/grep '^STATEMENT CHANGED' work/overlay-stmts.out)"
expect overlay.body "$(/usr/bin/grep '^body-only' work/overlay-stmts.out)"
expect overlay.added "$(/usr/bin/grep '^added' work/overlay-stmts.out)"
{ echo; echo "## the stand-in against MIG-0b's declaration (overlay/standin-vs-mig0b.diff)"; \
  cat overlay/standin-vs-mig0b.diff; echo; echo "## part 1 against the tip's Loop.lean (overlay/part1-vs-tip.diff)"; \
  cat overlay/part1-vs-tip.diff; echo; echo "## full elaborator output of the overlay"; \
  cat work/LoopOverlay.lean.out; } >> "$OVLOG"
say ""

# ---- 12. Retarget checks and the retarget table ---------------------------------------------
say "## 12. Retarget checks (Lean) and the systematic retarget table"
RTLOG="$LOGDIR/$LOGPFX-retarget.log"
run "retarget_checks.py" $P scripts/retarget_checks.py "$WT" data/deletion-plan.json overlay/part1.lean checks \
  > work/retarget-checks.out
expect retarget.examples "$(head -1 work/retarget-checks.out)"
elab checks/RetargetChecks-r2.lean || fail "retarget checks (r2): $ELABSTAT"
r2stat="$ELABSTAT"
elab checks/RetargetChecks-tip.lean || true
tipstat="$ELABSTAT"
{ echo "# retarget checks: r2 file $r2stat; tip file (negative control) $tipstat"; cat work/retarget-checks.out; \
  echo; } > "$RTLOG"
# shellcheck disable=SC2046
run "retarget checks verdict" $P scripts/overlaycheck.py retarget checks/RetargetChecks-r2.lean \
  work/RetargetChecks-r2.lean.out checks/RetargetChecks-tip.lean work/RetargetChecks-tip.lean.out \
  $(exp retarget.tipfails) > work/retargetverdict.out
cat work/retargetverdict.out >> "$RTLOG"
say "  retarget checks: $(paste -sd';' work/retargetverdict.out | sed 's/;/; /g')"
run "retarget.py" $P scripts/retarget.py "$WT" data/deletion-plan.json MIG1Statements.lean \
  "$M0B/TCSlib/Complexity/TuringMachine/Finite.lean" checks/retarget-checks.tsv data/retarget-table.tsv \
  > work/retarget.out
{ echo; echo "# retarget table (data/retarget-table.tsv)"; cat work/retarget.out; echo; \
  echo "# full elaborator output of the tip negative control (checks/RetargetChecks-tip.lean)"; \
  /usr/bin/grep -A12 ': error' work/RetargetChecks-tip.lean.out || true; } >> "$RTLOG"
expect retarget.population "$(/usr/bin/grep '^population' work/retarget.out)"
expect retarget.classes "$(/usr/bin/grep '^classes' work/retarget.out)"
expect retarget.accessible "$(/usr/bin/grep '^accessible' work/retarget.out)"
say ""

# ---- 13. Decision 2's records ---------------------------------------------------------------
say "## 13. The eight citation specs proved at S: from which batch each is sorry-free (srecords.py)"
SRLOG="$LOGDIR/$LOGPFX-s-records.log"
run "srecords.py" $P scripts/srecords.py MIG1Statements.lean work/probe-tail.lean > "$SRLOG"
expect srecords.summary "$(head -1 "$SRLOG")"
expect srecords.batches "$(tail -8 "$SRLOG" | sed -E 's/^([^:]+):.*sorry-free from (.*)$/\1 \2/' | paste -sd'|' - | sed 's/|/ | /g')"
say ""

# ---- Result --------------------------------------------------------------------------------
if [ "${#FAILS[@]}" -eq 0 ]; then
  say "RESULT: PASS (every check matched scripts/expected-r2.json)"
  exit 0
fi
say "RESULT: FAIL (${#FAILS[@]} deviations)"
for f in "${FAILS[@]}"; do say "  - $f"; done
exit 1
