#!/usr/bin/env bash
# U2 statement gate: rebuild the unit and re-run every check, fail-closed.
# Usage: bash run.sh <S> <repo> [<olean snapshot>]
#   <S>    the scratchpad (tools/leanelab.sh, the snapshot, wt-u2 for the Lean packages)
#   <repo> the tcslib clone, read-only (rev-parse, cat-file, ls-tree, hash-object without -w)
#   snapshot: default <S>/oleans-ltip3, which must be complete (its replay log's last line).
# lean only through leanelab.sh (no -o, no olean written); python3 -I; nothing outside <S>/gate-u2.
set -euo pipefail
S="$1"; REPO="$2"; OL="${3:-$S/oleans-ltip3}"; G="$S/gate-u2"; SC="$G/scripts"; W="$G/work"
LG="$G/logs"; WT="$S/wt-u2"; ELAB="$S/tools/leanelab.sh"
BASE_REV=fba93e7ecfdf15baa3b58fe275af4da8460966c6
TM=TCSlib/Complexity/TuringMachine
san() { sed "s|$G|<G>|g; s|$S|<S>|g"; }
pass=0
ok() { pass=$((pass + 1)); echo "PASS $pass: $1" | tee -a "$LG/summary.log"; }
mkdir -p "$LG" "$W"; : > "$LG/summary.log"

# ---- 0. precheck ------------------------------------------------------------------------------
[ "$(cat "$G/base/HEAD")" = "$BASE_REV" ] || { echo "precheck: base/HEAD"; exit 1; }
(cd "$G/base" && find TCSlib TCSlib.lean -type f | LC_ALL=C sort) > "$W/paths.lst"
sed "s|^|$G/base/|" "$W/paths.lst" | git -C "$REPO" hash-object --no-filters --stdin-paths > "$W/hashes.lst"
paste -d' ' "$W/hashes.lst" "$W/paths.lst" | sort -k2 > "$W/export.idx"
git -C "$REPO" ls-tree -r "$BASE_REV" TCSlib TCSlib.lean | awk '{print $3" "$4}' | sort -k2 > "$W/commit.idx"
cmp -s "$W/export.idx" "$W/commit.idx" || { echo "precheck: exported tree differs"; exit 1; }
for f in scripts/style_lint.py; do
  [ "$(git -C "$REPO" hash-object --no-filters "$G/base/$f")" = "$(git -C "$REPO" rev-parse "$BASE_REV:$f")" ] \
    || { echo "precheck: $f differs"; exit 1; }; done
[ "$(git -C "$REPO" hash-object --no-filters "$SC/copy-text-screen-v2.py")" = \
  "$(git -C "$REPO" rev-parse 186286f7:audits/evidence/retrofit/copy-text-screen-v2.py)" ] \
  || { echo "precheck: the screen script differs from 186286f7's"; exit 1; }
[ "$(git -C "$REPO" hash-object --no-filters "$G/inputs/Diagonal.p1.lean")" = \
  "$(git -C "$REPO" rev-parse "$BASE_REV:audits/evidence/diagonal-p1/tree/TCSlib/Complexity/TimeHierarchy/Diagonal.lean.txt")" ] \
  || { echo "precheck: Diagonal Part 1's landed form differs from its gate's"; exit 1; }
tail -n 1 "$S/fills/replay/replay-ltip3.log" | grep -qx "# modules=152 failed=0" \
  || { echo "precheck: oleans-ltip3 is not complete"; exit 1; }
tip=$(git -C "$REPO" rev-parse origin/complexity/arora-barak-ch3-4)
moved=$(git -C "$REPO" diff --name-only "$BASE_REV" "$tip" -- '*.lean')
{ echo "base $BASE_REV; tip $tip; snapshot $(basename "$OL") (replay log: complete)"
  echo "Lean files changed between the base and the tip: ${moved:-none}"; } > "$LG/precheck.log"
[ -z "$moved" ] || { echo "precheck: Lean files moved past the base; rebuild"; exit 1; }
ok "precheck (base blobs $(wc -l < "$W/commit.idx" | tr -d ' '), screen script, Diagonal Part 1, complete snapshot, tip Lean-equal)"

# ---- 1. the unit, rebuilt -------------------------------------------------------------------
rm -rf "$W/landed"
python3 -I "$SC/mklanded.py" "$G/base" "$G/unit" "$W/landed" | san > "$LG/mklanded.log"
diff -r "$W/landed" "$G/landed" > /dev/null
ok "the 5 landed files rebuilt by 17 asserted edits plus the new module, identical to landed/"

# ---- 2. graph, freeze, names, widths/hygiene, lint -----------------------------------------
PK=$(ls -d "$WT"/.lake/packages/*/.lake/build/lib/lean | tr '\n' ':')
python3 -I "$SC/graph2.py" "$G/base" "$G/landed" "$OL" "$PK" "$W/graph" | san > "$LG/graph.log"
cp "$W/graph/replay-order.txt" "$G/replay-order.txt"
! grep -qx "TCSlib" "$G/replay-order.txt"
ok "replay-order.txt: $(wc -l < "$G/replay-order.txt" | tr -d ' ') modules, topological, root excluded, imports covered"
python3 -I "$SC/freeze.py" "$G/base" "$G/landed" > "$LG/freeze.log"
ok "freeze of the 4 touched files (signatures byte-identical; one listed promotion)"
python3 -I "$SC/names.py" "$G/base" "$G/landed" > "$LG/names.log"
ok "names: none of the new names occurs in the base tree"
python3 -I "$SC/hygiene.py" "$G/base" "$G/landed" > "$LG/widths-hygiene.log"
ok "widths (new lines <= 100) and hygiene"
rm -rf "$W/lintroot"; mkdir -p "$W/lintroot/scripts"; cp "$G/base/scripts/style_lint.py" "$W/lintroot/scripts/"
(cd "$G/landed" && find TCSlib -type f) | while read -r f; do mkdir -p "$W/lintroot/$(dirname "$f")"; cp "$G/landed/$f" "$W/lintroot/$f"; done
LF=($TM/Build/StepBlockLoop.lean $TM/Codes2Tape.lean $TM/SelfUniversal.lean TCSlib/Complexity/TuringMachine.lean)
{ echo "## base"; (cd "$G/base" && python3 -I scripts/style_lint.py "${LF[@]}" 2>&1 || true)
  echo "## landed"; (cd "$W/lintroot" && python3 -I scripts/style_lint.py "${LF[@]}" $TM/UniversalK.lean 2>&1 || true); } > "$LG/lint.log"
b=$(sed -n '/^## base/,/^## landed/p' "$LG/lint.log" | grep -c ': ' || true)
l=$(sed -n '/^## landed/,$p' "$LG/lint.log" | grep -c ': ' || true)
[ "$b" = "$l" ] || { echo "lint: findings $b -> $l"; exit 1; }
ok "style_lint: no new finding (base $b, landed $l: the pre-existing Codes2Tape heading)"

# ---- 3. elaborations --------------------------------------------------------------------------
rm -rf "$W/cut" "$W/out"; mkdir -p "$W/out"
python3 -I "$SC/mkcuts.py" "$G/base" "$G/landed" "$G/inputs/Diagonal.p1.lean" "$G/probes" "$W/cut" | san > "$LG/cutfiles.log"
elab() { bash "$ELAB" "$WT" "$OL" "$W/cut/$1.lean" > "$W/out/$1.out" 2>&1 \
  || { echo "elaboration of $1 exited nonzero"; san < "$W/out/$1.out" | head -40; exit 1; }; }
CK() { python3 -I "$SC/check_diag.py" "$W/cut/$1.lean" "$W/out/$1.out" "$2" >> "$LG/elaboration.log" \
  || { echo "check of $1 failed"; tail -20 "$LG/elaboration.log"; exit 1; }; }
: > "$LG/elaboration.log"
SB=Turing.StepBlock; U3=exists_selfStartupTMK,exists_selfUniversalK,universalK
for f in StepBlockLoop.check Codes2Tape.check UniversalK.cut SelfUniversal.cut SelfUniversal.base \
         TuringMachine.cut U2Consumer.cut CodeSimulator.base CodeSimulator.cut; do
  elab "$f"; echo "## $f" >> "$LG/elaboration.log"; done
CK StepBlockLoop.check "sorried=exists_forwardLoopTM;std=$SB.loopTM,$SB.hostedLoopTM,$SB.loopTM_run,$SB.hostedLoopTM_run,$SB.hostedLoop_read,$SB.forwardLoopCfg;sorryAx=$SB.exists_forwardLoopTM"
CK Codes2Tape.check "sorried=;std=Turing.Code2TM,Turing.Code2TM.toFinTM,Turing.Code2TM.serialize,Turing.MachineCode2,Turing.MachineCode2.decode_encode,Turing.EffectiveMachineCode2,Turing.exists_effectiveMachineCode2,Turing.UniformMachineCode2,Turing.Code2TM.serialize_eq_serializeK;sorryAx=Turing.exists_uniformMachineCode2"
CK UniversalK.cut "sorried=$U3;std=Turing.EffectiveCodeK,Turing.EffectiveCodeK.toFinTM,Turing.EffectiveCodeK.ofSerialize,Turing.EffectiveMachineCode.toK,Turing.EffectiveMachineCode2.toK,Turing.EffectiveMachineCode.toK_toFinTM,Turing.EffectiveMachineCode2.toK_toFinTM,Turing.EffectiveMachineCode.toK_machine,Turing.EffectiveMachineCode2.toK_machine;sorryAx=Turing.exists_selfStartupTMK,Turing.exists_selfUniversalK,Turing.universalK"
CK SelfUniversal.cut "sorried=$U3;std=;sorryAx=Turing.exists_selfStartupTM,Turing.exists_selfUniversal"
CK SelfUniversal.base "sorried=exists_selfStartupTM,exists_selfUniversal;std=;sorryAx=Turing.exists_selfStartupTM,Turing.exists_selfUniversal"
CK TuringMachine.cut "sorried=$U3;std=;sorryAx="
CK U2Consumer.cut "sorried=$U3;std=Turing.U2ConsumerProbe.exists_code2TM,Turing.U2ConsumerProbe.logOverhead_mul_le;sorryAx=Turing.U2ConsumerProbe.twoTapeSelfSimulator,Turing.U2ConsumerProbe.time_hierarchy_log,Turing.U2ConsumerProbe.time_hierarchy_book"
python3 -I "$SC/check_vs_base.py" "$W/cut/CodeSimulator.base.lean" "$W/out/CodeSimulator.base.out" \
  "$W/cut/CodeSimulator.cut.lean" "$W/out/CodeSimulator.cut.out" exists_forwardLoopTM >> "$LG/elaboration.log"
for f in StepBlockLoop.check Codes2Tape.check UniversalK.cut SelfUniversal.cut U2Consumer.cut; do
  { echo; echo "### raw output: $f"; san < "$W/out/$f.out"; } >> "$LG/axioms.log"; done
ok "elaboration: 9 files, 0 errors, sorry warnings exactly at the sorried contracts, axioms as classified"

# ---- 4. negative controls, screens -----------------------------------------------------------
bash "$SC/negctl.sh" "$S" "$G" "$OL" | san > "$LG/negative-controls.log"
[ "$(grep -c -- "— PASS" "$LG/negative-controls.log")" = 7 ] || { echo "negative controls"; exit 1; }
ok "negative controls: 7, each check failing on its broken input"
bash "$SC/screens.sh" "$G" > /dev/null
{ python3 -I "$SC/screendelta.py" "$LG/screen-before.txt" "$LG/screen-after.txt"
  python3 -I "$SC/pairdiff.py" "$LG/screen-after.txt" "$LG/screen-before.txt"; } > "$LG/screen-delta.log"
grep -q "new 4 (cross-file 2); gone 0" "$LG/screen-delta.log"
ok "copy-text screen (v2): exactly the 4 disclosed new pairs (the scheme-field mirror, the two one-line views)"

echo "TOTAL: $pass checks PASS" | tee -a "$LG/summary.log"
(cd "$G" && find landed unit inputs probes scripts logs audits replay-order.txt BUNDLE-FILES.txt -type f \
   ! -name '*.pyc' | LC_ALL=C sort | xargs shasum -a 256) > "$G/SHA256SUMS"
echo "wrote SHA256SUMS"
