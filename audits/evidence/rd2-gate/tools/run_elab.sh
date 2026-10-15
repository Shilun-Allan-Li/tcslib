#!/usr/bin/env bash
# RD-2 statement gate: rebuild the harnesses and elaborate every proposed file, read-only
# (tools/leanelab.sh: `lean FILE`, no -o, no lake), against the oleans-f7 tree and the wt-g3
# checkout. Writes gate-rd2/elaboration.log.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
O=$S/gate-rd2; T=$S/rd2gate-tools; LOG=$O/elaboration.log
H() { python3 -I $T/mkharness.py "$@"; }
{
echo "# RD-2 statement gate — elaboration log"
echo "# checkout: wt-g3 (read-only campaign tip); olean tree: oleans-f7; toolchain: $(cat $S/wt-g3/lean-toolchain)"
echo "# command per file: bash tools/leanelab.sh wt-g3 oleans-f7 <file>   (lean <file>; no -o; no lake)"
echo "# generated: $(date -u '+%Y-%m-%dT%H:%M:%SZ')"
echo
echo "## harness construction (bodies verbatim; SHA-256 of inputs and harness)"
H $O/harness/FormulaKitEmit.harness.lean $O/FormulaKitGate.lean $O/FormulaKitEmit.lean
H $O/harness/FormulaKit.harness.lean $O/FormulaKitGate.lean $O/FormulaKitEmit.lean $O/FormulaKit.lean
H $O/harness/TQBF.harness.lean $O/FormulaKitGate.lean $O/FormulaKitEmit.lean $O/TQBF.lean
cat $O/QBF.lean $O/evidence/QBFEvidence.tail > $O/evidence/QBFEvidence.lean
cat $O/harness/TQBF.harness.lean $O/evidence/TQBFEvidence.tail > $O/evidence/TQBFEvidence.lean
echo "evidence files rebuilt: evidence/QBFEvidence.lean = QBF.lean + evidence/QBFEvidence.tail; evidence/TQBFEvidence.lean = harness/TQBF.harness.lean + evidence/TQBFEvidence.tail"
echo
echo "## SHA-256 of the proposed files and evidence files"
( cd $O && shasum -a 256 FormulaKitGate.lean FormulaKitEmit.lean FormulaKit.lean QBF.lean TQBF.lean ClassPSPACE.lean evidence/QBFEvidence.tail evidence/TQBFEvidence.tail evidence/QBFEvidence.lean evidence/TQBFEvidence.lean )
echo
for f in FormulaKitGate.lean QBF.lean ClassPSPACE.lean harness/FormulaKitEmit.harness.lean harness/FormulaKit.harness.lean harness/TQBF.harness.lean evidence/QBFEvidence.lean evidence/TQBFEvidence.lean; do
  out=$(cd $S && bash $S/tools/leanelab.sh $S/wt-g3 $S/oleans-f7 $O/$f 2>&1); rc=$?
  e=$(printf '%s\n' "$out" | grep -c ': error')
  w=$(printf '%s\n' "$out" | grep -c ": warning: declaration uses 'sorry'")
  o=$(printf '%s\n' "$out" | grep ': warning' | grep -vc "declaration uses 'sorry'")
  echo "## $f — exit $rc, errors $e, sorry warnings $w, other warnings $o"
  printf '%s\n' "$out" | sed "s|$S/||g"
  echo
done
} > $LOG 2>&1
grep '^## ' $LOG
