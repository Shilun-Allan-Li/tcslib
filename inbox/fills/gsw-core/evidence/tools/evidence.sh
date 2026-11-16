#!/usr/bin/env bash
# Run the gsw-core delivery checks for one phase (cp1, cp2, final) on the lead tree.
# usage: evidence.sh PHASE [EXPECTED_REMOVED_COMMA_LIST] [ALLOW_SORRY_COMMA_LIST]
# Writes everything under $D/evidence/<kind>/<PHASE>/... (D = the exchange delivery dir).
# Every Lean run goes through the host lock (chk.sh / seal.py).
set -u
PHASE=$1; EXPECT=${2:-}; ALLOW=${3:-}
R=/home/user/gsw; T=/home/user/tools; B=486f44f8414c20a2d21e452c44de8b8c8d8513a0
D=/home/user/exchange/inbox/fills/gsw-core; E=$D/evidence
O=/home/user/exchange/outbox/fills/gsw-core
G=TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW
OWN="$G/Gadget.lean $G/Noise.lean $G/Scheme.lean $G/Symmetric.lean $G/Eval.lean"
cd $R
CHANGED=$(git diff --name-only $B HEAD -- TCSlib)
echo "phase $PHASE at $(git rev-parse HEAD); changed: $CHANGED"
git status --short -- TCSlib | grep . && { echo "UNCOMMITTED CHANGES in TCSlib"; exit 1; }

# 1. per-module checks of the owned modules, then the sweep of the whole order
mkdir -p $E/logs/$PHASE/modules $E/logs/$PHASE/sweep
for f in Gadget Noise Scheme Symmetric Eval; do
  $T/chk.sh $R $G/$f $E/logs/$PHASE/modules/$f.log
done | tee $E/logs/$PHASE/modules.txt
( while read -r m; do
    $T/chk.sh $R "$m" "$E/logs/$PHASE/sweep/$(echo $m | tr / _).log" || echo "SWEEP-FAIL $m"
  done < $O/order.txt ) | tee $E/logs/$PHASE/sweep.txt
echo "sweep: $(wc -l < $E/logs/$PHASE/sweep.txt) modules, $(grep -c ' errors=0 ' $E/logs/$PHASE/sweep.txt) with 0 errors, $(grep -c SWEEP-FAIL $E/logs/$PHASE/sweep.txt) failed" | tee -a $E/logs/$PHASE/sweep.txt

# 2. admissions
mkdir -p $E/sorries
python3 -I $T/sorries.py $R $E/logs/$PHASE/sweep $O/base-sorries.txt $O/order.txt \
  ${EXPECT:+--expect-removed $EXPECT} | tee $E/sorries/$PHASE.txt

# 3. axioms and dependency trace
mkdir -p $E/axioms/$PHASE probes/axioms-$PHASE
cp $T/axioms_probe.lean.txt probes/axioms-$PHASE/AxiomsProbe.lean
cp $T/axioms_probe.lean.txt $E/axioms/$PHASE/AxiomsProbe.lean
$T/chk.sh $R probes/axioms-$PHASE/AxiomsProbe $E/axioms/$PHASE/AxiomsProbe.log
python3 -I $T/axioms_report.py $E/axioms/$PHASE/AxiomsProbe.log $O/base-sorries.txt \
  ${ALLOW:+--allow-sorry $ALLOW} | tee $E/axioms/$PHASE/report.txt

# 4. headers (+ controls), width, clash
mkdir -p $E/headers/$PHASE $E/width $E/clash
python3 -I $T/headers.py $B $R $OWN > $E/headers/$PHASE/headers.txt; tail -1 $E/headers/$PHASE/headers.txt
for f in $OWN; do python3 -I $T/headers.py --controls $B $R $f; done > $E/headers/$PHASE/controls.txt
grep -c "CONTROLS PASS" $E/headers/$PHASE/controls.txt
python3 -I $T/width.py $OWN $CHANGED | tee $E/width/$PHASE.txt | tail -1
python3 -I $T/clash.py $B $R $OWN > $E/clash/$PHASE.txt; tail -1 $E/clash/$PHASE.txt

# 5. explicit-unfold scan (Lean-resolved)
rm -rf ./probes/unfold-$PHASE
python3 -I $T/unfold_scan.py prepare probes/unfold-$PHASE $R $OWN
for f in Gadget Noise Scheme Symmetric Eval; do
  $T/chk.sh $R probes/unfold-$PHASE/UnfoldScan$f probes/unfold-$PHASE/UnfoldScan$f.log
done
python3 -I $T/unfold_scan.py report probes/unfold-$PHASE > probes/unfold-$PHASE/report.txt
tail -1 probes/unfold-$PHASE/report.txt
mkdir -p $E/unfold; rm -rf "${E:?}"/unfold/$PHASE; cp -r probes/unfold-$PHASE $E/unfold/$PHASE

# 6. seals of every changed owned file (4 variants) and the paired controls
rm -rf ./probes/seals-$PHASE
for f in $CHANGED; do python3 -I $T/seal.py prepare probes/seals-$PHASE $PHASE $f; done
python3 -I $T/seal.py run probes/seals-$PHASE $R $R/.lake/tcslib-check-oleans \
  > probes/seals-$PHASE/run.log 2>&1
cat probes/seals-$PHASE/run.log
rm -rf ./probes/ctl-$PHASE; mkdir -p probes/ctl-$PHASE
cp $T/controls/SealControls.lean probes/ctl-$PHASE/
$T/chk.sh $R probes/ctl-$PHASE/SealControls probes/ctl-$PHASE/SealControls.unsealed.log
python3 -I $T/seal.py prepare probes/ctl-$PHASE/sealed ctl probes/ctl-$PHASE/SealControls.lean
python3 -I $T/seal.py run probes/ctl-$PHASE/sealed $R $R/.lake/tcslib-check-oleans \
  > probes/ctl-$PHASE/sealed/run.log 2>&1
python3 -I $T/ctlcheck.py probes/ctl-$PHASE/SealControls.lean \
  probes/ctl-$PHASE/SealControls.unsealed.log probes/ctl-$PHASE/sealed/results.jsonl \
  | tee probes/ctl-$PHASE/ctlcheck.txt
mkdir -p $E/seals; rm -rf "${E:?}"/seals/"${PHASE:?}" "${E:?}"/seals/controls-"${PHASE:?}"
cp -r probes/seals-$PHASE $E/seals/$PHASE; rm -rf "${E:?}"/seals/$PHASE/_olean
cp -r probes/ctl-$PHASE $E/seals/controls-$PHASE; rm -rf "${E:?}"/seals/controls-$PHASE/sealed/_olean

# 7. lint
mkdir -p $E/lint
python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography --check8b > $E/lint/lint-$PHASE.log 2>&1
python3 -I - $E/lint/lint-base.log $E/lint/lint-$PHASE.log <<'EOF' | tee $E/lint/diff-$PHASE.txt
import re, sys
def s(p):
    return {l.rstrip() for l in open(p) if re.match(r'^(FAIL|WARN)\b', l)}
b, f = s(sys.argv[1]), s(sys.argv[2])
print(f'base FAIL/WARN lines: {len(b)}; {sys.argv[2]}: {len(f)}')
print('new lines:'); [print('  + ' + x) for x in sorted(f - b)]
print('removed lines:'); [print('  - ' + x) for x in sorted(b - f)]
print(open(sys.argv[2]).read().strip().splitlines()[-1])
print('LINT DIFF ' + ('PASS' if not (f - b) else 'REVIEW'))
EOF
echo "phase $PHASE done"
