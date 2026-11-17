#!/usr/bin/env bash
# dw10.sh <phase> [args] (dw10-seal-inventory, Claude lead, 2026-11-17): NEW driver, after bb1-sim-statements'
# drivers/rule10_stmt.sh and seal/rule10_b.sh (phases collect, seals, scan), split into phases that run per collector
# batch and per probe queue so the 434 owners can be resumed and checkpointed. Every probe runs through
# seal/runner_full.py (lean -DmaxErrors=0, no -o, per-probe flock on the host's one-Lean lock); the olean tree is the
# lead's bootstrap tree (read-only after the bootstrap). Phases:
#   collect <batch>          mkcollect.py over the batch's owners (collect/batches.tsv), one collector probe, run.
#   touched                  touched.py over all 434 owner files with the EMPTY TREE as the base revision, so every
#                            declaration of every file is NEW_FILE/touched (brief: the whole file is treated as touched).
#   genseals <batch>         mkseals_ab.py (A; B with SEAL_EVAL=1) and mkseals_coe.py (A; B) for the batch's owners,
#                            from the batch's collector log; SEAL_CHUNK (default 2000) for every probe.
#   runq <queue> <rundir>    runner_full.py over a queue of probe modules.
#   scan <batch>             scan1_g40.py (archived scan_explicit.py lexer) over the batch's owner files with touched-all.json,
#                            its kinds probe importing the batch's owners (SCAN_IMPORTS), then scan2.py.
#   scanpart <name> <files>  the same over a subset of owner files (file list <files>), the kinds probe importing only their
#                            modules: used for b2, whose single kinds probe overflowed Lean's stack (rc 134, 137k candidate names
#                            in one string literal; attempt kept as scan/b2-attempt1/); b2 runs as b2a and b2b.
set -u
W=/home/user/dw10/lead; TREE=/home/user/dw10/tree; PP=DW10Probe
E=/home/user/dw10/exch/inbox/audits/dw10-seal-inventory/evidence; T=$E/tools/seal; G=$T/review/archived-gate10-tools
B=f472accd5e000a53d0fbe02b5414435429ce4a70; EMPTY=4b825dc642cb6eb9a060e54bf8d69288fbee4904
export SEAL_CHUNK=${SEAL_CHUNK:-2000} LEAN_LOCK=${LEAN_LOCK:-/home/user/dw10/lead/.lean.lock} LAKE_PACKAGES=/home/user/dw10/lead/.lake/packages
[ "$(git -C $W rev-parse HEAD)" = "$B" ] || { echo "worktree not at base"; exit 2; }
ph=$1; shift
echo "phase $ph $* start $(date -u +%FT%TZ)"
case $ph in
collect)
  b=$1; D=$E/collect/$b; mkdir -p $D $W/$PP
  awk -F'\t' -v b=$b '$1==b{print $2}' $E/collect/batches.tsv > $D/owners.txt
  python3 -I $T/review/mkcollect.py $T/review/NmCollect.template.lean $D/owners.txt "dw10-seal-inventory collector $b" $W/$PP/Collect_$b.lean
  cp $W/$PP/Collect_$b.lean $D/Collect_$b.lean.txt
  echo $PP/Collect_$b > $D/probes.txt
  python3 -I $T/runner_full.py $W $D/probes.txt $TREE $D/runs > $D/runner.out 2>&1; echo "collector rc=$?";;
touched)
  D=$E/touched; mkdir -p $D
  python3 -I $T/review/touched.py $W $EMPTY $B $D/touched-all.json $(cut -f3 $E/collect/batches.tsv | tail -n +2) > $D/touched-all.tsv 2> $D/touched.err
  echo "touched rc=$? decls $(wc -l < $D/touched-all.tsv)";;
genseals)
  b=$1; LOG=$E/collect/$b/runs/mods/${PP}_Collect_$b.log; R=$E/seals/records; mkdir -p $R
  MODS=$(cat $E/collect/$b/owners.txt)
  python3 -I $T/review/mkseals_ab.py $G $LOG $W $B $R/strict-A/$b $PP/S SealA_ $MODS > $R/mkseals-strict-A-$b.log 2>&1 || echo FAIL strict-A
  SEAL_EVAL=1 python3 -I $T/review/mkseals_ab.py $G $LOG $W $B $R/strict-B/$b $PP/S SealB_ $MODS > $R/mkseals-strict-B-$b.log 2>&1 || echo FAIL strict-B
  python3 -I $T/review/mkseals_coe.py $G $LOG $W $B $R/coe-A/$b $PP/C SealA_ $MODS > $R/mkseals-coe-A-$b.log 2>&1 || echo FAIL coe-A
  SEAL_EVAL=1 python3 -I $T/review/mkseals_coe.py $G $LOG $W $B $R/coe-B/$b $PP/C SealB_ $MODS > $R/mkseals-coe-B-$b.log 2>&1 || echo FAIL coe-B
  tail -n 2 $R/mkseals-*-$b.log;;
scan)
  b=$1; S=$E/scan/$b; mkdir -p $S
  awk -F'\t' -v b=$b '$1==b{print $3}' $E/collect/batches.tsv > $S/files.txt
  SCAN_IMPORTS="$(cat $E/collect/$b/owners.txt | tr '\n' ' ')" python3 -I $T/scan1_g40.py $G/scan_explicit.py $W $E/touched/touched-all.json $S/items.json $W/$PP/ScanKinds_$b.lean $(cat $S/files.txt) > $S/scan1.out 2>&1; echo "scan1 rc=$?"
  cp $W/$PP/ScanKinds_$b.lean $S/ScanKinds_$b.lean.txt
  echo $PP/ScanKinds_$b > $S/order.txt
  python3 -I $T/runner_full.py $W $S/order.txt $TREE $S/runs > $S/scan-runner.out 2>&1; echo "kinds rc=$?"
  python3 -I $T/scan2.py $S/items.json $S/runs/mods/${PP}_ScanKinds_$b.log $S/explicit.json > $S/scan2.log 2>&1; echo "scan2 rc=$?";;
scanpart)
  n=$1; S=$E/scan/$n; mkdir -p $S; cp $2 $S/files.txt
  SCAN_IMPORTS="$(sed 's|\.lean$||; s|/|.|g' $S/files.txt | tr '\n' ' ')" python3 -I $T/scan1_g40.py $G/scan_explicit.py $W $E/touched/touched-all.json $S/items.json $W/$PP/ScanKinds_$n.lean $(cat $S/files.txt) > $S/scan1.out 2>&1; echo "scan1 rc=$?"
  cp $W/$PP/ScanKinds_$n.lean $S/ScanKinds_$n.lean.txt
  echo $PP/ScanKinds_$n > $S/order.txt
  python3 -I $T/runner_full.py $W $S/order.txt $TREE $S/runs > $S/scan-runner.out 2>&1; echo "kinds rc=$?"
  python3 -I $T/scan2.py $S/items.json $S/runs/mods/${PP}_ScanKinds_$n.log $S/explicit.json > $S/scan2.log 2>&1; echo "scan2 rc=$?";;
runq)
  Q=$1; RD=$2; mkdir -p $RD
  python3 -I $T/runner_full.py $W $Q $TREE $RD >> $RD/runner.out 2>&1; echo "runner rc=$?";;
esac
echo "phase $ph $* done $(date -u +%FT%TZ)"
