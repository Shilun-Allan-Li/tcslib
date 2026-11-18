#!/usr/bin/env bash
# All seal runs of gsw-6b-u13 (C6), at most 3 Lean processes at once (xargs -P 3), each job its own
# jsonl/out under evidence/seals/runs/; skips jobs already recorded. Variants: A = PolyExpr.eval
# excluded as notation, B = sealed; strict / coe (projection coercions excluded). coe-A canonical.
set -u
WT=/workspace/u13; T=/workspace/u13-tools; R=/workspace/exchange/inbox/fills/gsw-6b-u13/evidence/seals/runs
mkdir -p $R
F=TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/DecryptFormula.lean
jobs() {
  for v in Ac As Bc Bs; do
    flags=""; case $v in A*) flags="--eval-open";; esac; case $v in *c) flags="$flags --coe-open";; esac
    echo "head $v $flags|$F"
    echo "base $v $flags --as=$F|lean_proof/u13/base/DecryptFormulaBase.lean"
    for c in CtlUnfoldOwn CtlUnfoldScheme CtlCoe CtlReader; do echo "ctl-$c $v $flags|lean_proof/u13/ctl/$c.lean"; done
  done
}
run() {
  spec="${1%%|*}"; src="${1#*|}"
  set -- $spec; kind=$1; v=$2; shift 2
  tag="${kind%%-*}$v"; out=$R/$kind-$v.jsonl
  [ -s "$out" ] && exit 0
  cd $WT && python3 -I $T/seal_run.py $WT $tag $out "$@" "$src"
}
export -f run; export WT T R
jobs | xargs -P 3 -I{} bash -c 'run "$@"' _ {}
echo SEAL-JOBS-DONE
