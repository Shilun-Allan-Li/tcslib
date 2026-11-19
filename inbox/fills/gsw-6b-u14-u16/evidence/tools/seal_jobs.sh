#!/usr/bin/env bash
# All seal runs of gsw-6b-u14-u16 (C6), at most 3 Lean processes at once (xargs -P 3), each job its
# own jsonl/out under evidence/seals/runs/; skips jobs already recorded. Variants: A = PolyExpr.eval
# excluded as notation, B = sealed; strict / coe (projection coercions excluded). coe-A canonical.
# Head: the two owned files; base: verbatim copies of the base files, recorded under the owned
# paths (--as); controls: lean_proof/u1416/ctl/*.lean.
set -u
WT=/workspace/u1416; T=/workspace/u1416-tools; R=/workspace/exchange/inbox/fills/gsw-6b-u14-u16/evidence/seals/runs
mkdir -p $R
G=TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW
jobs() {
  for v in Ac As Bc Bs; do
    flags=""; case $v in A*) flags="--eval-open";; esac; case $v in *c) flags="$flags --coe-open";; esac
    echo "head-Bootstrap $v $flags|$G/Bootstrap.lean"
    echo "head-Leveled $v $flags|$G/Leveled.lean"
    echo "base-Bootstrap $v $flags --as=$G/Bootstrap.lean|lean_proof/u1416/base/BootstrapBase.lean"
    echo "base-Leveled $v $flags --as=$G/Leveled.lean|lean_proof/u1416/base/LeveledBase.lean"
    for c in CtlUnfoldBoot CtlUnfoldBootGate CtlUnfoldLev CtlUnfoldHost CtlUnfoldLayer CtlUnfoldNoise CtlUnfoldRegev CtlReader; do
      echo "ctl-$c $v $flags|lean_proof/u1416/ctl/$c.lean"
    done
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
