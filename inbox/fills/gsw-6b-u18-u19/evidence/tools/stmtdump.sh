#!/usr/bin/env bash
# StmtDump (gsw-6b-u18-u19; the gsw-6b-u12 tool adapted to two owned files): each owned file's text
# at REV (the base or HEAD) followed by `#check` of its targets with full names, compiled as a
# scratch module through scripts/lean_check_tree.sh; the info lines, stripped of positions, are the
# dump. With REV = HEAD a third module dumps the new public helper.
# usage: stmtdump.sh REV TAG
set -e
cd /work/tcslib
G=TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW
N=TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
export PATH=$HOME/.elan/bin:$PATH
mkdir -p scratch/stmt /work/deliv/evidence/stmt
dump() { # key file names...
  local key=$1 f=$2; shift 2
  local P=scratch/stmt/StmtDump_${key}_$TAG
  git show "$REV:$f" > $P.lean
  { echo; echo 'set_option pp.fullNames true'; echo 'set_option pp.funBinderTypes true'
    for n in "$@"; do echo "#check @$N.$n"; done; } >> $P.lean
  bash scripts/lean_check_tree.sh $P > /work/deliv/evidence/stmt/StmtDump-${key}-$TAG.log 2>&1 || true
  python3 -I - "/work/deliv/evidence/stmt/StmtDump-${key}-$TAG" <<'EOP'
import re, sys
t = open(sys.argv[1] + '.log').read()
t = re.sub(r'^\S+\.lean:\d+:\d+: (info|warning): ', r'\1: ', t, flags=re.M)
open(sys.argv[1] + '.stripped', 'w').write(t)
EOP
}
REV=$1; TAG=$2
dump PolyRatio $G/PolyRatio.lean bootRatio_le_poly decrypt_fheEval_of_ratio decrypt_leveledEval_of_ratio
dump Asymptotic $G/Asymptotic.lean indCPA_of_dlweAssumption leveledINDCPA_of_dlweAssumption
if [ "$REV" != "bff0567b6c4b6b724c8fd20ff3ef92258eb3fc9d" ]; then
  P=scratch/stmt/StmtDump_helper_$TAG
  { echo "import $N.PolyRatio"; echo; echo 'set_option pp.fullNames true'
    echo 'set_option pp.funBinderTypes true'; echo "#check @$N.Parameters.ofFamily_columns_le"; } > $P.lean
  bash scripts/lean_check_tree.sh $P > /work/deliv/evidence/stmt/StmtDump-helper-$TAG.log 2>&1 || true
fi
