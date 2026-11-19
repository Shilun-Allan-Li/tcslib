#!/usr/bin/env bash
# StmtDump (gsw-6b-u15-u17; the u12 tool for two owned files): for each owned file, its text at REV
# (base or HEAD) followed by `#check` of its targets with full names, compiled as a scratch module
# through scripts/lean_check_tree.sh (its imports are unchanged modules); the info lines of both
# modules, stripped of positions, are the dump.
# usage: stmtdump.sh REV TAG
set -e
cd /workspace/gsw2/repo
D=TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW
N=TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
export PATH=$HOME/.elan/bin:$PATH
mkdir -p scratch/stmt
: > /workspace/gsw2/evidence/stmt/StmtDump-$2.log
for pair in "Circular:distAdv_fheView_noEvk_le" "LeveledSecurity:distAdv_levelHybrid_le distAdv_leveledView_le"; do
  f=${pair%%:*}; ts=${pair#*:}
  P=scratch/stmt/StmtDump_${2//-/_}_$f
  git show "$1:$D/$f.lean" > $P.lean
  printf '\nset_option pp.fullNames true\nset_option pp.funBinderTypes true\n' >> $P.lean
  for t in $ts; do echo "#check @$N.$t" >> $P.lean; done
  echo "== $f ($1)" >> /workspace/gsw2/evidence/stmt/StmtDump-$2.log
  bash scripts/lean_check_tree.sh $P >> /workspace/gsw2/evidence/stmt/StmtDump-$2.log 2>&1 || true
done
python3 -I - "$2" <<'EOP'
import re, sys
t = open(f'/workspace/gsw2/evidence/stmt/StmtDump-{sys.argv[1]}.log').read()
t = re.sub(r'^\S+\.lean:\d+:\d+: (info|warning): ', r'\1: ', t, flags=re.M)
t = re.sub(r'^== (\S+) \(\S+\)$', r'== \1', t, flags=re.M)
open(f'/workspace/gsw2/evidence/stmt/StmtDump-{sys.argv[1]}.stripped', 'w').write(t)
EOP
