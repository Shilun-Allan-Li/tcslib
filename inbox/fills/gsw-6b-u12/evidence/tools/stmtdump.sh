#!/usr/bin/env bash
# StmtDump (gsw-6b-u12): the owned file's text at REV (base or HEAD) followed by `#check` of every
# target with full names, compiled as a scratch module through scripts/lean_check_tree.sh (its
# imports are unchanged modules); the info lines, stripped of positions, are the dump.
# usage: stmtdump.sh REV TAG
set -e
cd /workspace/gsw/repo
F=TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Branching.lean
P=scratch/stmt/StmtDump_$2
git show "$1:$F" > $P.lean
cat >> $P.lean <<'EOT'

set_option pp.fullNames true
set_option pp.funBinderTypes true
#check @TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Encrypts.select
#check @TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.encrypts_homEvalPBP
#check @TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.encrypts_homEvalFormula
EOT
export PATH=$HOME/.elan/bin:$PATH
bash scripts/lean_check_tree.sh $P > /workspace/gsw/evidence/stmt/StmtDump-$2.log 2>&1 || true
python3 -I - "$2" <<'EOP'
import re, sys
t = open(f'/workspace/gsw/evidence/stmt/StmtDump-{sys.argv[1]}.log').read()
t = re.sub(r'^\S+\.lean:\d+:\d+: (info|warning): ', r'\1: ', t, flags=re.M)
open(f'/workspace/gsw/evidence/stmt/StmtDump-{sys.argv[1]}.stripped', 'w').write(t)
EOP
