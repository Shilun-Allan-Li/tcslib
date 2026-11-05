#!/usr/bin/env bash
# walk.sh <outdir> : copy the owned module + walk tail, check it, extract the walk; then
# a second copy with #print axioms for every new declaration and the target.
set -u
source ~/.elan/env
cd /home/user/tcslib
OD="$1"; mkdir -p "$OD"
MOD=TCSlib/Complexity/ClassNP/NDNormalForm.lean
cat "$MOD" scratch/walk.lean.txt > scratch/NFWalk.lean
bash scripts/lean_check_tree.sh scratch/NFWalk > "$OD/walk-raw.log" 2>&1; echo "walk exit: $?" >> "$OD/walk-raw.log"
python3 - "$OD" <<'PY'
import sys,re
od=sys.argv[1]; t=open(od+'/walk-raw.log').read()
m=re.search(r'WALK_NEW (\d+)\n(.*?)(?=\nscratch/|\Z)',t,re.S); news=m.group(2).strip().split('\n')
m2=re.search(r'WALK_EXT (\d+)\n(.*?)(?=\nscratch/|\Z)',t,re.S); ext=m2.group(2).strip().split('\n')
open(od+'/walk-new.txt','w').write('\n'.join(news)+'\n')
open(od+'/walk-ext.tsv','w').write('\n'.join(e for e in ext if e.count('\t')==2)+'\n')
import subprocess
src=open('TCSlib/Complexity/ClassNP/NDNormalForm.lean').read().split('\n')
first=set(l.strip() for l in open('scratch/first39.txt'))
top=[]
for l in src:
    m=re.match(r'^private (?:theorem|def|instance|inductive|abbrev) (nf_[^ \n(:]+)',l)
    if m and m.group(1) not in first: top.append('Turing.FinNDTM.'+m.group(1))
open(od+'/new-decls.txt','w').write('\n'.join(top)+'\n')
PY
{ cat "$MOD"; echo; echo "namespace Turing.FinNDTM"; while read -r n; do s="${n#Turing.FinNDTM.}"; echo "#print axioms $s"; done < "$OD/new-decls.txt"; echo "#print axioms exists_codeNDTM_accepts_linear"; echo "end Turing.FinNDTM"; } > scratch/NFAxioms.lean
bash scripts/lean_check_tree.sh scratch/NFAxioms > "$OD/axioms-raw.log" 2>&1; echo "axioms exit: $?" >> "$OD/axioms-raw.log"
grep -c "depends on axioms\|does not depend" "$OD/axioms-raw.log"
