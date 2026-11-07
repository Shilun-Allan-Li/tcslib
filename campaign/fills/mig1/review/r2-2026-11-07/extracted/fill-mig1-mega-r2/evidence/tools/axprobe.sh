#!/usr/bin/env bash
# axprobe.sh <tag> <imports file> <names file>: #print axioms for each name, via leanelab.sh
. /work/mig1/env.sh; cd "$TCSLIB_REPO"; tag=$1
P=ScratchProbes/Ax_$tag.lean
{ sed 's/^/import /' "$2"; echo; while read -r n; do [ -n "$n" ] && echo "#print axioms $n"; done < "$3"; } > $P
mkdir -p $EV/logs/axioms; cp $P $EV/logs/axioms/Ax_$tag.lean.txt
bash devtools/seyoon/leanelab.sh "$TCSLIB_REPO" "$TCSLIB_OLEANS" $P > $EV/logs/axioms/Ax_$tag.out 2>&1; st=$?
echo "exit=$st" >> $EV/logs/axioms/Ax_$tag.out
python3 -I - "$EV/logs/axioms/Ax_$tag.out" "$3" <<'PY'
import sys,re
out=open(sys.argv[1]).read(); names=[l.strip() for l in open(sys.argv[2]) if l.strip()]
std={'propext','Classical.choice','Quot.sound'}
blocks=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",out,re.S)
seen={}
for n,ax in blocks:
    s=set(a.strip() for a in ax.replace('\n',' ').split(',') if a.strip())
    seen[n]=s
bad=0
for n in names:
    s=seen.get(n)
    if s is None: print('MISSING',n); bad+=1
    elif s<=std: print('STANDARD',n,sorted(s))
    else: print('NONSTANDARD',n,sorted(s)); bad+=1
print(f'names={len(names)} standard={len(names)-bad} other={bad}')
PY
