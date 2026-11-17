#!/usr/bin/env bash
set -uo pipefail
source "$(dirname "$0")/lib.sh"
S=$SCRATCH; G=$GATE; O=$S/$OUTPUT_SNAPSHOT; RT=$G/replay/runtime
until [ -f $G/replay/RESULT.json ]; do sleep 20; done
python3 -I -c "import json,sys;r=json.load(open('$G/replay/RESULT.json'));print('REPLAY',r['pass'],r['modules'],r['failed'],r['inherited_admissions']);sys.exit(0 if r['pass'] else 1)" || { echo REPLAY-FAIL; exit 1; }
python3 -I $KIT/checks/metadata.py $G/SOURCE.json $RT $O $G/metadata all || { echo METADATA-FAIL; exit 2; }
python3 -I $KIT/checks/grouped-cmp.py $G/seals $O $RT $G/SOURCE.json final $G/metadata/DATA.json > $G/seals.out 2>&1; s=$?; grep -c PASS $G/seals.out; grep FAIL $G/seals.out
N=$(python3 -I -c "import json;d=json.load(open('$G/seals/REQUEST.json'));h={n for o in d['owners'] for c in o['checks'] for n in c['heads']};print(-(-len(h)//45))")
# Control parts are disjoint, each with its own runtime and output directory: run them in parallel (workflow.md 4.1).
P=$(bash $TOOLS/leanpool.sh); echo "pool $P"
c=0; seq 0 $((N-1)) | G=$G O=$O N=$N KIT=$KIT GATE=$GATE xargs -P "$P" -I{} bash -c 'HEADS_PART={} HEADS_PARTS=$N python3 -I $KIT/checks/controls-half.py $G/seals/REQUEST.json $O $G/controls-part{}' || c=1
python3 -I $KIT/checks/qa.py $RT $G/SOURCE.json $G/metadata/DATA.json $G/qa > $G/qa.log 2>&1; q=$?; tail -3 $G/qa.log | cut -c1-400
echo "SEALS exit=$s CONTROLS fail=$c parts=$N QA exit=$q"
echo CHECKS DONE
