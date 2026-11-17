#!/usr/bin/env bash
# Gate 145 Lean-backed definition sweep: compile Kinds, then one #kinds check per owner.
source "$(dirname "$0")/../lib.sh"
G=$GATE; W=$G/dsw; OV=$G/dsw-ov; mkdir -p $G/defsweep
bash $TOOLS/leanelab-o.sh $W $OV TCSlib/Scratch/Kinds.lean $OV > $G/defsweep/Kinds.log 2>&1; echo "Kinds exit $?"
# One probe per owner, each its own file and log; run in parallel within the pool (workflow.md 4.1).
P=$(bash $TOOLS/leanpool.sh); echo "pool $P"
ls $W/TCSlib/Scratch/DefSweep/Check_*.lean | xargs -n1 basename | sed 's/\.lean$//' | W=$W OV=$OV G=$G TOOLS=$TOOLS xargs -P "$P" -I{} bash -c \
  'bash $TOOLS/leanelab-o.sh $W $OV TCSlib/Scratch/DefSweep/{}.lean $OV > $G/defsweep/{}.log 2>&1; echo "{} exit $?"' | sort
python3 -I - <<'PY'
import json, re
from pathlib import Path
import os
G = Path(os.environ['GATE'])
src = json.loads((G/'SOURCE.json').read_text())
out = {}
for row in src['owner_source']:
    stem = Path(row['path']).stem; mod = row['path'][:-5].replace('/', '.')
    rows = [l.split('|') for l in (G/'defsweep'/f'Check_{stem}.log').read_text().splitlines() if l.startswith('KIND|')]
    foreign = sorted({(n, m) for _, n, k, m in rows if k in ('def', 'opaque', 'axiom', 'quot') and m != mod})
    out[stem] = {'identifiers': len(rows), 'foreign_definitions': [list(x) for x in foreign]}
(G/'defsweep/SUMMARY.json').write_text(json.dumps(out, indent=1) + '\n'); print(json.dumps(out))
PY
