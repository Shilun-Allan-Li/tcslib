"""Screen the MIG-1 proposed names against another tree of landing files (e.g. MIG-0b's round-2
landing set). Read-only. Usage: python3 -I namescreen_extra.py <landing root> <gate-public.txt>
<moved-names.json>. Reports exact full-name matches and shared last components."""
import glob
import json
import os
import sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from namescreen import index_file  # noqa: E402

root, gate_list, moved_json = sys.argv[1:4]
idx = []
for f in sorted(glob.glob(os.path.join(root, '**', '*.lean'), recursive=True)):
    idx.extend(index_file(f, os.path.relpath(f, root)))
prop = [l.split()[3] for l in open(gate_list, encoding='utf-8') if '.MIG1Gate.' not in l]
moved = list(json.load(open(moved_json, encoding='utf-8')))
full = {d['full']: d for d in idx}
print(f'landing files: {len(set(d["mod"] for d in idx))}; declarations: {len(idx)}')
hits = [(n, full[n]['mod'], full[n]['line'], full[n]['private']) for n in prop + moved if n in full]
print(f'exact full-name matches with the {len(prop)} public and {len(moved)} moved proposed names: '
      f'{len(hits)}')
for h in hits:
    print('  ', h)
shorts = {n.split('.')[-1]: n for n in prop}
same = sorted({(d['full'], shorts[d['short']]) for d in idx if d['short'] in shorts
               and d['full'] != shorts[d['short']]})
print(f'shared last components (other namespaces): {len(same)}')
for a, b in same:
    print('  ', a, '~', b)
