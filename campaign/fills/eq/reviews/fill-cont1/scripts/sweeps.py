"""Summarize the delivered bootstrap / final sweep / tail logs (python3 -I; data only).
For each run: module count, order vs the order list, exits, errors, warnings, sorry warnings per
module (with the declaration found at the warned line in the source at that commit), time and memory.
usage: python3 -I sweeps.py <evidence/logs> <order list> <source root> <run>..."""
import json, os, re, sys
logs, order_p, src_root = sys.argv[1:4]
order = [l.strip() for l in open(order_p) if l.strip()]
W = re.compile(r"^(\S+\.lean):(\d+):(\d+): (warning|error): (.*)$")
DECL = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec)\s+)*(?:theorem|lemma|def|abbrev|instance|structure)\s+(\S+)')
def decl_at(path, line):
    try: L = open(os.path.join(src_root, path), encoding='utf-8').read().split('\n')
    except OSError: return '?'
    m = DECL.match(L[line - 1]); return m.group(1) if m else '?(' + L[line - 1].strip()[:40] + ')'
for run in sys.argv[4:]:
    J = json.load(open(os.path.join(logs, run + '.json')))
    mods = [e['module'] for e in J]
    print(f'## {run}: {len(J)} entries; exit file: {open(os.path.join(logs, run + ".exit")).read().strip() if os.path.exists(os.path.join(logs, run + ".exit")) else "absent"}')
    print(f'   modules equal the order list in order: {mods == order}; a suffix of it: {mods == order[len(order) - len(mods):]}')
    print(f'   exits nonzero: {[e["module"] for e in J if e["exit"] != 0]}')
    tot = sum(e['elapsed_seconds'] for e in J); peak = max(e['max_rss_kib'] for e in J)
    pm = max(J, key=lambda e: e['max_rss_kib'])['module']
    print(f'   summed seconds {tot:.3f}; peak RSS {peak} KiB ({pm}); span {J[0]["start"]} .. {J[-1]["end"]}')
    d = os.path.join(logs, run); errs = 0; warns_other = []; sor = {}
    for i, e in enumerate(J, 1):
        f = os.path.join(d, f'{i:03d}-' + e['module'].replace('/', '_') + '.log')
        txt = open(f, encoding='utf-8').read() if os.path.exists(f) else None
        if txt is None: print('   MISSING LOG', f); continue
        for l in txt.split('\n'):
            m = W.match(l)
            if not m: continue
            if m.group(4) == 'error': errs += 1
            elif "declaration uses 'sorry'" in m.group(5):
                sor.setdefault(e['module'], []).append(decl_at(m.group(1), int(m.group(2))))
            else: warns_other.append((e['module'], l[:160]))
    print(f'   errors {errs}; sorry warnings {sum(len(v) for v in sor.values())} in {len(sor)} modules; other warnings {len(warns_other)}')
    for k, v in sor.items(): print(f'     {k}: {len(v)}: {", ".join(v)}')
    nd = [w for w in warns_other if 'NTimeDiagonalizer' in w[0]]
    print(f'   other warnings in NTimeDiagonalizer: {nd}')
