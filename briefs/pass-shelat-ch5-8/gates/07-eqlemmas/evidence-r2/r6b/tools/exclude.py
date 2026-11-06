"""Derive minimal named unseal entries (gate 04 round 4).

exclude.py <worktree> <olean-tree> <candidate-dir> <files.txt> <outdir> <seed.json> <out.json> [jobs]

For each file F: start from the entries of <seed.json> for F (if any). Fixpoint: seal F with every
candidate and the current entries (tools/seal.py); for every declaration that still fails, unseal
for it the candidates it uses (collector's <module>.uses.txt), then, if it still fails, every
candidate. Minimisation: drop entries F passes without (cascades), then binary-partition each entry's
names, dropping every part F passes without (1-minimal: each remaining name is needed). Writes the entries to
<out.json> and a log of every step to <outdir>/exclude-<file>.log."""
import json, os, re, subprocess, sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

WT, OL, CAND, FILES, OUT, SEED, RES = sys.argv[1:8]
jobs = int(sys.argv[8]) if len(sys.argv) > 8 else 3
TOOLS = Path(__file__).resolve().parent
OUT = Path(OUT).resolve(); OUT.mkdir(parents=True, exist_ok=True)
seed = json.load(open(SEED)) if os.path.exists(SEED) else {}

def cands(path):
    mod = path[:-5].replace('/', '.')
    return [l.split('\t')[0] for l in open(Path(CAND) / f"{mod}.txt", encoding='utf-8')
            if l.strip() and not l.startswith('#')]

def uses(path):
    mod = path[:-5].replace('/', '.')
    u = {}
    p = Path(CAND) / f"{mod}.uses.txt"
    for l in open(p, encoding='utf-8'):
        if ':' in l:
            o, rest = l.split(':', 1); u[o.strip()] = rest.split()
    return u

def run(path, entries, tag):
    d = OUT / 'work' / path.replace('/', '_')[:-5]
    d.mkdir(parents=True, exist_ok=True)
    (d / 'files.txt').write_text(path + '\n')
    js = {path: [{"decl": k, "names": sorted(v)} for k, v in entries.items() if v]}
    (d / 'unseal.json').write_text(json.dumps(js))
    r = subprocess.run([sys.executable, '-I', str(TOOLS / 'seal.py'), tag, WT, OL, CAND, str(d / 'files.txt'),
                        str(d), '--unseal', str(d / 'unseal.json')], capture_output=True, text=True)
    res = (d / f'results_{tag}.txt').read_text() if (d / f'results_{tag}.txt').exists() else r.stdout + r.stderr
    head = res.split('\n')[0]
    fails = []
    for l in res.split('\n')[1:]:
        m = re.match(r'\s+\S+:\d+:\d+ \[\w+ (\S+)\]', l)
        if m and m.group(1) not in fails: fails.append(m.group(1))
        if 'SEAL-LINE' in l or 'RAW:' in l or '[?]' in l: fails.append('?')
    return (' PASS ' in head), fails, res

def one(path):
    log = []
    C = set(cands(path)); U = uses(path)
    entries = {e['decl']: set(e['names']) for e in seed.get(path, [])}
    for rnd in range(12):
        ok, fails, res = run(path, entries, f"fx{rnd}")
        log.append(f"## fixpoint round {rnd}: {'PASS' if ok else 'FAIL'} {fails}")
        if ok: break
        if '?' in fails:
            log.append(res); return path, None, log
        for D in fails:
            have = entries.setdefault(D, set())
            add = (set(U.get(D, [])) & C) - have
            if not add: add = C - have
            if not add:
                log.append(f"!! {D} fails with every candidate unsealed"); return path, None, log
            have |= add
            log.append(f"   + {D}: {sorted(add)}")
    else:
        return path, None, log
    # minimisation: drop whole entries that are cascades, then split the names of each remaining
    # entry in halves (binary partition) and drop every part the file passes without
    k = [0]
    def passes(trial):
        ok, fails, _ = run(path, trial, f"min{k[0]}"); k[0] += 1
        return ok, fails
    for D in sorted(entries):
        trial = {x: set(v) for x, v in entries.items() if x != D}
        ok, fails = passes(trial)
        if ok:
            log.append(f"   - {D}: whole entry not needed (cascade) {sorted(entries[D])}"); del entries[D]
    def shrink(D, part):
        trial = {x: set(v) for x, v in entries.items()}
        trial[D] -= set(part)
        ok, fails = passes(trial)
        if ok:
            entries[D] -= set(part); log.append(f"   - {D}: not needed {part}")
        elif len(part) == 1:
            log.append(f"   = {D}: {part[0]} needed [trial min{k[0] - 1}] (without it: {fails})")
        else:
            h = len(part) // 2
            shrink(D, part[:h]); shrink(D, [n for n in part[h:] if n in entries[D]])
    for D in sorted(entries):
        shrink(D, sorted(entries[D]))
    entries = {D: v for D, v in entries.items() if v}
    ok, fails, res = run(path, entries, "final")
    log.append(f"## final: {'PASS' if ok else 'FAIL'} {fails}")
    return path, (entries if ok else None), log

files = [l.strip() for l in open(FILES) if l.strip()]
# restart-safe: each file's entries and log are written as soon as it completes; a file whose
# result is already in <outdir>/done/ is not run again
DONE = OUT / 'done'; DONE.mkdir(exist_ok=True)
todo = [f for f in files if not (DONE / (f.replace('/', '_')[:-5] + '.json')).exists()]
from concurrent.futures import as_completed
with ThreadPoolExecutor(jobs) as ex:
    futs = {ex.submit(one, f): f for f in todo}
    for fu in as_completed(futs):
        path, entries, log = fu.result()
        tag = path.replace('/', '_')[:-5]
        (OUT / f"exclude-{tag}.log").write_text('\n'.join(log) + '\n')
        print(path, 'OK' if entries is not None else 'UNRESOLVED', flush=True)
        if entries is not None:
            (DONE / f"{tag}.json").write_text(json.dumps(
                [{"decl": D, "names": sorted(v)} for D, v in sorted(entries.items())], indent=1))
out = {}
for f in files:
    p = DONE / (f.replace('/', '_')[:-5] + '.json')
    if p.exists():
        v = json.load(open(p))
        if v: out[f] = v
json.dump(out, open(RES, 'w'), indent=1)
print('resolved', sum((DONE / (f.replace('/', '_')[:-5] + '.json')).exists() for f in files), 'of', len(files))
