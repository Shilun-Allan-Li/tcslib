r"""stateplan.py (int-stmt-331-333, new): incremental integration builds on one olean tree by import-closure keys.
A module's closure key at a rev is a Merkle hash: sha256 of its path, its source SHA-256 at <rev>, and the sorted closure keys
of its local imports (`^import\s+(\S+)`, local = TCSlib.* / audits.*, exactly downorder.py's parsing; Mathlib is fixed).
Two oleans of a module with equal closure keys are built from identical source closures, so the tree's olean can be reused.

  stateplan.py init   <repo> <base-rev> <snapshot> <state.json>
      state = every TCSlib/audits module with an olean in <snapshot>, keyed at <base-rev> (the snapshot's source state),
      with the snapshot's olean hash.
  stateplan.py plan   <repo> <rev> <order.txt> <state.json> <outdir>
      queue.txt = modules of <order.txt> (imports-first) whose key at <rev> differs from the state's (or has no state);
      reuse.txt = the others; keys.tsv = module, key at <rev>, state key, state rev, decision. Asserts imports-first.
  stateplan.py update <repo> <rev> <state.json> <results.jsonl> <tree>
      for each module's last rc-0 record of the run: state[m] = key at <rev>, rev, object hash; the tree's olean must equal it.
  stateplan.py check  <repo> <rev> <order.txt> <state.json> <tree> <out>
      every module of <order.txt>: state key = key at <rev> and tree olean hash = state hash. Prints RESULT OK/FAIL."""
import sys, os, re, json, hashlib, subprocess
sha = lambda b: hashlib.sha256(b).hexdigest()
local = lambda n: n.split('.')[0] in ('TCSlib', 'audits')
class Keys:
    def __init__(self, repo, rev):
        self.repo, self.rev, self.k, self.src = repo, rev, {}, {}
    def source(self, m):
        if m not in self.src:
            p = subprocess.run(['git', '-C', self.repo, 'show', f'{self.rev}:{m}.lean'], capture_output=True)
            self.src[m] = p.stdout if p.returncode == 0 else None
        return self.src[m]
    def imports(self, m):
        s = self.source(m)
        return [i.replace('.', '/') for i in re.findall(r'^import\s+(\S+)', s.decode('utf-8', 'replace'), re.M) if local(i)]
    def key(self, m):
        if m in self.k: return self.k[m]
        s = self.source(m)
        if s is None: self.k[m] = None; return None
        sys.setrecursionlimit(100000)
        ks = sorted(f'{i}={self.key(i)}' for i in self.imports(m))
        self.k[m] = sha(('\n'.join([m, sha(s)] + ks)).encode())
        return self.k[m]
cmd = sys.argv[1]
if cmd == 'init':
    repo, rev, snap, st = sys.argv[2:6]; K = Keys(repo, rev); state = {}
    for l in open(snap):
        h, p = l.rstrip('\n').split('  ', 1)
        if not p.endswith('.olean') or p.startswith('PFR/') or p.startswith('Mathlib/'): continue
        m = p[:-6]; k = K.key(m)
        if k is None: print('no source at base rev:', m); continue
        state[m] = dict(key=k, rev=rev, olean=h)
    json.dump(state, open(st, 'w'), indent=0, sort_keys=True); print(f'init: {len(state)} modules keyed at {rev[:8]}')
elif cmd == 'plan':
    repo, rev, order, st, outd = sys.argv[2:7]; os.makedirs(outd, exist_ok=True)
    K = Keys(repo, rev); state = json.load(open(st)); mods = [l.strip() for l in open(order) if l.strip()]
    q, ru, rows = [], [], []
    for m in mods:
        k = K.key(m); s = state.get(m)
        d = 'reuse' if s and s['key'] == k else 'build'
        (q if d == 'build' else ru).append(m); rows.append((m, k, s['key'] if s else '-', s['rev'][:8] if s else '-', d))
    pos = {m: i for i, m in enumerate(mods)}
    for m in mods:
        for i in K.imports(m): assert pos[i] < pos[m], (i, m)
    w = lambda n, xs: open(os.path.join(outd, n), 'w').write(''.join(x + '\n' for x in xs))
    w('queue.txt', q); w('reuse.txt', ru); w('keys.tsv', ['\t'.join(r) for r in rows])
    print(f'plan {rev[:8]}: order {len(mods)}; build {len(q)}; reuse {len(ru)}')
    from collections import Counter
    print('  reuse by state rev:', dict(Counter(r[3] for r in rows if r[4] == 'reuse')), '; build by state rev:', dict(Counter(r[3] for r in rows if r[4] == 'build')))
elif cmd == 'update':
    repo, rev, st, res, tree = sys.argv[2:7]; K = Keys(repo, rev); state = json.load(open(st)); last = {}
    for l in open(res):
        r = json.loads(l)
        if 'module' in r: last[r['module']] = r
    n = 0; bad = []
    for m, r in last.items():
        if r['rc'] != 0: bad.append(m); continue
        o = sha(open(os.path.join(tree, m + '.olean'), 'rb').read())
        if o != r['object_sha256'] or r['source_sha256'] != sha(K.source(m)): bad.append(m); continue
        state[m] = dict(key=K.key(m), rev=rev, olean=o); n += 1
    json.dump(state, open(st, 'w'), indent=0, sort_keys=True); print(f'update {rev[:8]}: {n} modules; not taken {bad}')
elif cmd == 'check':
    repo, rev, order, st, tree, out = sys.argv[2:8]; K = Keys(repo, rev); state = json.load(open(st))
    mods = [l.strip() for l in open(order) if l.strip()]; bad = []
    with open(out, 'w') as o:
        for m in mods:
            s = state.get(m); p = os.path.join(tree, m + '.olean')
            h = sha(open(p, 'rb').read()) if os.path.exists(p) else None
            ok = s is not None and s['key'] == K.key(m) and h == s['olean']
            if not ok: bad.append(m)
            o.write(f"{'OK ' if ok else 'BAD'} {m} {s['rev'][:8] if s else '-'} {h}\n")
        o.write(f'{rev[:8]} order {len(mods)}; bad {len(bad)} {bad[:10]}\nRESULT {"OK" if not bad else "FAIL"}\n')
    print(open(out).read().splitlines()[-2], '|', open(out).read().splitlines()[-1])
