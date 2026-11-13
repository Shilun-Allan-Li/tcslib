#!/usr/bin/env python3
"""Whole-file seals of the dl-folds fill (resumable; stops after ~240 s).
usage: seal.py TAG [files...]   (default files: files.SUPER)
For each file: a census module with exactly the file's imports lists every seal candidate of its
full TCSlib import closure (semireducible, non-instance, non-projection, non-private TCSlib
definitions; all foreign to the file); seal A (PolyExpr.eval exempt) and seal B (sealed) are
verbatim copies of the file with `attribute [local irreducible]` on the candidates after the first
`open` of its first namespace. Results: logs/seal/TAG/results.jsonl (one line per file and variant,
with the failing declarations)."""
import re, sys, os, json, subprocess, time
sys.path.insert(0, '/workspace/foldtools')
from files import SUPER, key
F = '/workspace/folds'; TAG = sys.argv[1]; files = sys.argv[2:] or SUPER
L = f'/workspace/foldpay/evidence/logs/seal/{TAG}'; S = f'{F}/scratch/seal/{TAG}'
os.makedirs(L, exist_ok=True); os.makedirs(S, exist_ok=True)
EVAL = 'Complexity.PolyExpr.eval'
LP = F + '/.lake/tcslib-check-oleans:' + ':'.join(
    f'{F}/.lake/packages/{d}/.lake/build/lib/lean' for d in sorted(os.listdir(F + '/.lake/packages')))
env = dict(os.environ, LEAN_PATH=LP, PATH=os.path.expanduser('~/.elan/bin') + ':' + os.environ['PATH'])
BODY = '''
open Lean Elab Command Meta

/-! Seal census of the dl-folds fill (%s) for `%s`: the module's own imports, and every seal
candidate of its full TCSlib import closure (semireducible, non-instance, non-projection,
non-private TCSlib definitions; all are foreign to the file). One `CAND` line each. -/

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut out : Array String := #[]
  let mut skipped : Nat := 0
  for (c, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? c | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless mod.toString.startsWith "TCSlib" do continue
    unless ci matches .defnInfo _ do continue
    if c.isInternal || isPrivateName c then skipped := skipped + 1; continue
    if isInstanceCore env c || env.isProjectionFn c || isAuxRecursor env c ||
        isNoConfusion env c then skipped := skipped + 1; continue
    if getReducibilityStatusCore env c != .semireducible then skipped := skipped + 1; continue
    out := out.push s!"CAND {c.toString (escape := true)} | {mod}"
  for s in out.qsort (· < ·) do IO.println s
  IO.println s!"TOTAL {out.size} candidates; {skipped} TCSlib definitions skipped"
'''
DECL = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec)\s+)*'
                  r'(theorem|lemma|def|abbrev|instance|structure|inductive|example)\b\s*([^\s:({\[]*)')
def decl_at(lines, ln):
    for i in range(ln - 1, -1, -1):
        m = DECL.match(lines[i])
        if m: return m.group(2) or m.group(1)
    return '?'
def run(src, log):
    t = time.time()
    p = subprocess.run(['lean', src], cwd=F, env=env, capture_output=True, text=True)
    open(log, 'w').write(p.stdout + p.stderr)
    return p.returncode, time.time() - t
res = L + '/results.jsonl'
done = set()
if os.path.exists(res):
    for l in open(res): d = json.loads(l); done.add((d['file'], d['variant']))
t0 = time.time()
for path in files:
    k = key(path)
    if (path, 'A') in done and (path, 'B') in done: continue
    if time.time() - t0 > 200: print('PAUSE'); sys.exit(0)
    src = open(F + '/' + path).read()
    scanlog = f'{L}/scan-{k}.log'
    if not os.path.exists(scanlog) or 'TOTAL' not in open(scanlog).read():
        imps = [l for l in src.splitlines() if l.startswith('import ')]
        open(f'{S}/Scan_{k}.lean', 'w').write('\n'.join(imps) + '\n' + BODY % (TAG, path))
        rc, _ = run(f'{S}/Scan_{k}.lean', scanlog)
        if rc != 0: print('SCAN FAILED', path); sys.exit(1)
    cands = [l.split()[1] for l in open(scanlog) if l.startswith('CAND ')]
    ns = src.find('\nnamespace ')
    m = re.compile(r'\nopen [^\n]*\n').search(src, ns if ns >= 0 else 0)
    e = m.end() if m else (src.index('\n', ns + 1) + 1)
    for var in 'AB':
        if (path, var) in done: continue
        names = [c for c in cands if var == 'B' or c != EVAL]
        attr = ('attribute [local irreducible] ' + ' '.join('_root_.' + c for c in names)) if names \
            else '-- (no seal candidate: the file imports no TCSlib definition)'
        hdr = ('\n/-! Seal %s (dl-folds, %s): a verbatim copy of `%s`, with every seal candidate of its\n'
               'full TCSlib import closure (%d definitions%s) irreducible from here on. -/\n%s\n\n'
               % (var, TAG, path, len(names), ', `PolyExpr.eval` exempt' if var == 'A'
                  else ', `PolyExpr.eval` included', attr))
        sf = f'{S}/Seal{var}_{k}.lean'
        text = src[:e] + hdr + src[e:]
        open(sf, 'w').write(text)
        lg = f'{L}/seal{var}-{k}.log'
        rc, dt = run(sf, lg)
        lines = text.splitlines()
        errs = []
        for l in open(lg):
            mm = re.match(r'[^:]+\.lean:(\d+):\d+: error', l)
            if mm: errs.append(decl_at(lines, int(mm.group(1))))
        rec = {'file': path, 'variant': var, 'exit': rc, 'seconds': round(dt, 1),
               'candidates': len(names), 'errors': len(errs), 'failing': sorted(set(errs))}
        open(res, 'a').write(json.dumps(rec) + '\n')
        print(var, k, rc, len(errs), sorted(set(errs)), round(dt, 1))
print('DONE')
