"""proofseal.py <worktree> <olean-tree> <workdir> <file.lean>...: whole-file (proofs included) seal.
1. U = full source + collector whose roots include theorem VALUES (proofs) -> candidate defs.
2. S = full source with `attribute [local irreducible] <all candidates>` (PolyExpr.eval excepted,
   notation, ruling Q1) after the imports; every error is attributed to its enclosing declaration.
Output per file: <tag>.U.log, <tag>.cands, <tag>.S.lean, <tag>.S.log, and a summary line on stdout."""
import json, os, re, subprocess, sys
from pathlib import Path
WT, OL, WORK = Path(sys.argv[1]), sys.argv[2], Path(sys.argv[3])
TAIL = (Path(__file__).parent / 'proofcollect_tail.lean').read_text(encoding='utf-8')
env = dict(os.environ)
env["LEAN_PATH"] = ":".join([OL] + sorted(str(d) for d in (WT / ".lake/packages").glob("*/.lake/build/lib/lean")))
env["PATH"] = str(Path.home() / ".elan/bin") + ":" + env["PATH"]
NOTATION = {'Complexity.PolyExpr.eval'}
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec)\s+)*(theorem|lemma|def|abbrev|instance|example|structure)\b\s*([^\s:(\[{]*)')
def run(path):
    p = subprocess.run(["lean", str(path)], cwd=WT, env=env, capture_output=True, text=True, timeout=3600)
    return p.returncode, p.stdout + p.stderr
for f in sys.argv[4:]:
    tag = f.replace('/', '_')[:-5]
    src = (WT / f).read_text(encoding='utf-8')
    u = WORK / (tag + '.U.lean')
    u.write_text(src + '\n' + TAIL.replace('SWEEP_OUT_PATH', json.dumps(str(WORK / (tag + '.coll')))), encoding='utf-8')
    rc, out = run(u); (WORK / (tag + '.U.log')).write_text(out)
    cands = []
    cf = WORK / (tag + '.coll.cands.tsv')
    if cf.exists():
        cands = [l.split('\t')[0] for l in cf.read_text().splitlines() if l.strip()]
    cands = [c for c in cands if c not in NOTATION]
    lines = src.split('\n')
    last_imp = max(i for i, l in enumerate(lines) if l.startswith('import '))
    seal = ['', 'attribute [local irreducible] ' + ' '.join(cands)] if cands else []
    s_lines = lines[:last_imp + 1] + seal + lines[last_imp + 1:]
    off = len(seal)
    spath = WORK / (tag + '.S.lean'); spath.write_text('\n'.join(s_lines), encoding='utf-8')
    rc2, out2 = run(spath); (WORK / (tag + '.S.log')).write_text(out2)
    errs = [int(m.group(1)) for m in re.finditer(re.escape(str(spath)) + r':(\d+):\d+: error', out2)]
    decls = {}
    for ln in errs:
        o = ln - off  # line in the original file (1-based)
        name = '?'
        # an error reported at a declaration's docstring (e.g. a failed `rfl` behind `@[simp]`)
        # belongs to the declaration that docstring documents
        if lines[o - 1].lstrip().startswith('/--'):
            for j in range(o - 1, len(lines)):
                if DECL.match(lines[j]):
                    o = j + 1; break
        for j in range(o - 1, -1, -1):
            m = DECL.match(lines[j])
            if m:
                name = f"{m.group(1)} {m.group(2)}@{j+1}"; break
        decls.setdefault(name, []).append(o)
    print(f"{f}\tU_rc={rc}\tcands={len(cands)}\tS_rc={rc2}\terrors={len(errs)}\t" +
          '; '.join(f"{k} {v}" for k, v in decls.items()), flush=True)
