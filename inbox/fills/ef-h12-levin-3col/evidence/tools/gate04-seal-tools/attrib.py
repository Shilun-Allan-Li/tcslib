"""Per-candidate attribution of seal failures (gate 04 round 4).

attrib.py <worktree> <olean-tree> <candidate-dir> <files.txt> <outdir> [jobs]

For each file F in <files.txt> and each candidate c of F, compile a copy of F with only
`attribute [local irreducible] c` after its header and record which declarations fail."""
import os, re, subprocess, sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

WT, OL, CAND, FILES, OUT = sys.argv[1:6]
jobs = int(sys.argv[6]) if len(sys.argv) > 6 else 3
TIMEOUT = int(sys.argv[7]) if len(sys.argv) > 7 else 240
DONE = set()
if len(sys.argv) > 8:
    for l in open(sys.argv[8], encoding='utf-8'):
        p = l.rstrip('\n').split('\t')
        if len(p) >= 3: DONE.add((p[0], p[1]))
WT, OUT = Path(WT).resolve(), Path(OUT).resolve()
(OUT / 'src').mkdir(parents=True, exist_ok=True)
env = dict(os.environ)
env["LEAN_PATH"] = ":".join([OL] + sorted(str(d) for d in (WT / ".lake/packages").glob("*/.lake/build/lib/lean")))
env["PATH"] = str(Path.home() / ".elan/bin") + ":" + env["PATH"]
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*'
                  r'(theorem|lemma|def|abbrev|instance|structure|inductive|class|example|opaque)\b\s*(\S*)')

def header_end(lines):
    i, last, in_c = 0, -1, False
    while i < len(lines):
        s = lines[i].strip()
        if in_c:
            if '-/' in s: in_c = False
        elif s.startswith('/-') and not s.startswith('/-!'):
            in_c = '-/' not in s[2:]
        elif s.startswith('import ') or s.startswith('set_option '):
            last = i
        elif s == '' or s.startswith('--'):
            pass
        else:
            break
        i += 1
    return last

def decl_at(lines, ln):
    for j in range(min(ln, len(lines)) - 1, -1, -1):
        m = DECL.match(lines[j])
        if m: return f"{m.group(2)}@{j + 1}"
    return "?"

def one(args):
    path, c, k = args
    src = (WT / path).read_text(encoding='utf-8')
    lines = src.split('\n'); h = header_end(lines)
    text = '\n'.join(lines[:h + 1] + [f"attribute [local irreducible] {c}"] + lines[h + 1:])
    f = OUT / 'src' / (path.replace('/', '_')[:-5] + f"_c{k}.lean")
    f.write_text(text, encoding='utf-8')
    try:
        r = subprocess.run(["lean", str(f)], cwd=WT, env=env, capture_output=True, text=True, timeout=TIMEOUT)
        outp, rc = r.stdout + r.stderr, r.returncode
    except subprocess.TimeoutExpired:
        return path, c, 'TIMEOUT', [], f'no result within {TIMEOUT}s'
    errs = [l for l in outp.splitlines() if re.search(r':\d+:\d+: error', l)]
    decls, attr_err = [], False
    for e in errs:
        ln = int(re.search(r':(\d+):\d+: error', e).group(1))
        if ln == h + 2: attr_err = True; continue
        d = decl_at(lines, ln - 1 if ln > h + 1 else ln)
        if d not in decls: decls.append(d)
    st = 'PASS' if (rc == 0 and not errs) else ('ATTR-ERROR' if attr_err else 'FAIL')
    msg = errs[0].split('error:', 1)[-1].strip()[:120] if errs else ''
    return path, c, st, decls, msg

tasks = []
for path in [l.strip() for l in open(FILES) if l.strip()]:
    mod = path[:-5].replace('/', '.')
    names = [l.split('\t')[0] for l in open(Path(CAND) / f"{mod}.txt", encoding='utf-8')
             if l.strip() and not l.startswith('#')]
    for k, c in enumerate(names):
        if (path, c) not in DONE: tasks.append((path, c, k))
res = {}
with ThreadPoolExecutor(jobs) as ex:
    for (path, c, st, decls, msg) in ex.map(one, tasks):
        res.setdefault(path, []).append((c, st, decls, msg))
        print(f"{path}\t{c}\t{st}\t{' '.join(decls)}\t{msg}", flush=True)
with open(OUT / 'attrib.tsv', 'w', encoding='utf-8') as o:
    for path in res:
        for (c, st, decls, msg) in res[path]:
            o.write(f"{path}\t{c}\t{st}\t{' '.join(decls)}\t{msg}\n")
