"""Rule-10 seal (gate 04 round 4), adapted from gates/04-s2b/evidence-r3/seal.py.txt.

seal.py <tag> <worktree> <olean-tree> <candidate-dir> <files.txt> <outdir> [--rev REV] [--unseal U.json] [--lenient]

For every Lean file F in <files.txt>: take F's source (the worktree file, or `git show REV:F` with
--rev), insert `attribute [local irreducible] <every candidate of F>` after its header (imports and
set_option lines), and compile the copy with `lean` (no .olean is written) against <olean-tree>.
The candidates are the first column of <candidate-dir>/<module>.txt, written by the automatic
collector (tools/collect_body.lean); nothing is hand-picked.

Named exclusions (--unseal): U.json maps a file to a list of {"decl": <full name>, "names": [...]}.
Each listed declaration (with its docstring and attribute lines) is wrapped in
`section G04R4Unseal` / `attribute [local semireducible] <names>` / `end G04R4Unseal`, so exactly
that declaration may read exactly those foreign definitions, and every other declaration of F is
still compiled with every candidate sealed. An error on an inserted line is reported as SEAL-ERROR
(a seal that did not apply can never count as a pass)."""
import json, os, re, subprocess, sys
from pathlib import Path
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import declx

tag, WT, OL, CAND, FILES, OUT = sys.argv[1:7]
rest = sys.argv[7:]
rev = rest[rest.index('--rev') + 1] if '--rev' in rest else None
unseal = json.load(open(rest[rest.index('--unseal') + 1])) if '--unseal' in rest else {}
LENIENT = '--lenient' in rest
WT, OUT = Path(WT).resolve(), Path(OUT).resolve()
OUT.mkdir(parents=True, exist_ok=True)
env = dict(os.environ)
env["LEAN_PATH"] = ":".join([OL] + sorted(str(d) for d in (WT / ".lake/packages").glob("*/.lake/build/lib/lean")))
env["PATH"] = str(Path.home() / ".elan/bin") + ":" + env["PATH"]
TIMEOUT = 1200

def candidates(path):
    mod = path[:-5].replace('/', '.')
    return [l.split('\t')[0] for l in open(Path(CAND) / f"{mod}.txt", encoding='utf-8')
            if l.strip() and not l.startswith('#')]

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

def build(src, names, entries):
    lines = src.split('\n')
    # a file's own `attribute [local irreducible] …` line would fail on names the top seal already
    # made irreducible: drop exactly those names from it (the top seal covers them from line 1)
    for i, l in enumerate(lines):
        m = re.match(r'^(\s*attribute \[local irreducible\])\s+(.*)$', l)
        if m:
            toks = m.group(2).split()
            keep = [t for t in toks if not any(n == t or n.endswith('.' + t) for n in names)]
            lines[i] = (m.group(1) + ' ' + ' '.join(keep)) if keep else ('-- (covered by the seal line) ' + l.strip())
            OWNSEAL.append(f"{i + 1}: {l.strip()} -> {lines[i].strip()}")
    exts = {e['name']: e for e in declx.extents(src)}
    h = header_end(lines)
    before, after = {}, {}          # 0-based original line -> inserted lines
    before.setdefault(h + 1, []).append("attribute [local irreducible] " + " ".join(names) if names
                                        else "-- (no candidates)")
    used = []
    for ent in entries:
        e = exts.get(ent['decl'])
        if e is None:
            if LENIENT:
                SKIPPED.append(ent['decl']); continue
            raise SystemExit(f"unseal: declaration {ent['decl']} not found")
        ns = [n for n in ent['names'] if n in names]
        before.setdefault(e['dstart'] - 1, []).extend(
            ["section G04R4Unseal", "attribute [local semireducible] " + " ".join(ns)])
        after.setdefault(e['end'] - 1, []).append("end G04R4Unseal")
        used.append((ent['decl'], e['dstart'], e['end'], ns))
    out, omap = [], []              # omap[k] = original 1-based line of output line k+1, or None
    for i, l in enumerate(lines + ([] if h + 1 < len(lines) else [''])):
        for x in before.get(i, []): out.append(x); omap.append(None)
        if i < len(lines): out.append(l); omap.append(i + 1)
        for x in after.get(i, []): out.append(x); omap.append(None)
    return '\n'.join(out), omap, exts, used

OWNSEAL = []
SKIPPED = []
results = []
files = [l.strip() for l in open(FILES) if l.strip()]
for path in files:
    names = candidates(path)
    if rev:
        src = subprocess.run(["git", "show", f"{rev}:{path}"], cwd=WT, capture_output=True, text=True).stdout
    else:
        src = (WT / path).read_text(encoding='utf-8')
    entries = unseal.get(path, [])
    OWNSEAL.clear(); SKIPPED.clear()
    text, omap, exts, used = build(src, names, entries)
    f = OUT / (path.replace('/', '_')[:-5] + f"_{tag}.lean")
    f.write_text(text, encoding='utf-8')
    try:
        r = subprocess.run(["lean", str(f)], cwd=WT, env=env, capture_output=True, text=True, timeout=TIMEOUT)
        outp, rc = r.stdout + r.stderr, r.returncode
    except subprocess.TimeoutExpired:
        outp, rc = f"{f}:1:0: error: TIMEOUT after {TIMEOUT}s", -9
    errs = [l for l in outp.splitlines() if re.search(r':\d+:\d+: error', l)]
    sorted_exts = sorted(exts.values(), key=lambda e: e['dstart'])
    def owner(oln):
        best = None
        for e in sorted_exts:
            if e['dstart'] <= oln: best = e
        return f"{best['kind']} {best['name']}" if best else '?'
    detail, seal_err = [], False
    for e in errs:
        m = re.search(r':(\d+):(\d+): error:?\s*(.*)', e)
        k = int(m.group(1))
        oln = omap[k - 1] if 0 < k <= len(omap) else None
        if oln is None:
            seal_err = True
            detail.append(f"   SEAL-LINE {k}: {m.group(3)[:200]}")
        else:
            detail.append(f"   {path}:{oln}:{m.group(2)} [{owner(oln)}] {m.group(3)[:160]}")
    if rc != 0 and not errs:
        detail.extend("   RAW: " + l[:200] for l in outp.splitlines()[:15])
    st = 'SEAL-ERROR' if seal_err else ('PASS' if rc == 0 and not errs else 'FAIL')
    unote = f"; unsealed for {len(used)} named declaration(s)" if used else ''
    results.append(f"{path}: candidates={len(names)}{unote} {st} (rc={rc}, error lines={len(errs)})")
    for o in OWNSEAL:
        results.append(f"   own seal line {o}")
    for o in SKIPPED:
        results.append(f"   unseal entry not applicable at this revision (declaration absent): {o}")
    for (d, a, b, ns) in used:
        results.append(f"   unseal {d} (lines {a}-{b}): {' '.join(ns)}")
    results.extend(detail)
    print('\n'.join(results[-(1 + len(OWNSEAL) + len(SKIPPED) + len(used) + len(detail)):]), flush=True)
(OUT / f"results_{tag}.txt").write_text('\n'.join(results) + '\n', encoding='utf-8')
