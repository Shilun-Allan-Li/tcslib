"""Explicit-unfold scan of the owned files (gsw-security); full-file seals cover implicit
reduction. Modelled on the derand fill's `explicit_unfold_scan.py`.

Every selector `unfold X`, `delta X`, `simp/simp_all/simpa/dsimp/rw/erw [...]` (with `only`, `!`,
`?`) is split into its items; each head identifier is resolved against the catalog of
imported TCSlib definitions that the seal harness printed (`GSWSEC-CATALOG` rows of the given
seal logs; non-reducible definitions and matchers). Comments and docstrings are masked first.
Local `let`/`have`/`obtain` names, binder names and the file's own declarations are skipped
(own definitions may be read directly). A token is reported FOREIGN when it resolves (exactly,
or as a dotted suffix) to a catalog definition whose home module is not the scanned file.

Usage (python3 -I, from the fill checkout root):
    explicit_unfold_scan.py <base-commit> <outdir> <seal-log-dir> [<seal-log-dir> ...]
Writes <outdir>/{items.json,foreign.json,summary.txt}; exit 0 iff no item added since base is
FOREIGN.
"""
import json
from pathlib import Path
import re
import subprocess
import sys

FILES = ['TCSlib/Cryptography/Hashing/SIS/Columns.lean',
         'TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Security.lean']
base, out = sys.argv[1], Path(sys.argv[2])
catalog = {}
for folder in sys.argv[3:]:
    for path in Path(folder).rglob('*.log'):
        for line in path.read_text().splitlines():
            m = re.search(r'GSWSEC-CATALOG \S+ (\{.*\})$', line)
            if m:
                row = json.loads(m[1])
                if row['status'] != '[reducible]' or row['matcher']:
                    catalog[row['name']] = row
selector = re.compile(r'\b(?:unfold|delta)\s+([^\n;]+)|'
                      r'\b(?:simp_all|simpa|simp|dsimp|rw|erw|rwa)\b\s*'
                      r'(?:(?:only|!|\?)\s*)?\[([^\]]*)\]', re.S)
ident = re.compile(r'[A-Za-z_][A-Za-z_0-9₀-₉\']*(?:\.[A-Za-z_][A-Za-z_0-9₀-₉\']*)*')


def mask(src):
    """Blank comments and docstrings, keeping offsets and newlines."""
    out, i, depth = list(src), 0, 0
    while i < len(src):
        if src.startswith('/-', i):
            j, depth = i, 0
            while j < len(src):
                if src.startswith('/-', j):
                    depth += 1; j += 2; continue
                if src.startswith('-/', j):
                    depth -= 1; j += 2
                    if depth == 0:
                        break
                    continue
                j += 1
            for k in range(i, j):
                if out[k] != '\n':
                    out[k] = ' '
            i = j
        elif src.startswith('--', i):
            j = src.find('\n', i)
            j = len(src) if j < 0 else j
            for k in range(i, j):
                out[k] = ' '
            i = j
        else:
            i += 1
    return ''.join(out)


def heads(m):
    if m[1] is not None:
        return ident.findall(re.split(r'\bat\b', m[1], maxsplit=1)[0])
    body, pieces, start, depth = m[2], [], 0, 0
    for k, ch in enumerate(body):
        if ch in '([{':
            depth += 1
        elif ch in ')]}':
            depth -= 1
        elif ch == ',' and depth == 0:
            pieces.append(body[start:k]); start = k + 1
    pieces.append(body[start:])
    res = []
    for p in pieces:
        p = p.strip().removeprefix('←').strip()
        if p.startswith('-'):
            continue
        f = ident.match(p)
        if f and f[0] not in {'show', 'by', 'fun', 'if'}:
            res.append(f[0])
    return res


def scan(path, src):
    home = path[:-5].replace('/', '.')
    masked = mask(src)
    own = set(re.findall(r'(?m)^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*'
                         r'(?:theorem|lemma|def|abbrev)\s+(\S+)', masked))
    locs = set(re.findall(r'\b(?:let|have|obtain)\s+([A-Za-z_][A-Za-z_0-9₀-₉\']*)',
                          masked))
    locs |= set(re.findall(r'[({]\s*([A-Za-z_][A-Za-z_0-9₀-₉\']*)\s*[: ]', masked))
    decls = [(masked.count('\n', 0, m.start()) + 1, m[1]) for m in
             re.finditer(r'(?m)^(?:theorem|lemma|def)\s+(\S+)', masked)]
    rows = []
    for m in selector.finditer(masked):
        line = masked.count('\n', 0, m.start()) + 1
        decl = next((n for l, n in reversed(decls) if l <= line), '')
        for tok in heads(m):
            if '.' not in tok and (tok in locs or tok in own):
                kind = 'local-or-own'
                cands = []
            else:
                cands = sorted(n for n, r in catalog.items()
                               if (n == tok or n.endswith('.' + tok)) and r['home'] != home)
                kind = 'FOREIGN' if cands else 'lemma-or-nondefinition'
            rows.append(dict(path=path, line=line, declaration=decl, token=tok, kind=kind,
                             candidates=cands, selector=' '.join(m[0].split())[:160]))
    return rows


out.mkdir(parents=True, exist_ok=True)
before, after = [], []
for path in FILES:
    before += scan(path, subprocess.check_output(['git', 'show', f'{base}:{path}'], text=True))
    after += scan(path, Path(path).read_text())
key = lambda r: (r['path'], r['declaration'], r['selector'], r['token'])
old = {key(r) for r in before}
added = [r for r in after if key(r) not in old]
foreign = [r for r in after if r['kind'] == 'FOREIGN']
added_foreign = [r for r in added if r['kind'] == 'FOREIGN']
(out / 'items.json').write_text(json.dumps(after, indent=2, ensure_ascii=False) + '\n')
(out / 'foreign.json').write_text(json.dumps(foreign, indent=2, ensure_ascii=False) + '\n')
lines = [f'catalog: {len(catalog)} imported non-reducible TCSlib definitions/matchers',
         f'selector items: base={len(before)} final={len(after)} added={len(added)}',
         'by kind (final): ' + ', '.join(f'{k}={sum(r["kind"] == k for r in after)}'
                                        for k in ['local-or-own', 'lemma-or-nondefinition',
                                                  'FOREIGN'])]
for r in foreign:
    lines.append(f'FOREIGN {r["path"]}:{r["line"]} {r["declaration"]}: {r["token"]} -> '
                 f'{r["candidates"]} in `{r["selector"]}`')
lines.append('EXPLICIT UNFOLD SCAN ' + ('PASS' if not added_foreign else 'REVIEW'))
(out / 'summary.txt').write_text('\n'.join(lines) + '\n')
print('\n'.join(lines))
sys.exit(1 if added_foreign else 0)
