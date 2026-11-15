"""Scan explicit unfolding selectors; full-file seals cover implicit reduction.

Foreign definitions come from the actual full-closure Lean catalogs emitted by
the seal harness. Local binders/lets and declarations of the source file are
excluded. Ambiguous short names are conservatively reported with all matches.
The line-set comparison uses declaration and selector text, not shifting lines.
"""
import difflib
import hashlib
import json
from pathlib import Path
import re
import runpy
import subprocess

headers = runpy.run_path(str(Path(__file__).with_name('frozen_headers.py')))
names = runpy.run_path(str(Path(__file__).with_name('name_clash_all.py')))
base, mask = headers['BASE'], headers['mask']
files = list(headers['FILES'])
for directory in ['TCSlib/Complexity/Randomized/SeedMajority',
                  'TCSlib/Cryptography/Randomness/Derandomization']:
    files += [str(path) for path in sorted(Path(directory).rglob('*.lean'))]
catalog = {}
for folder in [Path('evidence/seals'),
               Path('/Users/seyoonr/.codex/worktrees/derand/tcslib-exchange/evidence/seals')]:
    for path in folder.rglob('*.log'):
        for line in path.read_text().splitlines():
            match = re.match(r'^DERAND-CATALOG \S+ (\{.*\})$', line)
            if match:
                row = json.loads(match[1])
                if row['status'] != '[reducible]' or row['matcher']:
                    catalog[row['name']] = row
selector = re.compile(r'\b(?:unfold|delta)\s+([^\n;]+)|'
                      r'\b(?:simp_all|simp|simpa|dsimp|rw|erw)\b\s*'
                      r'(?:(?:only|!|\?)\s*)?\[([^\]]*)\]', re.S)
identifier = re.compile(r'[A-Za-z_][A-Za-z_0-9\u2080-\u2089]*(?:\.[A-Za-z_][A-Za-z_0-9\u2080-\u2089]*)*')

def unfolding_heads(match):
    if match[1] is not None:
        body = re.split(r'\bat\b', match[1], maxsplit=1)[0]
        return identifier.findall(body)
    body = match[2]
    pieces, start, depth = [], 0, 0
    for index, character in enumerate(body):
        if character in '([{':
            depth += 1
        elif character in ')]}':
            depth -= 1
        elif character == ',' and depth == 0:
            pieces.append(body[start:index])
            start = index + 1
    pieces.append(body[start:])
    result = []
    for piece in pieces:
        piece = piece.strip().removeprefix('←').strip()
        if piece.startswith('-'):
            continue
        found = identifier.match(piece)
        if found and found[0] not in {'show', 'by', 'fun', 'if'}:
            result.append(found[0])
    return result

def scan(path, source):
    home = path[:-5].replace('/', '.')
    masked = mask(source)
    declarations = names['declarations'](path, source)
    own = {row['name'].rsplit('.', 1)[-1] for row in declarations}
    locals_ = set(re.findall(r'\b(?:let|have)\s+([A-Za-z_][A-Za-z_0-9]*)', masked))
    locals_.update(re.findall(r'[({]\s*([A-Za-z_][A-Za-z_0-9]*)\s*:', masked))
    result = []
    for match in selector.finditer(masked):
        body = match[1] if match[1] is not None else match[2]
        line = masked.count('\n', 0, match.start()) + 1
        declaration = next((row['name'] for row in reversed(declarations) if row['line'] <= line), '')
        for token in unfolding_heads(match):
            if '.' not in token and (token in locals_ or token in own):
                continue
            candidates = [row for name, row in catalog.items()
                          if (name == token or name.endswith('.' + token)) and row['home'] != home]
            if not candidates:
                continue
            key = (path, declaration, ' '.join(match[0].split()), token,
                   tuple(sorted(row['name'] for row in candidates)))
            result.append(dict(path=path, line=line, declaration=declaration,
                               selector=match[0], token=token,
                               candidates=sorted(row['name'] for row in candidates),
                               A_strict=[row['name'] for row in candidates
                                         if row['name'] != 'Complexity.PolyExpr.eval'],
                               B_strict=[row['name'] for row in candidates],
                               A_coe=[row['name'] for row in candidates
                                      if row['name'] != 'Complexity.PolyExpr.eval'
                                      and not (row['instance'] and row['projection_coercion'])],
                               B_coe=[row['name'] for row in candidates
                                      if not (row['instance'] and row['projection_coercion'])],
                               key=key))
    return result

before, after, sources = [], [], []
for path in files:
    result = subprocess.run(['git', 'show', f'{base}:{path}'], text=True, capture_output=True)
    if result.returncode == 0:
        before += scan(path, result.stdout)
    current = Path(path).read_text()
    after += scan(path, current)
    sources.append(dict(path=path, final_sha256=hashlib.sha256(current.encode()).hexdigest(),
                        base_present=result.returncode == 0))
old = {repr(row['key']) for row in before}
added = [row for row in after if repr(row['key']) not in old]
out = Path('evidence/unfold')
out.mkdir(parents=True, exist_ok=True)
for filename, rows in [('base.json', before), ('final.json', after), ('added.json', added),
                       ('sources.json', sources)]:
    (out / filename).write_text(json.dumps(rows, indent=2) + '\n')
print(f'Catalog: {len(catalog)} imported non-reducible definitions/matchers')
print(f'Explicit foreign selector sites: base={len(before)} final={len(after)} added={len(added)}')
for row in added:
    print(f'{row["path"]}:{row["line"]}: {row["token"]}: {row["candidates"]}')
print('EXPLICIT UNFOLD SCAN ' + ('PASS' if not added else 'REVIEW'))
raise SystemExit(bool(added))
