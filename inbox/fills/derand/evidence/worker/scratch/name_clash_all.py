"""Resolve source declaration names and compare every addition with the whole issue base."""
import io
import json
from pathlib import Path
import re
import runpy
import subprocess
import tarfile

scanner = runpy.run_path(str(Path(__file__).with_name('frozen_headers.py')))
mask, base = scanner['mask'], scanner['BASE']
command = re.compile(
    r'^(?:(?:@\[[^\n]*\]|private|protected|noncomputable|unsafe|partial|nonrec|'
    r'local|scoped)\s+)*'
    r'(?:(namespace|section|end)\b(?:\s+([^\n]+))?|'
    r'(theorem|lemma|def|abbrev|structure|inductive|class|instance|axiom|opaque)'
    r'\s+([^\s(:\[{]+))')

def declarations(path, source):
    result, stack = [], []
    for line_number, line in enumerate(mask(source).splitlines(), 1):
        match = command.match(line)
        if not match:
            continue
        control, argument, kind, name = match.groups()
        if control == 'namespace':
            stack.append(('namespace', argument.strip()))
        elif control == 'section':
            stack.append(('section', argument.strip() if argument else ''))
        elif control == 'end':
            if stack:
                stack.pop()
        else:
            namespace = '.'.join(n for t, n in stack if t == 'namespace')
            full = name[len('_root_.'):] if name.startswith('_root_.') else (
                namespace + '.' + name if namespace else name)
            result.append(dict(name=full, path=path, line=line_number, kind=kind,
                               private=bool(re.match(r'^(?:@\[[^\n]*\]\s*)*private\b', line))))
    return result

catalog, base_by_path = [], {}
archive = subprocess.check_output(['git', 'archive', base, 'TCSlib'])
with tarfile.open(fileobj=io.BytesIO(archive)) as tree:
    for member in tree:
        if not member.isfile() or not member.name.endswith('.lean'):
            continue
        rows = declarations(member.name, tree.extractfile(member).read().decode())
        base_by_path[member.name] = rows
        catalog.extend(rows)
files = list(scanner['FILES'])
for directory in ['TCSlib/Complexity/Randomized/SeedMajority',
                  'TCSlib/Cryptography/Randomness/Derandomization']:
    files += [str(path) for path in sorted(Path(directory).rglob('*.lean'))]
added = []
for path in files:
    old = {row['name'] for row in base_by_path.get(path, [])}
    added += [row for row in declarations(path, Path(path).read_text()) if row['name'] not in old]
names = {row['name'] for row in added}
collisions = [row for row in catalog if row['name'] in names]
out = Path('evidence/clash/all-additions')
out.mkdir(parents=True, exist_ok=True)
(out / 'base-catalog.json').write_text(json.dumps(catalog, indent=2) + '\n')
(out / 'results.json').write_text(json.dumps(dict(base=base, files=len(base_by_path),
    additions=added, collisions=collisions), indent=2) + '\n')
for row in added:
    print(f'{row["name"]}: {sum(hit["name"] == row["name"] for hit in collisions)} collisions')
print(f'NAME CLASH {"FAIL" if collisions else "PASS"}: {len(base_by_path)} base Lean files; '
      f'{len(added)} additions; {len(collisions)} collisions')
raise SystemExit(bool(collisions))
