"""Check the added shared-file declaration names against the entire issue-base tree."""
import io
import json
from pathlib import Path
import re
import runpy
import subprocess
import tarfile

root = Path.cwd()
scanner = runpy.run_path(str(Path(__file__).with_name('frozen_headers.py')))
mask = scanner['mask']
base = scanner['BASE']
targets = {
    'Complexity.IterateFind.computesFunInTime_find': 'E1',
    'Complexity.mem_DTIME_iff': 'E2',
    'Turing.FinTM.decidesInTime_iff': 'E3',
    'Randomized.inBPP_iff': 'SR-01',
}
archive = subprocess.check_output(['git', 'archive', base, 'TCSlib'])
command = re.compile(
    r'^(?:(?:@\[[^\n]*\]|private|protected|noncomputable|unsafe|partial|nonrec|'
    r'local|scoped)\s+)*'
    r'(?:(namespace|section|end)\b(?:\s+([^\n]+))?|'
    r'(theorem|lemma|def|abbrev|structure|inductive|class|instance|axiom|opaque)'
    r'\s+([^\s(:\[{]+))')
hits = []
total = 0
with tarfile.open(fileobj=io.BytesIO(archive)) as tree:
    for member in tree:
        if not member.isfile() or not member.name.endswith('.lean'):
            continue
        total += 1
        src = tree.extractfile(member).read().decode()
        stack = []
        for line_number, line in enumerate(mask(src).splitlines(), 1):
            match = command.match(line)
            if not match:
                continue
            control, arg, kind, name = match.groups()
            if control == 'namespace':
                stack.append(('namespace', arg.strip()))
            elif control == 'section':
                stack.append(('section', arg.strip() if arg else ''))
            elif control == 'end':
                if stack:
                    stack.pop()
            else:
                namespaces = '.'.join(n for t, n in stack if t == 'namespace')
                full = (namespaces + '.' + name) if namespaces else name
                if full.startswith('_root_.'):
                    full = full[len('_root_.'):]
                if full in targets:
                    hits.append(dict(name=full, path=member.name, line=line_number, kind=kind))
out = Path('evidence/clash')
out.mkdir(parents=True, exist_ok=True)
(out / 'results.json').write_text(json.dumps(dict(base=base, files=total,
                                                targets=targets, collisions=hits), indent=2) + '\n')
for name, tag in targets.items():
    found = [h for h in hits if h['name'] == name]
    print(f'{tag} {name}: {len(found)} issue-base declarations')
    for h in found:
        print(f'  {h["path"]}:{h["line"]} {h["kind"]}')
print(f'NAME CLASH {"PASS" if not hits else "FAIL"}: {total} Lean files; '
      f'{len(targets)} resolved names; {len(hits)} collisions')
raise SystemExit(bool(hits))
