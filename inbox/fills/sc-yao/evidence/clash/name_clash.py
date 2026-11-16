#!/usr/bin/env python3
"""Resolve explicit source names, including private names, at all required comparison tips."""
import io
import json
from pathlib import Path
import re
import runpy
import subprocess
import tarfile

lexer = runpy.run_path('evidence/tools/header_lexer.py')
BASE = '6ce4658db08a1dc2a03a149987197660db078011'

def scan(source):
    code, _ = lexer['lex'](source)
    decl = lexer['DECL']
    commands = re.compile(r'^(namespace|section|end)\b([^\n]*)', re.M)
    events = sorted([(m.start(), 'decl', m) for m in decl.finditer(code)] +
                    [(m.start(), 'command', m) for m in commands.finditer(code)])
    stack, rows = [], []
    for offset, event, match in events:
        if event == 'command':
            kind, words = match.group(1), match.group(2).strip().split()
            if kind == 'end':
                if stack:
                    stack.pop()
            else:
                stack.append((kind, words[0] if kind == 'namespace' and words else ''))
            continue
        token = re.match(r'\s*([^\s({\[:=]+)', code[match.end():])
        if not token or token.group(1) in {'where', 'by'}:
            continue
        name = token.group(1)
        prefix = '.'.join(name for kind, name in stack if kind == 'namespace' and name)
        full = name[7:] if name.startswith('_root_.') else '.'.join(filter(None, [prefix, name]))
        rows.append(dict(name=full, short=name, line=source[:offset].count('\n') + 1,
                         private='private ' in match.group(0), kind=match.group('kind')))
    return rows

def tree(ref, prefix):
    archive = subprocess.check_output(['git', 'archive', ref, prefix])
    sources = {}
    with tarfile.open(fileobj=io.BytesIO(archive)) as tar:
        for member in tar.getmembers():
            if member.isfile() and member.name.endswith('.lean'):
                relative = member.name[len(prefix) + 1:] if prefix != 'TCSlib' else member.name
                sources[relative] = tar.extractfile(member).read().decode()
    return sources

comparisons = [dict(label='base', ref=BASE, prefix='TCSlib'),
               dict(label='sc-garble', ref='a73072f1', prefix='inbox/fills/sc-garble/src'),
               dict(label='sc-ot', ref='f62a25b3', prefix='TCSlib'),
               dict(label='sc-compose', ref='bdfdcb76', prefix='inbox/fills/sc-compose/src')]
catalogs = {}
base_sources = {}
for comparison in comparisons:
    sources = tree(comparison['ref'], comparison['prefix'])
    if comparison['label'] == 'base':
        base_sources = sources
    catalog = {}
    for path, source in sources.items():
        for row in scan(source):
            catalog.setdefault(row['name'], []).append(dict(path=path, **row))
    catalogs[comparison['label']] = catalog
    print('CATALOG', comparison['label'], comparison['ref'], len(sources), len(catalog))
changed = subprocess.check_output(['git', 'diff', '--name-only', BASE, '--', 'TCSlib'],
                                  text=True).splitlines()
changed += subprocess.check_output(['git', 'ls-files', '--others', '--exclude-standard', 'TCSlib'],
                                   text=True).splitlines()
results = []
conflicts = []
for path in sorted(set(changed)):
    if not path.endswith('.lean'):
        continue
    old_names = {r['name'] for r in scan(base_sources.get(path, ''))}
    for row in scan(Path(path).read_text()):
        if row['name'] in old_names:
            continue
        hits = {label: catalog[row['name']] for label, catalog in catalogs.items()
                if row['name'] in catalog}
        # The approved fan-in reader is the sole intentional overlap with sc-garble.
        allowed = (row['name'] == 'BoolCircuit.DAGCircuit.isFaninTwo_iff'
                   and set(hits) <= {'sc-garble'})
        status = 'SY3_APPROVED' if hits and allowed else 'CLASH' if hits else 'CLEAR'
        entry = dict(path=path, **row, status=status, hits=hits)
        results.append(entry)
        if status == 'CLASH':
            conflicts.append(entry)
out = Path('evidence/clash')
out.mkdir(parents=True, exist_ok=True)
(out / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
print('ADDED_EXPLICIT_NAMES', len(results), 'CLASHES', len(conflicts))
for conflict in conflicts:
    print(json.dumps(conflict))
print('Includes explicit public/private names, resolves namespace and section nesting.')
print('Generated descendants are additionally checked by downstream Lean elaboration.')
raise SystemExit(bool(conflicts))
