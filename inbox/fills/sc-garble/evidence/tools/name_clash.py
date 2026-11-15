#!/usr/bin/env python3
"""Resolve source namespaces and compare every added explicit name with the base tree."""
import importlib.util
import io
import json
from pathlib import Path
import re
import subprocess
import tarfile

spec = importlib.util.spec_from_file_location('headers', 'evidence/tools/check_headers.py')
headers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(headers)
base = headers.BASE

def scan(text):
    code, _ = headers.lex(text)
    decl = re.compile(headers.DECL.pattern.replace('^', '^[ \\t]*', 1), re.M)
    commands = re.compile(r'^[ \t]*(namespace|section|end)\b([^\n]*)', re.M)
    events = sorted([(m.start(), 'decl', m) for m in decl.finditer(code)] +
                    [(m.start(), 'command', m) for m in commands.finditer(code)])
    stack, result = [], []
    for offset, kind, match in events:
        if kind == 'command':
            action, name = match.group(1), match.group(2).strip().split()
            if action == 'end':
                if stack: stack.pop()
            else:
                stack.append((action, name[0] if action == 'namespace' and name else ''))
            continue
        rest = code[match.end():]
        token = re.match(r'\s*([^\s({\[:=]+)', rest)
        if token is None: continue
        name = token.group(1)
        if name in ('where', 'by'): continue
        prefix = '.'.join(x[1] for x in stack if x[0] == 'namespace' and x[1])
        full = name[len('_root_.'):] if name.startswith('_root_.') else '.'.join(
            x for x in (prefix, name) if x)
        result.append(dict(name=full, short=name,
            line=text[:offset].count('\n')+1, kind=match.group('kind')))
    return result

archive = subprocess.check_output(['git','archive',base,'TCSlib'])
catalog, sources = {}, {}
with tarfile.open(fileobj=io.BytesIO(archive)) as tar:
    for member in tar.getmembers():
        if member.isfile() and member.name.endswith('.lean'):
            text = tar.extractfile(member).read().decode()
            sources[member.name] = text
            for row in scan(text):
                catalog.setdefault(row['name'], []).append(dict(path=member.name, **row))
changed = subprocess.check_output(['git','diff','--name-only',base,'--','TCSlib']).decode().splitlines()
changed += subprocess.check_output(['git','ls-files','--others','--exclude-standard','TCSlib']).decode().splitlines()
results, conflicts = [], []
for path in sorted(set(changed)):
    if not path.endswith('.lean'): continue
    old_names = {x['name'] for x in scan(sources.get(path, ''))}
    for row in scan(Path(path).read_text()):
        if row['name'] in old_names: continue
        hits = catalog.get(row['name'], [])
        allowed = [x for x in hits if x['path'].endswith('/SpecialEncryptionMulti.lean') and
                   x['short'] in headers.REMOVALS]
        status = 'SG1_REPLACEMENT' if hits and len(allowed)==len(hits) else 'CLASH' if hits else 'CLEAR'
        entry = dict(path=path, **row, status=status, base_hits=hits)
        results.append(entry)
        if status == 'CLASH': conflicts.append(entry)
out = Path('evidence/clash')
out.mkdir(parents=True,exist_ok=True)
(out/'results.json').write_text(json.dumps(results,indent=2)+'\n')
print('BASE_SOURCE_FILES',len(sources),'BASE_EXPLICIT_NAMES',len(catalog))
print('ADDED_EXPLICIT_NAMES',len(results),'SG1_REPLACEMENTS',sum(x['status']=='SG1_REPLACEMENT' for x in results))
print('CLASHES',len(conflicts))
for entry in conflicts: print(entry)
print('Scope: explicit public and private source declarations, namespaces resolved; generated')
print('descendants are additionally checked by the required downstream Lean sweep at final.')
if conflicts: raise SystemExit(1)
