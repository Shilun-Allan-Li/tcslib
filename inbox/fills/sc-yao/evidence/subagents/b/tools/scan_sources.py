#!/usr/bin/env python3
"""Inventory the assigned sources and scan explicit unfolding syntax."""
import hashlib
import json
from pathlib import Path
import re

names = ['RunWithHost', 'Decryption', 'FirstTagged', 'EvalGate', 'GarbledRun', 'BobTables']
root = Path('TCSlib/Cryptography/SecureComputation/Yao/HybridProof')
def uncomment(source):
    out = []
    i = depth = 0
    string = False
    while i < len(source):
        if depth:
            if source.startswith('/-', i):
                depth += 1; out.extend('  '); i += 2
            elif source.startswith('-/', i):
                depth -= 1; out.extend('  '); i += 2
            else:
                out.append('\n' if source[i] == '\n' else ' '); i += 1
        elif string:
            if source[i] == '\\' and i + 1 < len(source):
                out.extend('  '); i += 2
            else:
                if source[i] == '"': string = False
                out.append('\n' if source[i] == '\n' else ' '); i += 1
        elif source.startswith('/-', i):
            depth = 1; out.extend('  '); i += 2
        elif source.startswith('--', i):
            end = source.find('\n', i)
            if end == -1: end = len(source)
            out.extend(' ' * (end - i)); i = end
        elif source[i] == '"':
            string = True; out.append(' '); i += 1
        else:
            out.append(source[i]); i += 1
    return ''.join(out)
rows = []
for name in names:
    path = root / (name + '.lean')
    source = path.read_text()
    code = uncomment(source)
    lines = source.splitlines()
    explicit = [{'line':code[:m.start()].count('\n')+1, 'syntax':m[0]}
                for m in re.finditer(r'\b(?:unfold|delta)\b[^\n]*', code)]
    dsimp = [{'line':code[:m.start()].count('\n')+1, 'syntax':m[0]}
             for m in re.finditer(r'\bdsimp\b[^\n]*', code)]
    rows.append(dict(file=str(path), source_sha256=hashlib.sha256(source.encode()).hexdigest(), lines=len(lines), width_violations=[i for i,s in
        enumerate(lines,1) if len(s)>100], explicit_unfold_or_delta=explicit,
        dsimp=dsimp, admissions=len(re.findall(r'\b(?:sorry|admit)\b', code))))
out = Path('evidence/subagents/b/source-scan.json')
out.write_text(json.dumps(rows, indent=2)+'\n')
assert all(not r['width_violations'] and r['lines'] < 1000 and
           not r['explicit_unfold_or_delta'] and not r['admissions'] for r in rows)
assert all(d['syntax'].strip() == 'dsimp only' for r in rows for d in r['dsimp'])
print('PASS: six sources, width<=100, lines<1000, no admission or explicit unfold/delta;')
print('the only dsimp is empty-target dsimp only, reducing local lets/beta expressions.')
