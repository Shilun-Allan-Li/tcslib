"""Extend a copy of the brief's import probe by every other-file TCSlib name the audit walk finds
cited beyond the probes (python3 -I mkimportprobe.py <EDImportProbe> <EDImportProbe2> <audit.out> <out>).
Each added name gets `#check @name` and `#print axioms name`."""
import re, sys
p1, p2, audit, out = sys.argv[1:5]
base = open(p1, encoding='utf-8').read()
seen = set(re.findall(r'#check @(\S+)', base)) | set(re.findall(r'#check @(\S+)', open(p2, encoding='utf-8').read()))
seen |= {('Turing.' + s) for s in seen}
ext = [m.group(1) for m in (re.match(r'EXT (\S+) : (\S+)', l) for l in open(audit, encoding='utf-8')) if m]
add = [n for n in ext if n not in seen and n.split('.')[-1] not in {s.split('.')[-1] for s in seen if s.count('.') == 0}]
add = [n for n in ext if n not in seen]
lines = [base.rstrip(), '', '/-! ### E-D fill: names cited beyond the probes (from the audit walk) -/', '']
lines += [f'#check @{n}' for n in add] + [''] + [f'#print axioms {n}' for n in add]
open(out, 'w', encoding='utf-8').write('\n'.join(lines) + '\n')
print('probe names', len(seen), 'external names cited', len(ext), 'added', len(add))
