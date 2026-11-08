#!/usr/bin/env python3
"""Generate the census probe for a phase: imports every owned module, then #cp2dump, #cp2axioms,
#cp2c3 and one #cp2closure per owned module (its TCSlib import closure from source imports); the
rows are written to files under <outdir> (names.tsv, axioms.tsv, c3.tsv, closure.tsv).
python3 -I gen_census.py <owned-files.txt> <out.lean> <outdir>"""
import sys
sys.path.insert(0, '/workspace/cp2/tools')
import importlib.util
spec = importlib.util.spec_from_file_location('imports', '/workspace/cp2/tools/imports.py'); im = importlib.util.module_from_spec(spec); spec.loader.exec_module(im)
owned = [l.strip()[:-5].replace('/', '.') for l in open(sys.argv[1]) if l.strip()]
outdir = sys.argv[3]
core = open('/workspace/cp2/tools/lean/CensusCore.lean.txt').read()
dump = open('/workspace/cp2/tools/lean/NameDump.lean.txt').read()
out = [f'import {m}' for m in owned] + ['', 'set_option maxHeartbeats 0', f'def cp2OutDir : String := {outdir!r}'.replace("'", '"'), dump, '#cp2dump', core,
       '#cp2axioms [' + ', '.join(owned) + ']', '#cp2c3 [' + ', '.join(owned) + ']']
out.append('#cp2closures [' + ', '.join(owned) + ']')
open(sys.argv[2], 'w').write('\n'.join(out) + '\n')
print(len(owned), 'modules')
