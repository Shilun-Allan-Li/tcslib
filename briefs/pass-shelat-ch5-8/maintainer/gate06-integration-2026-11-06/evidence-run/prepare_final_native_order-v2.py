"""Derive the final native union with the reviewed header parser; never launch Lean."""
from pathlib import Path
import hashlib
import importlib.util
import json
import subprocess
import sys

sys.dont_write_bytecode = True
r = Path.cwd()
g = r / '.lake/ps-maintainer/gate06'
e = Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/evidence-run')
git = lambda *args: subprocess.check_output(['git', '--no-optional-locks', *args], text=True).strip()
head, base = git('rev-parse', 'HEAD'), git('rev-parse', sys.argv[1]+'^{commit}')
assert len(head) == len(base) == 40
assert not git('status', '--porcelain', '--untracked-files=no')
tool = g/'build_seals.py'
assert hashlib.sha256(tool.read_bytes()).hexdigest() == 'fae07000e8c3fda22225632ded45208e2651bab827d827639f48d46e2005347a'
spec = importlib.util.spec_from_file_location('final_native_headers', tool)
bs = importlib.util.module_from_spec(spec); spec.loader.exec_module(bs)
pins = {'base':base, 'head':head, 'base_is_ancestor':True, 'library_sources_equal_head':True,
        'untracked_or_ignored_library_lean_files':0, 'library_git_tree':git('rev-parse', head+':TCSlib')}
library, snapshot = bs.library_snapshot(r, pins)
changed = git('diff','--name-only',base,head,'--','*.lean').splitlines()
assert changed and all(p in library for p in changed)
roots = [p[:-5] for p in changed if p != 'TCSlib.lean'] + ['audits/pass-shelat/Checks']
headers, inputs, order, active, done, mathlib = {}, {}, [], set(), set(), set()
def visit(module):
    if module in done: return
    assert module not in active, ('import cycle', module)
    path = module+'.lean'
    if path in library: raw = library[path]
    else:
        assert module == 'audits/pass-shelat/Checks'
        raw = subprocess.check_output(['git','--no-optional-locks','show',head+':'+path])
        assert (r/path).read_bytes() == raw
    inputs[path] = hashlib.sha256(raw).hexdigest()
    headers[module] = bs.header(raw)['imports']
    active.add(module)
    for dep in headers[module]:
        if dep == 'TCSlib' or dep.startswith('TCSlib.'): visit(dep.replace('.','/'))
        elif dep.startswith('Mathlib.'): mathlib.add(dep)
    active.remove(module); done.add(module); order.append(module)
for module in sorted(set(roots)): visit(module)
old = (g/'order-current.txt').read_text().splitlines()
assert set(order) == set(old) and len(order) == len(old), 'Scope changed; require explicit reconciliation rather than overwrite'
old_positions = {m:i for i,m in enumerate(old)}
old_violations = [(m,d) for m,ds in headers.items() for d in ds if d.startswith('TCSlib.') and old_positions[d.replace('.','/')] >= old_positions[m]]
positions = {m:i for i,m in enumerate(order)}
assert all(positions[d.replace('.','/')] < positions[m] for m,ds in headers.items() for d in ds if d.startswith('TCSlib.'))
assert mathlib == set((g/'roots-current.txt').read_text().splitlines()), 'New Mathlib roots need narrowed fetch'
assert bs.library_snapshot(r,pins)[1] == snapshot
assert all(hashlib.sha256((r/p).read_bytes()).hexdigest()==v for p,v in inputs.items())
record = {'head':head, 'base':base, 'library_snapshot':snapshot, 'root_modules':sorted(set(roots)),
          'changed_lean_files':changed, 'native_modules':len(order), 'order':order, 'prior_order_violations':old_violations,
          'order_matches_fresh_union':True, 'order_is_topological':True, 'imports':headers,
          'source_sha256':inputs, 'mathlib_roots':sorted(mathlib), 'mathlib_roots_match_cached_scope':True,
          'header_tool_sha256':hashlib.sha256(tool.read_bytes()).hexdigest(),
          'prepare_tool_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
          'manifest_sha256':hashlib.sha256((r/'lake-manifest.json').read_bytes()).hexdigest(),
          'toolchain_sha256':hashlib.sha256((r/'lean-toolchain').read_bytes()).hexdigest(),
          'root_export_limit':'TCSlib.lean is byte/export pinned; native union builds changed facades and Checks but does not build the root aggregator.'}
for path, raw in [(e/'final-native-order-prep.json',(json.dumps(record,indent=2)+'\n').encode()),
                  (e/'final-native-order.txt',('\n'.join(order)+'\n').encode()),
                  (e/'prepare_final_native_order.py',Path(__file__).read_bytes())]:
    with path.open('xb') as handle: handle.write(raw)
print(json.dumps({'head':head,'base':base,'modules':len(order),'roots':len(set(roots)),'mathlib_roots':len(mathlib),'no_Lean_started':True}))
