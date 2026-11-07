"""Prepare Gate06 collector and source metadata; run with python3 -I at the worktree.

No Lean process is launched here. The root coordinator runs probes serially only
after reconciling the library source and object fingerprints.
"""
from pathlib import Path
import hashlib
import importlib.util
import io
import json
import re
import subprocess
import sys
import tarfile

root = Path.cwd()
out = Path(sys.argv[1]).resolve()
scratch = root / '.lake/ps-maintainer/gate06/rule10'
out.mkdir(parents=True, exist_ok=True)
scratch.mkdir(parents=True, exist_ok=True)
base_ref = sys.argv[2] if len(sys.argv) > 2 else 'origin/cryptography/pass-shelat-ch2-4'
base = subprocess.check_output(['git', 'rev-parse', base_ref + '^{commit}'], text=True).strip()
head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip()
assert not subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=no'], text=True).strip()
subprocess.run(['git', 'merge-base', '--is-ancestor', base, head], check=True)
archive = subprocess.check_output(['git', 'archive', '--format=tar', head, '--', 'TCSlib', 'TCSlib.lean'])
with tarfile.open(fileobj=io.BytesIO(archive)) as saved:
    committed = {p.name: saved.extractfile(p).read() for p in saved.getmembers()
                 if p.isfile() and p.name.endswith('.lean')}
library_paths = {str(p.relative_to(root)) for p in (root / 'TCSlib').rglob('*.lean')} | {'TCSlib.lean'}
assert library_paths == set(committed), 'Untracked/ignored or missing library Lean source'
assert all((root / p).read_bytes() == b for p, b in committed.items()), 'Library source differs from pinned HEAD'
tools = root / 'briefs/pass-shelat-ch5-8/gates/08-shared/evidence/tools'
spec = importlib.util.spec_from_file_location('census', tools / 'sorrycensus.py')
lex = importlib.util.module_from_spec(spec)
spec.loader.exec_module(lex)
paths = subprocess.check_output(['git', 'diff', '--name-only', base, head, '--', '*.lean'], text=True).splitlines()
decl = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec)\s+)*(?:theorem|lemma|def|instance|structure|inductive|abbrev|class|opaque|axiom)\b', re.M)
targets = [p for p in paths if decl.search(lex.code_text((root / p).read_text()))]
assert all(p.startswith('TCSlib/') for p in targets)
excluded = [p for p in paths if p not in targets]
for p in excluded:
    active = [line.strip() for line in lex.code_text((root / p).read_text()).splitlines() if line.strip()]
    assert all(re.fullmatch(r'(?:import\s+\S+|set_option\s+\S+\s+\S+)', line) for line in active), \
        ('Excluded source has an active command other than imports/options', p, active)
modules = {p[:-5].replace('/', '.'): p for p in targets}

def imports(module):
    return re.findall(r'(?m)^import\s+(TCSlib\.\S+)', lex.code_text((root / (module.replace('.', '/') + '.lean')).read_text()))

def closure(module):
    found, stack = set(), imports(module)
    while stack:
        name = stack.pop()
        if name in found:
            continue
        found.add(name)
        stack.extend(imports(name))
    assert module not in found
    return sorted(found)

closures = {m: closure(m) for m in modules}
touched = {}
for module, path in modules.items():
    text = subprocess.check_output(['python3', '-I', str(tools / 'touched.py'), str(root), base, path], text=True)
    touched[module] = text.splitlines()

body = (tools / 'collect_body.lean').read_text()
assert 'ts.any fun t => s == t' in body
body = body.replace('ts.any fun t => s == t', 'ts.any fun t => t == "*" || s == t')
body = body.replace('for t in ts do\n    unless ours.any', 'for t in ts do\n    if t == "*" then continue\n    unless ours.any')
body = body.replace('if s == t || s.endsWith', 'if t == "*" || s == t || s.endsWith')
axiom_log = 'logInfo m!"AXIOMS {modN} | {s} | {axs.toList}"'
assert body.count(axiom_log) == 1
body = body.replace(axiom_log, axiom_log + '\n          logInfo m!"AXIOMSID {modN} | {n.toString} | display={s} | {axs.toList}"')
closure_body = r'''
syntax (name := closureSealCmd) "#sealclosure " ident "[" ident,* "]" : command
@[command_elab closureSealCmd] def closureSeal : CommandElab := fun stx => do
  let audited := stx[1].getId
  let deps := stx[3].getSepArgs.map Syntax.getId
  let env ← getEnv
  for dep in deps do
    unless (env.getModuleIdx? dep).isSome do throwError "missing dependency {dep}"
  let mut rows : Array String := #[]
  for (n, ci) in env.constants.map₁.toList do
    let some mi := env.getModuleIdxFor? n | continue
    let home := env.header.moduleNames[mi.toNat]!
    unless deps.contains home do continue
    unless ci.isDefinition do continue
    if isInstanceCore env n then continue
    let matcher := (Match.Extension.getMatcherInfo? env n).isSome
    let status ← liftCoreM <| getReducibilityStatus n
    if !matcher && status == .reducible then continue
    if n == `Complexity.PolyExpr.eval || n == `TCSlib.Cryptography.glNeed then continue
    rows := rows.push s!"CLOSUREROW {audited} | {n} | {home} | matcher={matcher} | {repr status}"
  for row in rows.qsort (· < ·) do logInfo m!"{row}"
'''
source = '\n'.join(['import Lean', *('import ' + m for m in modules), 'set_option maxHeartbeats 0', body, closure_body]) + '\n'
for module in modules:
    source += '#collect ' + module + ' ["*"]\n'
    source += '#axs ' + module + ' ["*"]\n'
    source += '#sealclosure ' + module + ' [' + ', '.join(closures[module]) + ']\n'
(scratch / 'Collect.lean').write_text(source)
(out / 'Collect.source.txt').write_text(source)
(out / 'modules.json').write_text(json.dumps(modules, indent=2) + '\n')
(out / 'touched.json').write_text(json.dumps(touched, indent=2) + '\n')
(out / 'closures.json').write_text(json.dumps(closures, indent=2) + '\n')
(out / 'source-fingerprints.json').write_text(json.dumps({p: hashlib.sha256((root / p).read_bytes()).hexdigest() for p in paths}, indent=2) + '\n')
(out / 'pins.json').write_text(json.dumps({'base': base, 'head': head, 'base_is_ancestor': True, 'library_sources_equal_head': True, 'untracked_or_ignored_library_lean_files': 0, 'library_git_tree': subprocess.check_output(['git', 'rev-parse', head + ':TCSlib'], text=True).strip(), 'changed_lean_files': len(paths), 'audited_math_modules': len(modules), 'excluded_import_option_only_files': excluded, 'collector_scope': 'all stored constants of every changed math module, including private/generated declarations, plus import-closure supplement', 'anonymous_limit': 'stored-constant collector does not discover all anonymous commands; complete import-closure supplement and controls are required'}, indent=2) + '\n')
(out / 'prepare_audit.py').write_bytes(Path(__file__).read_bytes())
print(json.dumps({'base': base, 'head': head, 'changed_lean_files': len(paths), 'audited_math_modules': len(modules)}))
