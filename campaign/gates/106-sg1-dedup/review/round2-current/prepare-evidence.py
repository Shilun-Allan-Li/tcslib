"""Read-only current-source capture and probe preparation; never executes delivered tooling."""
import datetime
import difflib
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True

OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[4]
SCRATCH = Path(os.environ['TCSLIB_SCRATCH'])
WT = SCRATCH / 'wt-sg1'
GATE = ROOT / 'campaign/gates/106-sg1-dedup'
spec = importlib.util.spec_from_file_location('source_tools', OUT / 'source_tools.py')
source_tools = importlib.util.module_from_spec(spec)
spec.loader.exec_module(source_tools)
FILES = (GATE / 'evidence/current/screen/population-head.txt').read_text().splitlines()
assert len(FILES) == len(set(FILES)) == 9

def sha(data): return hashlib.sha256(data).hexdigest()
def write(name, text):
    path = OUT / name
    assert not path.exists(), path
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)
def capture(root):
    return {p.relative_to(root).as_posix(): sha(p.read_bytes()) for p in sorted((root / 'TCSlib').rglob('*.lean'))}
def exact_declaration(text, qualified):
    d = next(d for d in source_tools.decls(text) if d['name'] == qualified)
    last = d['start'] - 1 + max(i + 1 for i, line in enumerate(d['code'].splitlines()) if line.strip())
    return d, ''.join(text.splitlines(keepends=True)[d['start']-1:last])

base_tree, head_tree = capture(ROOT), capture(WT)
changed = sorted(f for f in base_tree.keys() | head_tree.keys() if base_tree.get(f) != head_tree.get(f))
assert len(changed) == 5 and set(changed) <= set(FILES), changed
comparison, pins = {}, {}
diff = []
for file in FILES:
    a, b = (ROOT / file).read_text(), (WT / file).read_text()
    write('base-source/' + file + '.txt', a)
    write('head-source/' + file + '.txt', b)
    r = source_tools.compare(a, b)
    am, bm = ({d['name']:d for d in source_tools.decls(t)} for t in (a,b))
    r['private_header_changes'] = [n for n in am.keys() & bm.keys() if am[n]['private'] and am[n]['header'] != bm[n]['header']]
    r['private_definition_changes'] = [n for n in am.keys() & bm.keys() if am[n]['private'] and bm[n]['kind'] not in ('theorem','lemma') and source_tools.norm(am[n]['code']) != source_tools.norm(bm[n]['code'])]
    r['surviving_private_order_unchanged'] = [n for n in am if am[n]['private'] and n in bm] == [n for n in bm if bm[n]['private'] and n in am]
    for key in ['public_added','public_removed','visibility_changes','public_header_changes','private_header_changes','public_definition_changes','private_definition_changes']:
        assert not r[key], (file, key, r[key])
    assert r['public_order_unchanged'] and r['surviving_private_order_unchanged']
    if file.endswith(('SAT.lean','Hardness.lean')):
        assert not r['private_added'] and not r['private_removed'] and len(r['private_changed']) == 1, (file,r['private_changed'])
    assert r['imports_before'] == r['imports_after'] or file.endswith(('Tautology.lean','SingleTape.lean'))
    comparison[file] = r
    pins[file] = dict(base_sha256=sha(a.encode()), head_sha256=sha(b.encode()),
                      head_git_blob_sha1=hashlib.sha1(('blob '+str(len(b.encode()))+'\0').encode()+b.encode()).hexdigest(),
                      base_bytes=len(a.encode()), head_bytes=len(b.encode()))
    diff.extend(difflib.unified_diff(a.splitlines(keepends=True),b.splitlines(keepends=True),fromfile='base/'+file,tofile='head/'+file))
write('source-comparison.json', json.dumps(comparison,indent=2)+'\n')
write('current-source.diff', ''.join(diff))
write('population.txt','\n'.join(FILES)+'\n')
write('tree-hashes.json',json.dumps(dict(base=base_tree,head=head_tree),indent=2)+'\n')
old = json.loads((GATE / 'evidence/current-after-natbits/receipt.json').read_text())
identity=[]
for row in old['audited_scope']:
    f=row['path']
    assert pins[f]['head_sha256']==row['source_sha256']
    assert pins[f]['head_git_blob_sha1']==row['audited_blob']==row['current_blob']
    identity.append(dict(path=f,sha256=pins[f]['head_sha256'],git_blob_sha1=pins[f]['head_git_blob_sha1'],unchanged_from_msg3_and_audited_head=True))
applied=json.loads((GATE / 'evidence/round2/applied-guard-patches.json').read_text())
for row in applied['source_files']:
    assert pins[row['path']]['head_sha256']==row['after_sha256']

seal='attribute [local irreducible] Turing.Segment\nattribute [-simp] Turing.Segment\n'
targets=[]
for short,file in [('SAT','TCSlib/Complexity/ClassNP/SAT.lean'),('Hardness','TCSlib/Complexity/CookLevin/Hardness.lean')]:
    qualified='Complexity.'+('sat_guard_add' if short=='SAT' else 'clA5_guard_add')
    text=(WT/file).read_text()
    d,raw=exact_declaration(text,qualified)
    assert not re.search(r'\b(?:simp|rw|unfold)\s*\[\s*(?:Turing\.)?Segment\b',raw)
    original_imports='\n'.join(source_tools.imports(text))+'\n'
    probe=original_imports+'\nset_option autoImplicit false\nset_option relaxedAutoImplicit false\n'+seal+'namespace Complexity\nopen Turing\n\n'+raw+'\n#print axioms '+qualified+'\nend Complexity\n'
    write('probes/GuardActual'+short+'.lean.txt',probe)
    write('exact-declarations/'+short+'.lean.txt',raw)
    targets.append(dict(path=file,qualified_name=qualified,line=d['start'],exact_declaration_sha256=sha(raw.encode()),header=d['header'],original_import_context_unchanged=True))
control=(GATE / 'review/guard-repair/probes/ControlsUnsealed.lean.txt').read_text()
write('probes/Controls-unsealed.lean.txt',control)
write('probes/Controls-sealed.lean.txt',control.replace('open Turing\n','open Turing\n'+seal,1))

modules=[f.removesuffix('.lean').replace('/','.') for f in FILES]
imports=''.join('import '+m+'\n' for m in modules)
census=imports+'''
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let wanted : List Name := ['''+', '.join('`'+m for m in modules)+''']
  for mod in wanted do
    unless (env.getModuleIdx? mod).isSome do throwError "missing imported module {mod}"
  let names := env.constants.toList.filterMap fun (n, ci) =>
    match env.getModuleIdxFor? n with
    | some i =>
      let mod := env.header.moduleNames[i.toNat]!
      if wanted.contains mod then some (n, ci, mod) else none
    | none => none
  for (n, ci, mod) in names.toArray.qsort (fun a b => a.1.toString < b.1.toString) do
    let kind := match ci with
      | .thmInfo _ => "theorem" | .defnInfo _ => "definition"
      | .opaqueInfo _ => "opaque" | .axiomInfo _ => "axiom"
      | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"
      | .inductInfo _ => "inductive" | .quotInfo _ => "quotient"
    logInfo m!"CONSTANT {n} module={mod} kind={kind} private={isPrivateName n} internal={n.isInternalDetail}"
    if n.toString.endsWith ".Complexity.sat_guard_add" || n.toString.endsWith ".Complexity.clA5_guard_add" then
      logInfo m!"GUARD {n} : {ci.type}"
      let ax ← Lean.collectAxioms n
      logInfo m!"GUARD_AXIOMS {n}: {ax}"
'''
write('probes/ModuleCensus.lean.txt',census)
axioms=imports+'\n'+''.join('#print axioms '+n+'\n' for n in ['Complexity.LogProg.halfL_run','Turing.RoundContract.counterLoopDone_traj','Turing.RoundContract.counterLoopEscape_traj','Turing.counterLoopTMVia_done_witness','Turing.counterLoopTMVia_escape_witness','Turing.counterLoopTMVia_run_done'])
write('probes/Axioms.lean.txt',axioms)
context=dict(at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    supplied_frozen_head='478cd3a8dfb46094b9d8b971662f2ddadb1eccdb',supplied_current_base='e3adffac67377a8b6e23bed74bfdbb44a123dd86',
    base_source=str(ROOT),head_source=str(WT),base_snapshot=str(SCRATCH/'oleans-mac3'),head_snapshot=str(SCRATCH/'oleans-msg4'),
    pin_method='Maintainer-supplied commit identities; full TCSlib Lean source tree and each nine-file body independently SHA256-captured. No Git command.',
    changed_files=changed,population=FILES,source_pins=pins,old_audited_blob_identity=identity,new_actual_seal_targets=targets,
    old_seals_not_rerun='Unchanged audited source bodies; prior seals retained as historical evidence, not claimed re-executed. Scope remains Segment and the isolated Frag cell read.',
    compiler_sha256={label:{f:sha((snap/(f.removesuffix('.lean')+'.olean')).read_bytes()) for f in FILES} for label,snap in [('base',SCRATCH/'oleans-mac3'),('head',SCRATCH/'oleans-msg4')]},
    replay_receipt_path='campaign/gates/106-sg1-dedup/evidence/round2/current-replay/receipt.json',
    replay_receipt_sha256=sha((GATE/'evidence/round2/current-replay/receipt.json').read_bytes()),
    no_new_replay=True,no_source_git_snapshot_cache_changes=True)
write('context.json',json.dumps(context,indent=2)+'\n')
print(json.dumps(dict(changed_files=changed,source_counts={f:dict(public=r['public_counts'],private=r['private_counts']) for f,r in comparison.items()},new_actual_targets=targets),indent=2))
