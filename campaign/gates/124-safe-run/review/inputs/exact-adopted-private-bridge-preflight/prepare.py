from pathlib import Path
import re,json,hashlib,difflib
O=Path('/private/tmp/ab34-safe-run-bridge-refinement');D=Path('/private/tmp/ab34-small-gate-drafts/124');P=O/'project';rel='TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean';old=(D/'source/HEAD'/(rel+'.txt')).read_text();s=old
bridge='''/-- Safe runs are segments with one forbidden control state and a trivial head invariant. -/
private theorem safeRun_iff_segment {H : MultiTapeTM k Bool B} {avoid : B}
    {c c' : Cfg k Bool B x} {t : ℕ} :
    SafeRun H avoid c t c' ↔ Segment H {some avoid} (fun _ => True) c c' t := by
  simp only [SafeRun, segment_iff, Set.mem_singleton_iff, implies_true, and_true]
'''
marker='/-- The empty run is safe. -/';assert s.count(marker)==1;s=s.replace(marker,bridge+'\n'+marker)
rows=json.loads((D/'inputs/sg-extras/chunk-mappings.json').read_text());replacements={
'SafeRun.zero':'''  exact safeRun_iff_segment.mpr (Segment.zero True.intro)''',
'SafeRun.cons':'''  apply safeRun_iff_segment.mpr
  simpa only [Nat.add_comm 1 t] using
    (Segment.cons hstep (by simpa only [Set.mem_singleton_iff] using hc)
      True.intro (safeRun_iff_segment.mp h))''',
'SafeRun.trans':'''  exact safeRun_iff_segment.mpr
    (Segment.trans (safeRun_iff_segment.mp h₁) (safeRun_iff_segment.mp h₂))'''}
chunks=[]
for r in rows:
 if r['name'] not in replacements:continue
 prior=r['new_chunk'];header=prior.split(':= by\n',1)[0]+':= by\n';new=header+replacements[r['name']];assert s.count(prior)==1;s=s.replace(prior,new);chunks.append({'name':'Turing.'+r['name'],'old':prior,'new':new,'header_exact':prior.split(':= by',1)[0]==new.split(':= by',1)[0]})
assert len(chunks)==3
(O/'owner-before.lean.txt').write_text(old);(O/'owner-proposed.lean.txt').write_text(s);(O/'private-bridge.lean.txt').write_text(bridge);(O/'public-three-chunk-map.json').write_text(json.dumps(chunks,indent=2,ensure_ascii=False)+'\n');(O/'bridge-refinement.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),s.splitlines(True),fromfile='a/'+rel,tofile='b/'+rel)))
imports='\n'.join(l for l in old.splitlines() if l.startswith('import '))+'\nimport Lean\nset_option maxHeartbeats 0\nset_option relaxedAutoImplicit false\nset_option autoImplicit false\nnamespace Turing\nopen MultiTapeTM\nvariable {k m : ℕ} {B SS : Type} {x : List Bool}\n'
a=old.index('/-- A run from `c`');b=old.index('/-- The empty run is safe. -/');safe_def=old[a:b]
scope=imports+safe_def+bridge+'\n'+'\n\n'.join(r['new'] for r in chunks)+'\nend Turing\n'
(O/'ScopeNative.lean.txt').write_text(scope);(P/'ScopeNative.lean').write_text(scope)
invsrc=Path('/private/tmp/ab34-ch7-run-seals-v2/Inventory.lean.txt').read_text();tail=invsrc[invsrc.index('open Lean Elab Command Meta'):]
print('inventory_template_tail',tail[:250])
# Use the tested bounded traversal: each root's type/value, referenced definition
# type/value, and imported theorem TYPES; imported theorem values remain boundaries.
code=Path('/private/tmp/ab34-overnight-sg1-extras/prepare-inventories.py').read_text();template=code.split("template='''",1)[1].split("'''",1)[0]
root_names=['Turing.safeRun_iff_segment','Turing.SafeRun.zero','Turing.SafeRun.cons','Turing.SafeRun.trans'];inventory=scope+template.replace('ROOTS',json.dumps(root_names));(O/'Inventory.lean.txt').write_text(inventory);(P/'Inventory.lean').write_text(inventory)
# Complete owner with only a diagnostic Lean import added; library candidate is
# separately captured byte for byte and actual source worktree is never written.
native=s.replace('import TCSlib.Complexity.TuringMachine.Build.Embed\n','import TCSlib.Complexity.TuringMachine.Build.Embed\nimport Lean\n')
if 'import Lean\n' not in native:
 last=max(m.end() for m in re.finditer(r'^import[^\n]*\n',native,re.M));native=native[:last]+'import Lean\n'+native[last:]
metadata=(D/'selected-metadata-probe.lean.txt').read_text();body=metadata[metadata.index('open Lean Elab Command Meta'):];body=body.replace('((env.getModuleIdxFor? n).any fun i => env.header.moduleNames[i.toNat]!.toString == owner)','(env.getModuleIdxFor? n).isNone')
native=native+'\n'+body;(O/'OwnerNative.lean.txt').write_text(native);(P/'OwnerNative.lean').write_text(native)
(O/'source-binding.json').write_text(json.dumps({'actual_old_head':'535c0043310bb3ad6efd9359aef62518699b7de8','base':'9b5dcf46408db681bcbc721930ef2203fa6bc47d','owner':rel,'old_sha256':hashlib.sha256(old.encode()).hexdigest(),'proposed_sha256':hashlib.sha256(s.encode()).hexdigest(),'new_private_helper':'Turing.safeRun_iff_segment','new_public_API':False,'source_worktree_Git_canonical_or_snapshot_mutation':False,'root_adoption_pending':True},indent=2)+'\n')
print('Prepared one private bridge plus three public-header-exact consumers, complete owner and four-proof scope.')
