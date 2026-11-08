from pathlib import Path
import json,hashlib
O=Path('/private/tmp/ab34-safe-run-bridge-refinement');P=O/'project';D=Path('/private/tmp/ab34-small-gate-drafts/124');E=D/'inputs/sg-extras'
s=(O/'ScopeNative.lean.txt').read_text();marker='/-- Safe runs are segments with one forbidden control state and a trivial head invariant. -/';assert s.count(marker)==1
rows=json.loads((E/'definition-inventories.json').read_text());old=next(r for r in rows if r['context']=='SafeRun');guards=old['guards'];simp=old['default_simp_definitions_removed'];assert len(guards)==7 and simp==['Turing.Action.apply']
start='section BridgeOpacity\nattribute [-simp] Turing.Action.apply\n';line='attribute [local irreducible] '+' '.join(guards)+'\n'
assert s.endswith('end Turing\n');body=s[:-len('end Turing\n')];trailer='\n#print axioms safeRun_iff_segment\n#print axioms SafeRun.zero\n#print axioms SafeRun.cons\n#print axioms SafeRun.trans\nend BridgeOpacity\nend Turing\n'
for sealed in [False,True]:
 name='Scope'+('Sealed' if sealed else 'GuardNative');out=body.replace(marker,start+(line if sealed else '')+marker)+trailer
 (O/(name+'.lean.txt')).write_text(out);(P/(name+'.lean')).write_text(out)
for mode in ['native','sealed']:
 s=(E/('SafeRun-controls-'+mode+'.lean.txt')).read_text();assert s.count('OvernightSafeRunRfl_')==1;s=s.replace('OvernightSafeRunRfl_','BridgeSafeRunRfl_');name='Controls'+mode.title();(O/(name+'.lean.txt')).write_text(s);(P/(name+'.lean')).write_text(s)
a=(O/'ScopeGuardNative.lean.txt').read_text();b=(O/'ScopeSealed.lean.txt').read_text();assert a==b.replace(line,'',1)
a=(O/'ControlsNative.lean.txt').read_text();b=(O/'ControlsSealed.lean.txt').read_text();assert a==b.replace(line,'',1)
identities=next(r for r in json.loads((E/'control-identities.json').read_text()) if r['context']=='SafeRun')['identities'];identities=[dict(r,kernel_name=r['kernel_name'].replace('OvernightSafeRunRfl_','BridgeSafeRunRfl_')) for r in identities]
for filename in ['ScopeGuardNative.lean.txt','ScopeSealed.lean.txt']:
 t=(O/filename).read_text();assert (O/'private-bridge.lean.txt').read_text() in t
 for row in json.loads((O/'public-three-chunk-map.json').read_text()):assert t.count(row['new'])==1
original_imports=[l for l in (O/'owner-before.lean.txt').read_text().splitlines() if l.startswith('import ')]
for filename in ['ScopeGuardNative.lean.txt','ScopeSealed.lean.txt','ControlsNative.lean.txt','ControlsSealed.lean.txt']:
 t=(O/filename).read_text();assert [l for l in t.splitlines() if l.startswith('import ')]==original_imports+['import Lean']
(O/'guard-context.json').write_text(json.dumps({'four_complete_proof_roots':['Turing.safeRun_iff_segment','Turing.SafeRun.zero','Turing.SafeRun.cons','Turing.SafeRun.trans'],'same_original_imports':original_imports,'diagnostic_import':'Lean','guards':guards,'default_simp_definitions_removed_in_both_modes':simp,'native_sealed_differ_only_by_guard_line':True,'all_four_proof_chunks_exact':True,'fresh_control_identities':identities,'fresh_positive_negative_count':len(identities),'guard_line':line.strip()},indent=2)+'\n')
print('Prepared all FOUR exact proof bodies in paired guard contexts and 14 fresh paired controls.')
