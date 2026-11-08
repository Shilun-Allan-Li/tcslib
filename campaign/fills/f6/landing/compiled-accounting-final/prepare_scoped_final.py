from pathlib import Path
import json,hashlib,re,datetime
O=Path('/private/tmp/f6-compiled-accounting-final');R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');L=R/'campaign/fills/f6/landing';D=O/'scoped-seals-final';assert not D.exists();D.mkdir();c=json.loads((O/'context.json').read_bytes());pre=L/'seam-step-repoint-preflight';old=L/'scoped-seals-v1';meta=json.loads((old/'preparation.json').read_bytes())
def sha(b):return hashlib.sha256(b).hexdigest()
# Review establishes exact native source and exactly19 attribute scopes; no other generated code.
source=(O/'Hierarchy-head.lean.txt').read_bytes();native=(pre/'Owner-native-with-axioms.lean.txt').read_bytes();sealed=(pre/'Owner-sealed-with-axioms.lean.txt').read_bytes()
append=b'\n#print axioms Complexity.space_universal\n#print axioms Complexity.f6_seam\n#print axioms Turing.seamCompTM_step\n';assert native==source+append
line=b'attribute [local irreducible] '+' '.join(meta['guards']).encode()+b'\n';nosimp=b'attribute [-simp] '+' '.join(meta['simp_unfold_disabled']).encode()+b'\n';recover=sealed;scopes=[]
for i,name in enumerate(meta['sections'],1):
 n=f'F6LandingSeal{i:02d}';prefix=b'section '+n.encode()+b'\n'+line+nosimp+b'\n';suffix=b'end '+n.encode()+b'\n'
 assert recover.count(prefix)==recover.count(suffix)==1;start=recover.index(prefix);end=recover.index(suffix,start);body=recover[start+len(prefix):end]
 # The complete named target header and body lie after the guard and before closing section.
 leaf=name.split('.')[-1];assert re.search(rb'^(?:private )?theorem '+re.escape(leaf.encode())+rb'\b',body,re.M)
 scopes.append({'ordinal':i,'section':n,'target':name,'guards_before_complete_doc_header_body':True,'scoped_body_sha256':sha(body)})
 recover=recover.replace(prefix,b'',1).replace(suffix,b'',1)
assert recover==native and len(scopes)==19 and len(meta['guards'])==36
assert set(meta['guards'])==set(json.loads((pre/'context.json').read_bytes())['guards'])
# The already-read control code uses default MetaM refl, point+whole-function goals and kernel declarations.
pos=(old/'Controls-native.lean.txt').read_bytes();neg=(old/'Controls-sealed.lean.txt').read_bytes();assert b'goal.mvarId!.refl' in pos and b'withTransparency' not in pos and b'allowUnsafeReducibility' not in pos
assert neg.replace(line+nosimp,b'',1)==pos
names=(old/'control-definitions.txt').read_text().splitlines();assert names==meta['guards'];assert len(set(names))==36
for name,b in [('Owner-native.lean.txt',native),('Owner-sealed.lean.txt',sealed),('Controls-native.lean.txt',pos),('Controls-sealed.lean.txt',neg),('control-definitions.txt',(old/'control-definitions.txt').read_bytes())]:(D/name).write_bytes(b)
# Save hashes of every trusted source artifact, plus complete scope mapping and limits.
inputs=[]
for p in [pre/'Owner-native-with-axioms.lean.txt',pre/'Owner-sealed-with-axioms.lean.txt',old/'Controls-native.lean.txt',old/'Controls-sealed.lean.txt',old/'control-definitions.txt',old/'preparation.json',old/'verify-controls.py']:
 b=p.read_bytes();inputs.append({'path':str(p.relative_to(R)),'bytes':len(b),'sha256':sha(b)})
(D/'source-equivalence.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_head':c['candidate_head'],'source_sha256':sha(source),'native_exact_current_source_plus_only3AXprints':True,'sealed_inverse_exact_native':True,'scope_count':19,'scopes':scopes,'guards':names,'TCSlib_effective_guards':35,'extra_Mathlib_guard':'Nat.bits','nosimp':meta['simp_unfold_disabled'],'paired_controls':72,'control_source_guard_only_difference':True,'default_MetaM_refl_no_transparency_override':True,'no_unsafe_reducibility_override':True,'excluded_regular_Fintype_instances':meta['excluded_regular_instances'],'other_limits':'14abbreviation/projections; two ineffective regular Fintype-instance controls remain separately disclosed. No blanket global/imported-theorem proof seal.','exact_reused_inputs':inputs},indent=2)+'\n')
print('Prepared exact current19-scoped owner and72control inputs; no Lean run by preparation')
