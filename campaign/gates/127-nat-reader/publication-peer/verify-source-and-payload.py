from pathlib import Path
import json,hashlib,subprocess,os
P=Path('/private/tmp/ab34-gate127-reader-repair-ready-draft');O=Path('/private/tmp/ab34-gate127-publication-peer');R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');env=dict(os.environ);env['GIT_OPTIONAL_LOCKS']='0';h=lambda b:hashlib.sha256(b).hexdigest();J=lambda p:json.loads(p.read_text())
def w(n,x):(O/n).write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
def git(*args):return subprocess.check_output(['git','-C',str(R),*args],env=env)
expected='d6a33e86030b20bbff564af997fda9078f65564bc6cf6be4c0ff2640544fbe5c';assert h((P/'MANIFEST.json').read_bytes())==expected;m=J(P/'MANIFEST.json');assert len(m['files'])==m['payload_file_count']==512
manifest_rows=[];actual={p.relative_to(P).as_posix() for p in P.rglob('*') if p.is_file()};assert not any(p.is_symlink() for p in P.rglob('*'))
for r in m['files']:
 p=P/r['path'];assert not Path(r['path']).is_absolute() and '..' not in Path(r['path']).parts;b=p.read_bytes();assert len(b)==r['bytes'] and h(b)==r['sha256'];b.decode('utf8');manifest_rows.append(dict(r,hash_bytes_UTF8_exact=True))
assert actual=={r['path'] for r in m['files']}|{'MANIFEST.json'} and sum(r['bytes'] for r in m['files'])==m['payload_bytes']==27388925
idx=J(P/'PAYLOAD-INDEX.json')['files'];assert len(idx)==511 and {r['path'] for r in idx}==actual-{'PAYLOAD-INDEX.json','MANIFEST.json'}
for r in idx:assert (P/r['path']).stat().st_size==r['bytes'] and h((P/r['path']).read_bytes())==r['sha256']
components=[]
for rel,count in [('inputs/exact-adopted-full-target-preflight',53),('historical-d725-packet',226)]:
 q=P/rel;c=J(q/'MANIFEST.json');assert len(c['files'])==c['payload_file_count']==count
 for r in c['files']:assert (q/r['path']).stat().st_size==r['bytes'] and h((q/r['path']).read_bytes())==r['sha256']
 assert {x.relative_to(q).as_posix() for x in q.rglob('*') if x.is_file()}=={r['path'] for r in c['files']}|{'MANIFEST.json'};components.append({'component':rel,'payloads':count,'manifest_SHA256':h((q/'MANIFEST.json').read_bytes()),'all_payloads_exact':True})
w('all512-payload-checks.json',{'input_MANIFEST_SHA256':expected,'payload_files':512,'payload_bytes':m['payload_bytes'],'actual_file_set_exact_no_symlinks':True,'all_UTF8':True,'PAYLOAD_INDEX_511_exact':True,'nested_manifests':components,'files':manifest_rows})
base='9b5dcf46408db681bcbc721930ef2203fa6bc47d';head='e16049ad20823b3e6abba171e328489746062080';trees={}
for ref in [base,head]:
 subprocess.run(['git','-C',str(R),'cat-file','-e',ref+'^{commit}'],env=env,check=True);raw=git('ls-tree','-r',ref).decode();trees[ref]={s.split('\t',1)[1]:s.split()[2] for s in raw.splitlines()};assert len([p for p in trees[ref] if p.endswith('.lean')])==1003
changed=[p for p in sorted(trees[base].keys()|trees[head].keys()) if p.endswith('.lean') and trees[base].get(p)!=trees[head].get(p)];assert changed==['TCSlib/Complexity/TuringMachine/CodeSimulator.lean']
sm=J(P/'replay/source-before.json');assert len(sm)==1003 and set(sm)=={p for p in trees[head] if p.endswith('.lean')}
# Read immutable object bytes only; no checkout, fetch, update-index, merge-tree or repository mutation.
ids=sorted({trees[head][p] for p in sm}|{trees[base][changed[0]]});proc=subprocess.run(['git','-C',str(R),'cat-file','--batch'],input=('\n'.join(ids)+'\n').encode(),capture_output=True,env=env,check=True);data=proc.stdout;pos=0;blobs={}
for oid in ids:
 end=data.index(b'\n',pos);got,kind,size=data[pos:end].decode().split();assert got==oid and kind=='blob';n=int(size);b=data[end+1:end+1+n];assert data[end+1+n:end+2+n]==b'\n';assert hashlib.sha1(('blob '+str(len(b))+'\0').encode()+b).hexdigest()==oid;blobs[oid]=b;pos=end+2+n
assert pos==len(data)
source_rows=[]
for p,r in sm.items():
 b=blobs[trees[head][p]];assert r=={'git_blob':trees[head][p],'sha256':h(b),'bytes':len(b)};source_rows.append({'path':p,**r,'actual_HEAD_Git_and_bytes_exact':True})
w('all1003-current-source-checks.json',{'head':head,'base':base,'all1003_actual_Git_blob_SHA_and_bytes_exact':True,'sole_changed_Lean_path':changed[0],'source_map':source_rows})
for phase,ref in [('BASE',base),('HEAD',head)]:
 a=J(P/(phase+'-export-source-map.json'));assert a['source_ref']==ref and a['canonical_TCSlib_plus_root_facade_Lean_count']==len(a['files'])==930
 for r in a['files']:
  p=r['path'];b=blobs[trees[ref][p]];assert len(b)==r['bytes'] and h(b)==r['sha256']
owner=changed[0];sb=blobs[trees[base][owner]].decode();sh=blobs[trees[head][owner]].decode();binding=J(P/'literal-source-and-scope-binding.json');bc=binding['BASE_complete_target_header_body'];hc=binding['HEAD_complete_target_header_body'];assert sb.count(bc)==sh.count(hc)==1 and sh.replace(hc,bc)==sb
assert hc.replace('    rw [← codeBitsNat_eq]\n','    change Nat.bit true (codeBitsNat w.length.bits + 1) = _\n',1).replace('    simp only [Nat.bit_val, Bool.toNat_true]\n','    simp [Nat.bit]\n',1)==bc
F=P/'inputs/exact-adopted-full-target-preflight';assert (F/'owner-proposed.lean.txt').read_text()==(F/'OwnerNative.lean.txt').read_text()==sh
headbody=h(sh.encode());assert headbody=='8f1b19cf6893b7129e6d98ced5572633f6ed04a1b2fcd5767d04e136e7cef9c8';assert (P/'source/HEAD'/(owner+'.txt')).read_text()==sh and (P/'source/BASE'/(owner+'.txt')).read_text()==sb
w('source-and-scope-checks.json',{'base':base,'head':head,'BASE_owner_SHA256':h(sb.encode()),'HEAD_owner_SHA256':headbody,'all1003_current_source_map_Git_bindings_exact':True,'both930_canonical_source_map_SHA_bytes_exact':True,'sole_Lean_change':owner,'reverse_exactly_two_target_lines_recovers_entire_BASE_owner':True,'target_header_literal_exact':hc.split(':= by')[0]==bc.split(':= by')[0],'all_remaining_owner_bytes_exact':True,'original_private_header_no_API_import_name_definition_or_math_fill_change':True,'entire_actual_HEAD_equals_preflight_owner_and_native':True,'public12_private196_existing_tool_count_confirmed_by_original_receipt_and_source_reversal':True})
# The request declares96 source captures plus4 helper copies; validate every one against actual Git.
req=J(P/'screen/REQUEST.json');assert req['base']==base and req['Nat_source']==head and len(req['population_common48'])==48;assert 'TCSlib/Complexity/TuringMachine/Build/Convention.lean' in req['population_common48'];assert 'TCSlib/Complexity/TuringMachine/CodeParser.lean' in req['population_common48']
mathlib=R/'.lake/packages/mathlib';rows=[]
for phase,key,ref in [('BASE','BASE',base),('HEAD','NAT',head)]:
 e=req['exports'][key];assert e['source']==ref and e['files']==req['population_common48'] and len(e['sha256'])==50
 for rel,sha in e['sha256'].items():
  source=rel in req['population_common48'];p=P/'source'/phase/(rel+'.txt') if source else P/'screen/request-inputs'/phase/rel;b=p.read_bytes();assert h(b)==sha and len(b)==e['source_provenance'][rel]['bytes'];blob=hashlib.sha1(('blob '+str(len(b))+'\0').encode()+b).hexdigest()
  if rel.startswith('Mathlib/'):
   t=req['Mathlib_files'][rel];assert t['package_commit']==req['Mathlib_package']=='029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e';actual=subprocess.check_output(['git','-C',str(mathlib),'rev-parse',t['package_commit']+':'+rel],env=env).decode().strip();assert blob==t['git_blob']==actual and h(b)==t['sha256'];pin=t['package_commit']
  else:assert blob==trees[ref][rel];pin=ref
  rows.append({'phase':phase,'logical_path':rel,'packet_path':p.relative_to(P).as_posix(),'source_population_member':source,'git_pin':pin,'Git_blob':blob,'bytes':len(b),'SHA256':sha,'all_exact':True})
 assert not any(p.relative_to(P/'source'/phase).as_posix().endswith('Ladner.lean.txt') for p in (P/'source'/phase).rglob('*.lean.txt'))
assert len(rows)==100 and sum(r['source_population_member'] for r in rows)==96
w('all100-screen-request-bindings.json',{'request_SHA256':h((P/'screen/REQUEST.json').read_bytes()),'population_each_side':48,'two_Mathlib_package_sources_each_side':True,'full_root_facade_and_both_foreign_TCS_homes_included':True,'Ladner_absent_no_fake_empty_source':True,'all100_SHA_byte_Git_bindings_exact':True,'files':rows})
# Independent prior whole-MAC8 anchors exist outside this frozen packet and can accompany adoption.
A=R/'campaign/status/2026-11-08-mig1-merge';ar=[]
for name in ['receipt.json','Lean-tree.json','object-hashes.json']:
 p=A/name;b=p.read_bytes();q=O/'independent-MAC8-anchors'/name;q.parent.mkdir(exist_ok=True);q.write_bytes(b);ar.append({'original_repository_path':p.relative_to(R).as_posix(),'peer_capture':q.relative_to(O).as_posix(),'bytes':len(b),'SHA256':h(b)})
objects=J(A/'object-hashes.json');assert objects==J(P/'replay/input-before.json')==J(P/'replay/input-after.json');tree=J(A/'Lean-tree.json');receipt=J(A/'receipt.json')
w('independent-MAC8-anchor-bindings.json',{'all895_input_and_after_objects_exact_independent_anchor':True,'input_owner_object_SHA256':objects['TCSlib/Complexity/TuringMachine/CodeSimulator.olean'],'independent_Lean_tree_type':type(tree).__name__,'independent_Lean_tree_count':len(tree),'receipt':receipt,'files':ar,'not_in_original512_packet':True,'publication_action':'Include these exact3 anchors via root canonical list; raw receipt paths/pins remain original.'})
print(json.dumps({'payloads':512,'payload_bytes':27388925,'current_source_map':1003,'canonical_source_maps_each':930,'screen_request_inputs':100,'independent_MAC8_input_objects':len(objects),'actual_source_two_lines_only':True}))
