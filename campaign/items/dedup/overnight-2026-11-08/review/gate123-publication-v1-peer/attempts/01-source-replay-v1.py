import hashlib,json,re,subprocess
from pathlib import Path
B=Path('/private/tmp/ab34-gate123-publication-peer');R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');Q=B/'records-inputs/campaign/gates/123-ch7-run/review';P=json.loads((B/'inputs/publication.json').read_text());BASE='9b5dcf46408db681bcbc721930ef2203fa6bc47d';HEAD=P['source'];OWNER='TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean'
def git(*args): return subprocess.run(['git','-C',str(R),*args],capture_output=True,check=True).stdout
def write(name,value): (B/name).write_text(json.dumps(value,indent=2,ensure_ascii=False)+'\n')
def sha(raw):return hashlib.sha256(raw).hexdigest()
def tree(rev):
 d={}
 for line in git('ls-tree','-r','-z',rev).split(b'\0'):
  if not line:continue
  meta,p=line.split(b'\t',1);p=p.decode()
  if p.endswith('.lean'):d[p]=meta.decode().split()[2]
 return d
sources={}
for rev in [BASE,HEAD]:
 ts=tree(rev);names=sorted(ts);request=''.join(rev+':'+p+'\n' for p in names).encode();raw=subprocess.run(['git','-C',str(R),'cat-file','--batch'],input=request,capture_output=True,check=True).stdout
 offset=0;data={}
 for p in names:
  end=raw.index(b'\n',offset);h,kind,n=raw[offset:end].split();assert kind==b'blob' and h.decode()==ts[p];n=int(n);offset=end+1;v=raw[offset:offset+n];offset+=n;assert raw[offset:offset+1]==b'\n';offset+=1;data[p]=v
 assert offset==len(raw);sources[rev]=data
assert len(sources[BASE])==len(sources[HEAD])==1003
before=json.loads((Q/'replay/source-before.json').read_text());actual_source={p:{'git_blob':tree(HEAD)[p],'sha256':sha(raw),'bytes':len(raw)} for p,raw in sources[HEAD].items()};assert actual_source==before
adopt=json.loads((B/'additional-inputs/campaign/status/2026-11-08-mig1-merge/Lean-tree.json').read_text());assert adopt==tree(BASE)
changed=[p for p in sources[HEAD] if sources[BASE].get(p)!=sources[HEAD][p]];assert changed==[OWNER]
assert git('diff','--name-only',BASE,P['records'],'--','*.lean')==b''
# Independent top-level declaration and balanced assignment reader, sufficient for the captured owner.
pat=re.compile(r'(?m)^((?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma|def|abbrev|opaque|axiom|structure|inductive))\s+([\w.\'\u2080-\u2089]+)')
def assignment(t,a,z):
 depth=0;block=0;string=False;i=a
 while i<z:
  if block:
   if t.startswith('/-',i):block+=1;i+=2;continue
   if t.startswith('-/',i):block-=1;i+=2;continue
   i+=1;continue
  if string:
   if t[i]=='\\':i+=2;continue
   if t[i]=='"':string=False
   i+=1;continue
  if t.startswith('/-',i):block=1;i+=2;continue
  if t.startswith('--',i):j=t.find('\n',i);i=z if j<0 else j;continue
  if t[i]=='"':string=True;i+=1;continue
  if t[i] in '([{':depth+=1
  elif t[i] in ')]}':depth-=1
  elif t.startswith(':=',i) and depth==0:return i
  i+=1
 raise AssertionError('no assignment '+t[a:a+100])
def declarations(t):
 ms=list(pat.finditer(t));out={}
 for i,m in enumerate(ms):
  z=ms[i+1].start() if i+1<len(ms) else len(t);a=assignment(t,m.start(),z)
  out[m.group(2)]={'kind':m.group(1),'start':m.start(),'assignment':a,'end':z,'header':t[m.start():a],'body_suffix':t[a:z],'full':t[m.start():z]}
 return out
bt=sources[BASE][OWNER].decode();ht=sources[HEAD][OWNER].decode();bd=declarations(bt);hd=declarations(ht);assert bd.keys()==hd.keys() and len(bd)==18
s=json.loads((Q/'inputs/ch7-full-five-scopes-v2/SOURCE.json').read_text());roots=s['roots'];sn=[x.split('.')[-1] for x in roots];assert all(bd[n]['kind']==hd[n]['kind']=='theorem' and bd[n]['header']==hd[n]['header'] for n in sn)
actual_changed=[n for n in bd if bd[n]['full']!=hd[n]['full']];assert actual_changed==sn
masked=ht
for n in sorted(sn,key=lambda n:hd[n]['assignment'],reverse=True):masked=masked[:hd[n]['assignment']]+bd[n]['body_suffix']+masked[hd[n]['end']:]
assert masked==bt
assert [l for l in bt.splitlines() if l.startswith('import ')]==[l for l in ht.splitlines() if l.startswith('import ')]
assert [l for l in bt.splitlines() if re.match(r'\s*(?:attribute|@\[)',l)]==[l for l in ht.splitlines() if re.match(r'\s*(?:attribute|@\[)',l)]
assert bd['runFrom_one']['full']==hd['runFrom_one']['full']
for name,chunk in s['complete_literal_chunks'].items():assert ht.count(chunk)==1
# Literal scopes/imports/settings must match the owner, allowing Lean instrumentation only.
native=(Q/'inputs/ch7-full-five-scopes-v2/ScopeNative.lean.txt').read_text();sealed=(Q/'inputs/ch7-full-five-scopes-v2/ScopeSealed.lean.txt').read_text()
for name,chunk in s['complete_literal_chunks'].items():assert native.count(chunk)==sealed.count(chunk)==1
for l in [l for l in ht.splitlines() if l.startswith('import ') or l.startswith('set_option ') or l.startswith('namespace ') or l.startswith('variable ') or l=='open MultiTapeTM']: assert l in native and l in sealed
write('SOURCE-CHECK.json',{'BASE':BASE,'HEAD':HEAD,'records':P['records'],'all1003_replay_source_entries_exact_HEAD':True,'MAC8_adoption_1003_blobmap_exact_BASE':True,'records_since_MAC8_has_no_Lean_delta':True,'changed_Lean_files':changed,'owner_declarations':18,'changed_public_bodies_exact5':sn,'all5_balanced_literal_headers_exact':True,'outside5_body_ranges_exact_recovery':True,'all_other_decl_chunks_exact':True,'imports_and_attribute_source_lines_exact':True,'definitions_and_public_Bool_runFrom_one_exact':True,'all5_native_and_sealed_literal_chunks_exact_HEAD':True,'original_import_settings_namespace_variables_present':True,'owner_BASE_sha256':sha(bt.encode()),'owner_HEAD_sha256':sha(ht.encode())})
# Header import graph independently parsed; no elaboration.
def imports(raw):
 t=raw.decode();i=0;n=len(t);out=[]
 while i<n:
  if t[i].isspace():i+=1;continue
  if t.startswith('/-',i):
   d=1;i+=2
   while d:
    if t.startswith('/-',i):d+=1;i+=2
    elif t.startswith('-/',i):d-=1;i+=2
    else:i+=1
   continue
  if t.startswith('--',i):j=t.find('\n',i);i=n if j<0 else j;continue
  if t.startswith('import ',i):j=t.find('\n',i);j=n if j<0 else j;out+=t[i+7:j].split('--')[0].split();i=j;continue
  break
 return out
mods={p[:-5].replace('/','.'):imports(raw) for p,raw in sources[HEAD].items() if p.startswith('TCSlib/') or p=='TCSlib.lean'};rev={}
for m,imps in mods.items():
 for d in imps:rev.setdefault(d,set()).add(m)
closure=set();pending=[OWNER[:-5].replace('/','.')]
while pending:
 m=pending.pop()
 if m in closure:continue
 closure.add(m);pending.extend(rev.get(m,()))
closure.discard('TCSlib');indegree={m:sum(x in closure for x in mods[m]) for m in closure};ready=sorted(m for m in closure if indegree[m]==0);order=[]
while ready:
 m=ready.pop(0);order.append(m)
 for x in sorted(rev.get(m,())):
  if x in indegree:
   indegree[x]-=1
   if indegree[x]==0:ready.append(x);ready.sort()
assert len(order)==len(closure)==80
actual_order=(Q/'replay/down.txt').read_text().splitlines();assert [m.replace('.','/') for m in order]==actual_order
index=json.loads((Q/'replay/compiled-source-index.json').read_text());assert len(index)==80
for row in index:
 raw=(Q/row['capture']).read_bytes();assert raw==sources[HEAD][row['path']] and sha(raw)==row['sha256'] and row['git_blob']==before[row['path']]['git_blob']
assert {x['path'][:-5] for x in index}==set(actual_order)
rows=json.loads((Q/'replay/module-results.json').read_text());assert [x['module'] for x in rows]==actual_order and all(x['pass'] and x['exit']==x['errors']==0 and x['fresh_output'] for x in rows)
for row in rows:assert sha((Q/'replay/logs'/(row['module']+'.log')).read_bytes())==row['log_sha256']
assert sum(x['sorry'] for x in rows)==31
ib=json.loads((Q/'replay/input-before.json').read_text());ia=json.loads((Q/'replay/input-after.json').read_text());ob=json.loads((Q/'replay/output.json').read_text());anchor=json.loads((B/'additional-inputs/campaign/status/2026-11-08-mig1-merge/object-hashes.json').read_text());assert ib==ia==anchor and len(ib)==len(ob)==895 and ib.keys()==ob.keys()
assert [p for p in ob if ob[p]!=ib[p]]==[OWNER[:-5]+'.olean']
write('REPLAY-CHECK.json',{'all1003_source_entries_exact':True,'independent_graph_closure_count':len(closure),'exact_topological_replay_order':True,'full80_compiled_sources_exact_Git_HEAD_and_source_map':True,'all80_module_rows_and_log_hashes_pass':True,'sum_actual_declaration_sorry_warnings':31,'static_receipt':(Q/'replay/static.txt').read_text().strip(),'actual_input895_exact_published_MAC8_adoption':True,'input_after_unchanged':True,'output895_same_keys':True,'changed_objects':[p for p in ob if ob[p]!=ib[p]],'MAC8_anchor_checked_outside_bundle':True,'module_order':actual_order})
print('SOURCE and REPLAY checks PASS: exact5 public body ranges,1003 source maps,80 closure/logs,895 published MAC8 input objects; no Lean executed')
