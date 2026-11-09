import hashlib,json,re,subprocess
from pathlib import Path
B=Path('/private/tmp/ab34-gates123125-peer-v2');R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');D=B/'125';Q=D/'sections/campaign/gates/125-word-leaves/review';A=D/'sections/campaign/status/2026-11-08-mig1-merge';headmap=json.loads((Q/'replay/source-before.json').read_text());basemap=json.loads((A/'Lean-tree.json').read_text());sha=lambda x:hashlib.sha256(x).hexdigest()
# Source import graph, read exact already-verified HEAD blobs, no compilation.
paths=sorted(p for p in headmap if p.startswith('TCSlib/') or p=='TCSlib.lean');raw=subprocess.run(['git','-C',str(R),'cat-file','--batch'],input=''.join(headmap[p]['git_blob']+'\n' for p in paths).encode(),capture_output=True,check=True).stdout;off=0;sources={}
for p in paths:
 e=raw.index(b'\n',off);h,kind,n=raw[off:e].split();assert h.decode()==headmap[p]['git_blob'];off=e+1;n=int(n);sources[p]=raw[off:off+n].decode();off+=n+1
assert off==len(raw)
def imports(t):
 i=0;n=len(t);out=[]
 while i<n:
  if t[i].isspace():i+=1;continue
  if t.startswith('/-',i):
   d=1;i+=2
   while d:
    if t.startswith('/-',i):d+=1;i+=2
    elif t.startswith('-/',i):d-=1;i+=2
    else:i+=1
   continue
  if t.startswith('--',i):e=t.find('\n',i);i=n if e<0 else e;continue
  if t.startswith('import ',i):e=t.find('\n',i);e=n if e<0 else e;out+=t[i+7:e].split('--')[0].split();i=e;continue
  break
 return out
mods={p[:-5].replace('/','.'):imports(t) for p,t in sources.items()};reverse={}
for m,imps in mods.items():
 for i in imps:reverse.setdefault(i,set()).add(m)
closure=set();todo=['TCSlib.Complexity.CookLevin.Hardness']
while todo:
 m=todo.pop()
 if m in closure:continue
 closure.add(m);todo.extend(reverse.get(m,()))
closure.discard('TCSlib');down=(Q/'replay/down.txt').read_text().splitlines();assert set(down)=={m.replace('.','/') for m in closure} and len(closure)==26;pos={m.replace('/','.'):i for i,m in enumerate(down)};assert all(pos[i]<pos[m] for m in closure for i in mods[m] if i in closure)
seen=set();dfs=[]
def visit(m):
 if m in seen:return
 seen.add(m)
 for i in sorted(mods[m]):
  if i in closure:visit(i)
 dfs.append(m)
for m in sorted(closure):visit(m)
assert [m.replace('.','/') for m in dfs]==down
# Screen endpoint identities and every source capture bind exactly to requests and Git blobs.
pop=(Q/'screen-population.txt').read_text().splitlines();assert len(pop)==len(set(pop))==33;maps={};stats=[]
for side,rf,rr,rq in [('BASE','screen/BASE/screen-BASE.txt','screen/BASE/RESULT.json','screen/BASE/screen-BASE-request.json'),('HEAD','screen/HEAD.txt','screen/HEAD-RESULT.json','screen/HEAD-request.json')]:
 req=json.loads((Q/rq).read_text());run=json.loads((Q/rr).read_text());raw=(Q/rf).read_bytes();text=raw.decode();assert req['population']==pop and run['exit']==0 and run['bytes']==len(raw) and run['sha256']==sha(raw)
 for p in pop:
  v=(Q/'source'/side/(p+'.txt')).read_bytes();assert sha(v)==req['source_sha256'][p];blob=hashlib.sha1(f'blob {len(v)}\0'.encode()+v).hexdigest();assert blob==(basemap[p] if side=='BASE' else headmap[p]['git_blob'])
 assert sha((D/'sections/campaign/gates/125-word-leaves/reproduction-tools/copy-text-screen-v3.py').read_bytes())==req['tool_sha256']
 m=re.match(r'declarations screened: (\d+); copy pairs \(target reproduces >= half of source\): (\d+); reproduced text: ([\d,]+) chars',text);assert m
 rows=re.findall(r'^\s*(\S+)\s+reproduces\s+(\S+): (\d+)/(\d+) = (\d+)%$',text,re.M);assert len(rows)==int(m[2]);pairmap={(t,s):{'matched_chars':int(a),'source_chars':int(z),'percent':int(pc)} for t,s,a,z,pc in rows};assert len(pairmap)==len(rows);maps[side]=pairmap;stats.append({'phase':side,'declarations_extracted':int(m[1]),'directed_pairs':int(m[2]),'reproduced_chars':int(m[3].replace(',','')),'actual_exit':run['exit'],'all33_capture_blobs_and_request_SHA_exact':True,'tool_SHA256_exact_bundled_code':req['tool_sha256']})
new=maps['HEAD'].keys()-maps['BASE'].keys();gone=maps['BASE'].keys()-maps['HEAD'].keys();delta=json.loads((Q/'screen/pair-delta.json').read_text());disp=json.loads((Q/'screen/pair-dispositions.json').read_text());assert not new and len(gone)==10 and {(r['target'],r['source']) for r in delta['gone']}==gone=={(r['target'],r['source']) for r in disp['all_ten_BASE_only_pairs']}
for r in delta['gone']:assert maps['BASE'][(r['target'],r['source'])]=={k:r[k] for k in ['matched_chars','source_chars','percent']}
assert delta['new']==disp['all_new_pairs']==[]
# Only an existing line-location shift and one size number change in style output.
base=(Q/'qa/BASE-style-lint.txt').read_text();head=(Q/'qa/HEAD-style-lint.txt').read_text();normalized=re.sub(r'Hardness\.lean:\d+:','Hardness.lean:LINE:',base).replace('8686 lines','8668 lines');assert normalized==re.sub(r'Hardness\.lean:\d+:','Hardness.lean:LINE:',head)
cb=(Q/'qa/BASE-campaign-lint.txt').read_text();ch=(Q/'qa/HEAD-campaign-lint.txt').read_text();assert cb.replace('8685 lines','8667 lines')==ch
# Canonical source API locations, not just names.
source=(Q/'source/HEAD/TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean.txt').read_text().splitlines();assert 'polyTimeComputable_tail' in source[142] and 'polyTimeComputable_take1' in source[294]
report={'gate':125,'independent_import_graph_closure_exact26_and_DFS_order':True,'full33_population_BASE_HEAD_blobs_request_SHA_and_tool_exact':True,'raw_screen_stats':stats,'zero_new10_BASE_only_identities_and_all_dispositions_exact':True,'style_19_inherited_findings_after_only_source_line_shift_size_normalization':True,'campaign_raw_only_owner_size8685_to8667_changes':True,'public_closure_source_line143_295_correct':True,'new_Lean_or_screen_execution':False};(D/'GRAPH-SCREEN-LINT-CHECK.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
