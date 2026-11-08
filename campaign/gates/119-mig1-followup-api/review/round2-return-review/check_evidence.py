from pathlib import Path
import json,re,hashlib,subprocess,collections,base64,gzip,tarfile,io,difflib
R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');GP='campaign/gates/119-mig1-followup-api';G=R/GP;O=Path('/private/tmp/gate119-round2-return-review')
S='f1ca767a10551960faf36ad9c8ff17bea3a2d88c';B='3023dc1408c3d216fc07a7cbba9ae30135b861ed';C='bf02e7ccd9d0b76d38d4da8d03d31984945fe5b4'
def sha(b):return hashlib.sha256(b).hexdigest()
def git(*a):return subprocess.check_output(['git','-C',str(R),*a])
def blob(p,f):return git('show',p+':'+f)
def j(p):return json.loads(p.read_bytes())
def run(d,stem,src=None):
 rc=j(d/(stem+'-run.json'));out=(d/(stem+'.out')).read_bytes();src=(d/(src or stem+'.lean.txt')).read_bytes()
 assert rc['input_sha256']==sha(src) and rc['output_sha256']==sha(out),(d,stem)
 errs=list(re.finditer(r'^.*?:([0-9]+):([0-9]+): error: (.*)',out.decode(),re.M));assert len(errs)==rc['errors']
 return rc,out.decode(),src.decode(),errs
controls=[]
d=G/'review/first-entry';pos=run(d,'Controls-unsealed');neg=run(d,'Controls-sealed')
assert pos[0]['exit']==0 and pos[0]['errors']==0 and neg[0]['exit']==1 and neg[0]['errors']==8
starts=[i for i,s in enumerate(neg[2].splitlines(),1) if s.startswith('example')];assert len(starts)==8
identities=[]
for idx,start in enumerate(starts):
 end=starts[idx+1]-1 if idx+1<len(starts) else len(neg[2].splitlines());es=[e for e in neg[3] if start<=int(e[1])<=end]
 assert len(es)==1 and 'Tactic `rfl` failed' in es[0][3];identities.append({'ordinal':idx+1,'source_lines':[start,end],'error_line':int(es[0][1])})
assert pos[2]==neg[2].replace('attribute [local irreducible] Turing.MultiTapeTM.step Turing.MultiTapeTM.runFrom\n','')
controls.append({'group':'first-entry','identities':8,'positive_exit':0,'negative_exit':1,'exact_error_intervals':identities})
for group,pn,nn,n in [('pair-diag','Controls-unsealed-v1','Controls-sealed-v1',8),('inc-redirect','Controls-native','Controls-sealed',52)]:
 d=G/'review'/group;pos=run(d,pn);neg=run(d,nn)
 assert pos[0]['exit']==0 and pos[0]['errors']==0 and neg[0]['exit']==1 and neg[0]['errors']==n
 def markers(s,status):return [(a,b) for a,b,c in re.findall(r'^CONTROL\|([^|]+)\|([^|]+)\|([^|\n]+)(?:\|[^\n]*)?$',s,re.M) if c==status]
 pids=markers(pos[1],'PASS');nids=markers(neg[1],'FAIL');dids=re.findall(r': error: RFL_CONTROL\|([^|]+)\|([^|]+)\|',neg[1]);assert len(set(pids))==n and len(pids)==n and pids==nids==dids,(group,pids[:2],nids[:2],dids[:2])
 clean=lambda s:'\n'.join(x for x in s.splitlines() if not x.startswith('attribute [local irreducible]'))
 same=clean(pos[2])==clean(neg[2]);assert same,(group,'guard-only source difference')
 controls.append({'group':group,'identities':n,'positive_exit':0,'negative_exit':1,'exact_positive_negative_and_error_identities':pids,'guard_only_source_difference':same})
# Five-owner preflight authenticates every source and output at the frozen head.
pf=j(G/'evidence/preflight/receipt.json');preflight=[]
for r in pf['runs']:
 name=Path(r['source']).stem;source=(G/'evidence/preflight'/f'{name}.lean.txt').read_bytes();out=(G/'evidence/preflight'/f'{name}.out').read_bytes()
 assert source==blob(S,r['source']) and sha(source)==r['source_sha256'] and sha(out)==r['output_sha256'];assert r['exit']==r['errors']==0 and ': error:' not in out.decode()
 preflight.append({'source':r['source'],'source_sha256':sha(source),'log_sha256':sha(out),'exit':0})
assert len(preflight)==5
# Raw replay, order, every effective launch and final static count.
d=G/'evidence/replay-mfup2';rc=j(d/'receipt.json')
for i in rc['evidence']:
 b=(d/i['path']).read_bytes();assert len(b)==i['bytes'] and sha(b)==i['sha256']
order=(d/'down-mfup2.txt').read_text().splitlines();assert len(order)==len(set(order))==401 and 'TCSlib' not in order
log=(d/'replay-mfup2.log').read_text();rows=re.findall(r'^(\S+) exit=(\d+) errors=(\d+) sorry=(\d+)$',log,re.M);assert [r[0] for r in rows]==order and all(r[1:3]==('0','0') for r in rows) and sum(int(r[3]) for r in rows)==77
assert log.splitlines()[-1]=='# modules=401 failed=0';assert len(log.splitlines())==403
launches=[]
for ln in (d/'replay-mfup2-launches.log').read_text().splitlines():
 m=re.fullmatch(r'pid=([0-9]+) -j4 (\S+)\.lean -o (\S+)\.olean',ln);assert m;assert m[3].endswith('/oleans-mfup2/'+m[2]);launches.append(m[2])
assert launches==order
assert (d/'replay-mfup2-static.txt').read_text()=='modules 401, mismatches 0, static total 77\n'
helper=blob(S,'scripts/lean_check_tree.sh');assert helper==(d/'actual-branch-lean_check_tree.sh').read_bytes();assert '-j4' not in helper.decode()
assert '-j4' in (d/'lean-j4-shim.sh').read_text() and '4.25' in (d/'run.sh').read_text()
partial=list((G/'evidence/replay/partial-mfup1').glob('*.log'));assert len(partial)==1
prows=re.findall(r'^(\S+) exit=(\d+) errors=(\d+) sorry=(\d+)$',partial[0].read_text(),re.M);assert len(prows)==272 and all(r[1:3]==('0','0') for r in prows);assert '# modules=401 failed=0' not in partial[0].read_text()
# Screen rows and full normalized source denominators; decode archives without extraction.
d=G/'review/source-lint-screen';pop=(d/'population.txt').read_text().splitlines();assert len(pop)==16
screens={};maps={}
for ep,pin,expected in [('base',B,(2005,2222,738885)),('head',S,(2006,2228,740747))]:
 for p in pop:assert (d/'inputs'/ep/(p+'.txt')).read_bytes()==blob(pin,p)
 raw=(d/(ep+'.out')).read_text();ix=j(d/(ep+'-index.json'));cands=j(d/(ep+'-candidates.json'));im={i['label']:i for i in ix}
 assert len(im)==len(ix)
 for i in ix:assert len(i['normalized_body'])==i['body_chars']
 parsed=[]
 for ln in raw.splitlines()[1:]:
  m=re.fullmatch(r'\s+(\S+)  reproduces  (\S+): (\d+)/(\d+) = (\d+)%',ln);assert m,ln
  a,b,shared,den,pct=m.groups();assert im[b]['body_chars']==int(den)
  parsed.append((a,b,int(shared),int(den),int(pct)))
 assert parsed==[(i['a'],i['b'],i['shared'],i['denominator'],i['printed_percent']) for i in cands]
 assert (len(ix),len(parsed),sum(i[2] for i in parsed))==expected
 tar=base64.b64decode(b''.join((d/(ep+'.tar.base64.txt')).read_bytes().split()),validate=True)
 with tarfile.open(fileobj=io.BytesIO(tar),mode='r:*') as tf:
  files=[m for m in tf.getmembers() if m.isfile()];assert len(files)==16
  for m in files:
   p=m.name;assert p in pop,p;assert tf.extractfile(m).read()==blob(pin,p)
 maps[ep]={(i[0],i[1]):i[2:] for i in parsed}
 screens[ep]={'eligible':len(ix),'candidates':len(parsed),'shared_characters':sum(i[2] for i in parsed),'source_captures_exact':16,'archive_members_exact':16,'kind_cross_file':dict(collections.Counter(i['kind']+'/'+str(i['cross_file']) for i in cands))}
added=sorted(maps['head'].keys()-maps['base'].keys());assert len(added)==6 and not maps['base'].keys()-maps['head'].keys();assert all(maps['base'][k]==maps['head'][k] for k in maps['base'])
assert len({x for k in added for x in k})==5
lints=j(d/'lint-results.json');assert not lints['style_normalized_new'] and not lints['style_normalized_gone']
def normalized_lint(text):
 text=re.sub(r':([0-9]+):',':<LINE>:',text)
 text=re.sub(r'\b[0-9]+ lines','<LINES> lines',text)
 return [ln for ln in text.splitlines() if not re.match(r'^INFO .*lines; [0-9]+ public / [0-9]+ private declarations$',ln)]
for name in ['style','campaign']:
 assert normalized_lint((d/(name+'-base.out')).read_text())==normalized_lint((d/(name+'-head.out')).read_text())
for ep in ['base','head']:
 assert len(lints['sides'][ep]['style']['findings'])==77 and lints['sides'][ep]['style']['exit']==1
 assert collections.Counter(re.findall(r'^(FAIL|WARN|INFO) ',(d/('campaign-'+ep+'.out')).read_text(),re.M))=={'WARN':7,'INFO':7}
for k in ['campaign_normalized_new','campaign_normalized_gone']:
 assert len(lints[k])==5 and all(x.startswith('INFO|') and 'public /' in x for x in lints[k])
# Full strict population-map roundtrips plus all ref/commit/tree/blob/path joins.
rr=j(G/'evidence/reuse-population-utf8/receipt.json');reuse=[]
for a in rr['maps']:
 enc=(R/a['encoded_section']).read_bytes();assert len(enc)==a['encoded_utf8_bytes'] and sha(enc)==a['encoded_utf8_sha256'];gz=base64.b64decode(b''.join(enc.split()),validate=True);assert len(gz)==a['gzip_bytes'] and sha(gz)==a['gzip_sha256'];raw=gzip.decompress(gz);assert len(raw)==a['raw_bytes'] and sha(raw)==a['raw_sha256'];assert raw==blob(C,a['original_path']);tm=json.loads(raw);assert len(tm)==a['complete_tree_entries'];reuse.append({'trees':len(tm),'encoded_sha256':sha(enc),'gzip_sha256':sha(gz),'raw_sha256':sha(raw),'original_Git_blob_exact':True})
 if '/all-local-expanded/' in a['original_path']:expanded=tm
ed=G/'review/reuse-search/all-local-expanded';refs=j(ed/'refs.json');commits=j(ed/'commits.json');blobs=j(ed/'blob-population.json')
assert len(refs)==531 and len({i['ref'] for i in refs})==531;assert {i['commit'] for i in refs}=={i['commit'] for i in commits};assert len(commits)==328 and len(expanded)==277
assert {i['TCSlib_tree'] for i in commits if i['TCSlib_tree'] is not None}==set(expanded)
for i in commits:assert i['lean_sources']==(len(expanded[i['TCSlib_tree']]) if i['TCSlib_tree'] is not None else 0)
bmap=collections.defaultdict(set)
for tree,rows in expanded.items():
 assert len({i['path'] for i in rows})==len(rows)
 for i in rows:bmap[i['blob']].add(i['path'])
assert len(bmap)==2511 and len(set().union(*bmap.values()))==1167 and {i['blob'] for i in blobs}==set(bmap)
for i in blobs:assert set(i['paths'])==bmap[i['blob']]
out={'controls':controls,'controls_total':68,'preflight':preflight,'mfup2':{'rows':401,'effective_j4_launches':401,'static_mismatches':0,'admissions':77,'helper_exact_at_source':True,'snapshot_contents_NOT_inspected':True},'partial_mfup1':{'completed_passing_rows':272,'final_pass_absent':True},'screens':screens,'six_new_edges':[{'a':k[0],'b':k[1],'shared_denominator_percent':maps['head'][k]} for k in added],'lint_diagnostic_kinds_unchanged_after_line_size_normalization':True,'expected_changed_public_count_INFO_rows':5,'reuse_archives':reuse,'expanded_joins':{'refs':531,'commits':328,'trees':277,'blobs':2511,'paths':1167}}
(O/'evidence-check.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k not in ['controls','six_new_edges']},indent=2))
