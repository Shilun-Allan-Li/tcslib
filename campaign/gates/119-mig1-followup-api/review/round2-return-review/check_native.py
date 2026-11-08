from pathlib import Path
import base64,gzip,hashlib,json,collections
R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');G=R/'campaign/gates/119-mig1-followup-api/review/compiled-comparison';O=Path('/private/tmp/gate119-round2-return-review')
def sha(b):return hashlib.sha256(b).hexdigest()
receipt=json.loads((G/'utf8-archives-verification.json').read_bytes());sets={};results={}
for a in receipt['archives']:
 ep=a['endpoint'];enc=(G/a['utf8_file']).read_bytes();assert len(enc)==a['utf8_bytes'] and sha(enc)==a['utf8_sha256']
 gz=base64.b64decode(b''.join(enc.split()),validate=True);assert len(gz)==a['gzip_bytes'] and sha(gz)==a['gzip_sha256'];assert gz==(G/a['gzip_file']).read_bytes()
 raw=gzip.decompress(gz);assert len(raw)==a['raw_stdout_stderr_bytes'] and sha(raw)==a['raw_stdout_stderr_sha256']
 census=[];ax=[];pub=[]
 for n,ln in enumerate(raw.decode().splitlines(),1):
  if ln.startswith('CENSUS|'):
   x=json.loads(ln[7:]);tx=x.pop('typeExpr');x['typeExpr_sha256']=sha(tx.encode());x['typeExpr_utf8_bytes']=len(tx.encode());x['raw_log']=a['gzip_file'];x['raw_CENSUS_line']=n;census.append(x)
  elif ln.startswith('ALLAX|'):ax.append(json.loads(ln[6:]))
  elif ln.startswith('PUBLICAX|'):pub.append(json.loads(ln[9:]))
  elif ln.startswith(('TARGET|','TARGETAX|')):json.loads(ln.split('|',1)[1])
  elif ln.startswith(('TARGETTYPE|','MISSING_TARGET|','COMPLETE|','  ')):pass
  else:assert not ln.strip(),(ep,n,ln[:100])
 for name,rows in [('census',census),('allaxioms',ax),('publicaxioms',pub)]:
  archived=json.loads((G/f'{name}-{ep}.json').read_bytes());assert archived['count']==len(rows) and archived['rows']==rows,(ep,name)
 cm={x['name']:x for x in census};am={x['name']:x for x in ax};pm={x['name']:x for x in pub};assert len(cm)==len(census) and set(cm)==set(am)
 assert {n for n,v in cm.items() if not v['private']}==set(pm)
 assert all(am[n]==v for n,v in pm.items())
 results[ep]={'raw_bytes':len(raw),'raw_sha256':sha(raw),'all':len(cm),'nonprivate':len(pm),'nonprivate_noninternal':sum(not x['private'] and not x['internal'] for x in census),'private':sum(x['private'] for x in census),'sorry_dependent_all':sum('sorryAx' in x['axioms'] for x in ax),'sorry_dependent_nonprivate':sum('sorryAx' in x['axioms'] for x in pub),'all_saved_census_and_axiom_rows_exact':True}
 sets[ep]=(cm,am)
b,bax=sets['base'];h,hax=sets['head'];added=sorted(h.keys()-b.keys());removed=sorted(b.keys()-h.keys());assert not removed
expected=['Turing.FinTM.incFixedTM_spaceUsed','Turing.FinTM.redirectTM_spaceUsedByTape._simp_1_1','Turing.MultiTapeTM.exists_first_entry_of_fixed','Turing.pairDiagTM_spaceUsed'];assert added==expected
changes=[]
for n in b:
 fields=sorted(k for k in b[n] if k not in ['raw_log','raw_CENSUS_line'] and b[n][k]!=h[n][k])
 if fields:changes.append({'name':n,'fields':fields})
 assert bax[n]['axioms']==hax[n]['axioms']
assert changes==[{'name':'Turing.FinTM.redirectTM_spaceUsedByTape','fields':['owner']}],changes
for n in expected+['Turing.FinTM.redirectTM_spaceUsedByTape']:
 assert set(hax[n]['axioms'])=={'propext','Classical.choice','Quot.sound'}
 assert h[n]['kind']=='theorem' and not h[n]['private'] and not h[n]['simp'] and not h[n]['unfold']
out={'endpoints':results,'added':[{**h[n],'axioms':hax[n]['axioms']} for n in added],'removed':removed,'shared_changes':changes,'shared_axiom_changes':0,'full_type_digests_and_native_rows_reconciled':True}
(O/'native-check.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
