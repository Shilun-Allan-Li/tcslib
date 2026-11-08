from pathlib import Path
import json,hashlib,base64,gzip,re,collections,datetime
P=Path('/private/tmp/sg1-round3-return-review');G=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4/campaign/gates/106-sg1-dedup');D=G/'review/round3-final-compiled'
def sha(b):return hashlib.sha256(b).hexdigest()
def load(n):return json.loads((D/n).read_text())
allmaps={};out=[];simps={}
for side,total,private in [('Base',7101,5750),('Head',7063,5712)]:
 m=load('map-'+side+'.json');c=m['census'];assert len(c)==total and sum(r['private']for r in c.values())==private
 parsed={};axs={};pub={};stages=[]
 for suffix in ['census','types','ciattrs']:
  name=side+'-'+suffix+'-v1';raw=gzip.decompress(base64.b64decode((D/(name+'.out.gz.b64')).read_bytes()));run=load(name+'-run.json')
  # Supplied successful receipts remain reviewed executions, never re-executions here.
  rawsha=sha(raw);assert run['exit']==0 and run['errors']==0 and run.get('warnings',0)==0
  assert rawsha in json.dumps(run),(name,'missing output hash')
  stages.append({'name':name,'raw_bytes':len(raw),'raw_sha256':rawsha,'reviewed_successful_native_receipt':True})
  if suffix=='census':
   for l in raw.decode().splitlines():
    if l.startswith('CONSTANT '):
     mm=re.fullmatch(r'CONSTANT (\S+) module=(\S+) kind=(\S+) private=(true|false) internal=(true|false)',l);assert mm
     n,owner,kind,pr,inter=mm.groups();assert n not in parsed;parsed[n]={'owner':owner,'kind':kind,'private':pr=='true','internal':inter=='true'}
   for mm in re.finditer(r'(?m)^(ALLAX|PUBLICAX)\|([^|\n]+)\|(\[[\s\S]*?\])',raw.decode()):
    tag,n,a=mm.groups();a=a[1:-1].strip();v=[]if not a else re.split(r',\s*',a);dest=axs if tag=='ALLAX'else pub;assert n not in dest;dest[n]=v
   assert set(parsed)==set(axs)==set(c)and set(pub)=={n for n,d in parsed.items()if not d['private']}
   for n,r in parsed.items():assert all(c[n][k]==v for k,v in r.items())and c[n]['axioms']==axs[n]
   assert all(pub[n]==axs[n]for n in pub)
  elif suffix=='types':
   ms=list(re.finditer(rb'(?m)^TYPE_REPR\|([^|\n]+)\||^TYPECOMPLETE\|[^\n]*',raw));seen=set();typebytes=0
   for i,mm in enumerate(ms):
    if mm.group(1)is None:continue
    n=mm.group(1).decode();assert n not in seen;seen.add(n);e=ms[i+1].start()if i+1<len(ms)else len(raw);b=raw[mm.end():e].rstrip(b'\n');r=c[n]['type_repr'];assert(len(b),sha(b))==(r['utf8_bytes'],r['sha256']),(side,n,'type')
    typebytes+=len(b)
   assert seen==set(c)
  else:
   cis={};attrs={};sr=collections.defaultdict(list)
   for l in raw.decode().splitlines():
    if l.startswith(('CI|','ATTR|','SIMP_RULE|')):
     tag,n,j=l.split('|',2);r=json.loads(j)
     if tag=='SIMP_RULE':sr[n].append(r)
     else:
      dest=cis if tag=='CI'else attrs;assert n not in dest;dest[n]=r
   assert set(cis)==set(attrs)==set(c)
   for n in c:assert c[n]['ci']==cis[n]and c[n]['attributes']==attrs[n]
   simps[side]=dict(sr)
 out.append({'stage':side,'owned_constants':total,'private':private,'nonprivate':total-private,'type_payload_bytes':typebytes,'all_complete_types_metadata_AX_reparsed':True,'native_streams':stages,'all_simp_rules':sum(map(len,simps[side].values()))})
 allmaps[side]=c
b,h=allmaps['Base'],allmaps['Head'];added=set(h)-set(b);removed=set(b)-set(h);shared=set(b)&set(h);assert len(added)==6 and len(removed)==44 and all(h[n]['private']for n in added)and all(b[n]['private']for n in removed)
fields=['kind','owner','private','internal','ci','attributes','axioms'];changes={k:[n for n in sorted(shared)if b[n][k]!=h[n][k]]for k in fields};typchanges=[n for n in sorted(shared)if b[n]['type_repr']['sha256']!=h[n]['type_repr']['sha256']or b[n]['type_repr']['utf8_bytes']!=h[n]['type_repr']['utf8_bytes']]
assert all(not changes[k]for k in fields if k!='axioms')and len(changes['axioms'])==1 and len(typchanges)==10 and all(h[n]['private']for n in typchanges)
public={n for n,r in b.items()if not r['private']};assert public=={n for n,r in h.items()if not r['private']}and not(public&set(typchanges))and not(public&set(changes['axioms']))
std={'propext','Classical.choice','Quot.sound'};bad_b={n:r['axioms']for n,r in b.items()if not set(r['axioms'])<=std};bad_h={n:r['axioms']for n,r in h.items()if not set(r['axioms'])<=std};assert len(bad_b)==9 and bad_b==bad_h and all(h[n]['owner']=='TCSlib.Complexity.TuringMachine.Build.Primitives'for n in bad_h)
roots=load('all-current-repaired-roots.json');assert roots['root_count']==43 and roots['descendant_count']==93
seen=set();desc=set()
for r in roots['roots']:
 n=r['name'];assert n in h and h[n]['axioms']==r['axioms']and set(r['axioms'])<=std;seen.add(n)
 expected={q for q in h if q.startswith(n+'.')};actual={x['name']for x in r['descendants']};assert expected==actual
 for d in r['descendants']:assert h[d['name']]['axioms']==d['axioms']and set(d['axioms'])<=std
 desc|=actual
assert len(seen)==43 and len(desc)==93 and len(seen|desc)==136 and simps['Base']==simps['Head']and sum(map(len,simps['Base'].values()))==168
result={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source':'79e7c63a6bfa5f002663924f5c7d4e72db705026','comparison_base':'3023dc1408c3d216fc07a7cbba9ae30135b861ed','both_endpoint_streams':out,'all_six_streams_complete_reparse':True,'all1351_nonprivate_records_equal':True,'added6_removed44_all_private':True,'shared_field_changes':{k:len(v)for k,v in changes.items()},'type_changes10_private_generated':typchanges,'owned168_simp_rules_exact':True,'all43roots_plus93descendants_136distinct_standard':True,'inherited9_Primitives_nonstandard_exact':bad_h,'no_new_nonstandard_AXIOMS':True,'no_native_execution_here':True,'proof_value_equality_not_claimed':True}
(P/'compiled-evidence-check.json').write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n');print(json.dumps({k:v for k,v in result.items()if k not in ['type_changes10_private_generated','inherited9_Primitives_nonstandard_exact']},indent=2))
