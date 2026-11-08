from pathlib import Path
import gzip,json,hashlib,collections,datetime
P=Path('/private/tmp/mig-post234-compiled-accounting');ctx=json.loads((P/'preparation.json').read_text());rows={};ax={};pub={};apis=[];complete=[]
for line in gzip.open(P/'Base.out.gz','rt'):
 if '|{' in line:
  pre,payload=line.split('|',1);tag=pre.rsplit(' ',1)[-1]
  if tag not in ['CENSUS','ALLAX','PUBLICAX']:continue
  d=json.loads(payload);n=d['name'];dest={'CENSUS':rows,'ALLAX':ax,'PUBLICAX':pub}[tag];assert n not in dest
  if tag=='CENSUS':
   typ=d.pop('typeExpr').encode();d['typeExprBytes']=len(typ);d['typeExprSHA256']=hashlib.sha256(typ).hexdigest()
  dest[n]=d
 elif 'API_PRESENT|'in line:apis.append(line.split('API_PRESENT|',1)[1].strip())
 elif 'COMPLETE|'in line:complete.append(line.strip().split('COMPLETE|',1)[1])
assert set(rows)==set(ax) and set(pub)=={n for n,d in rows.items()if not d['private']}
assert all(pub[n]==ax[n]for n in pub)
assert len(apis)==len(set(apis))==5 and complete==[str(len(rows))+'|primaryOwners=12|contextOwners=1']
std={'propext','Classical.choice','Quot.sound'}
def stats(owners):
 names=[n for n,d in rows.items()if d['owner']in owners];bad={n:ax[n]['axioms']for n in names if not set(ax[n]['axioms'])<=std}
 return {'all':len(names),'private':sum(rows[n]['private']for n in names),'nonprivate':sum(not rows[n]['private']for n in names),'kinds':dict(collections.Counter(rows[n]['kind']for n in names)),'axiom_distribution':dict(collections.Counter(','.join(ax[n]['axioms'])for n in names)),'nonstandard':bad,'all_complete_raw_types_retained':True,'type_utf8_bytes':sum(rows[n]['typeExprBytes']for n in names)}
s={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source':ctx['campaign_base'],'PASS':True,'primary12':stats(ctx['primary_owners']),'context_Finite':stats(ctx['context_owners']),'all_census_equals_ALLAX':True,'PUBLICAX_equals_nonprivate':True,'approved_APIs_all5_present':apis,'HEAD_not_run_or_inferred':True}
for name,obj in [('map-base.json',rows),('allax-base.json',ax),('publicax-base.json',pub),('base-checkpoint.json',s)]: (P/name).write_text(json.dumps(obj,indent=2)+'\n')
print(json.dumps(s,indent=2))
