from pathlib import Path
import json,collections,re
O=Path('/private/tmp/ab34-fe-live1-final-validation/evidence');M=O/'metadata'
def put(name,data):(M/name).write_text(json.dumps(data,indent=2)+'\n')
a=json.loads((M/'BASE.json').read_text());b=json.loads((M/'HEAD.json').read_text());A={r['name']:r for r in a};B={r['name']:r for r in b};shared=sorted(set(A)&set(B));removed=[A[n] for n in sorted(set(A)-set(B))];added=[B[n] for n in sorted(set(B)-set(A))];changes=[]
keys=['owner','kind','private','internal','levelParams','typeExpr','valuePresent','unsafe','partial','kernelHints','reducibility','simp','unfold','protected','instancePriority','axioms']
for n in shared:
 d={k:{'BASE':A[n][k],'HEAD':B[n][k]} for k in keys if A[n][k]!=B[n][k]}
 if d:changes.append({'name':n,'differences':d,'BASE':A[n],'HEAD':B[n]})
put('REMOVED.json',removed);put('ADDED.json',added);put('CHANGED.json',changes)
# Retain complete actual types and metadata for each side; these files are not hash-only summaries.
for label,rows in [('BASE',a),('HEAD',b)]:
 put(label+'-NONPRIVATE.json',[r for r in rows if not r['private']]);put(label+'-AXIOM-SETS.json',dict(sorted(collections.Counter(tuple(r['axioms']) for r in rows).items())) if False else [{'axioms':list(k),'count':v} for k,v in sorted(collections.Counter(tuple(r['axioms']) for r in rows).items())])
counts=[]
for owner in sorted({r['owner'] for r in a+b}):
 ar=[r for r in a if r['owner']==owner];br=[r for r in b if r['owner']==owner]
 counts.append({'owner':owner,'BASE':{'raw':len(ar),'private':sum(r['private'] for r in ar),'nonprivate':sum(not r['private'] for r in ar)},'HEAD':{'raw':len(br),'private':sum(r['private'] for r in br),'nonprivate':sum(not r['private'] for r in br)}})
targets=[]
for c in json.loads((O/'CODE-CORRESPONDENCE.json').read_text())['rows']:
 for target in c['targets']:
  name=target['name'];aa=[r for r in a if r['name'].split('.')[-1]==name and r['owner']==c['path'][:-5].replace('/','.')];bb=[r for r in b if r['name'].split('.')[-1]==name and r['owner']==c['path'][:-5].replace('/','.')];assert len(aa)==1 and len(bb)==1,(name,len(aa),len(bb));x,y=aa[0],bb[0]
  assert x['levelParams']==y['levelParams'] and x['typeExpr']==y['typeExpr'],name
  targets.append({'target':name,'BASE':x,'HEAD':y,'exact_type_and_universe_params':True,'axioms_exact':x['axioms']==y['axioms']})
put('TARGET11.json',targets)
nonpriv_shared=[n for n in shared if not A[n]['private'] and not B[n]['private']];td=[n for n in nonpriv_shared if A[n]['typeExpr']!=B[n]['typeExpr'] or A[n]['levelParams']!=B[n]['levelParams']];axdiff=[n for n in shared if A[n]['axioms']!=B[n]['axioms']]
summary={'fresh_actual_BASE_HEAD_metadata':True,'owners':5,'counts':counts,'BASE_raw':len(a),'HEAD_raw':len(b),'raw_shared':len(shared),'removed':len(removed),'added':len(added),'changed_shared':len(changes),'shared_nonprivate':len(nonpriv_shared),'nonprivate_exact_type_differences':td,'shared_axiom_differences':axdiff,'target11_exact_types':True,'target11_axioms_equal':all(r['axioms_exact'] for r in targets),'target11_nonstandard_axioms':[{r['target']:r['HEAD']['axioms']} for r in targets if any(x not in ['propext','Quot.sound','Classical.choice'] for x in r['HEAD']['axioms'])],'all_types_stored_as_Expr_and_pretty_text':True,'proof_values_not_rendered':True,'new_unsafe_or_partial':[{k:r[k] for k in ['name','unsafe','partial']} for r in added if r['unsafe'] or r['partial']],'status':'Complete raw deltas retained for classification; no automatic public-name-set equivalence inferred'}
put('SUMMARY.json',summary);print(json.dumps(summary,indent=2));print('REMOVED NAMES',json.dumps([r['name'] for r in removed]));print('ADDED NAMES',json.dumps([r['name'] for r in added]));print('CHANGED SHARED',json.dumps([{'name':r['name'],'keys':list(r['differences'])} for r in changes]))
