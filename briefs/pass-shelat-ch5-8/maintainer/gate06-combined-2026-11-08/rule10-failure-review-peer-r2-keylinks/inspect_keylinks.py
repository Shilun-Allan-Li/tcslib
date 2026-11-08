"""Own data-only audit of provisional R2 key-link labels; no helper import."""
from pathlib import Path
from collections import Counter
import hashlib,json

W=Path('/Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4')
A=W/'.lake/ps-maintainer/gate06-combined-20261108'
P=A/'rule10-failure-review-prep-r2';H=P/'preparation-history/before-vertical-bar-and-link-guards';F=H/'preflight';OUT=A/'rule10-failure-review-peer-r2-keylinks'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text())
def safe(u):return u['kind'] in {'theorem','lemma','def','abbrev','opaque','axiom','instance','structure','inductive','class','example'} and u.get('canonical_parts') is not None and not u.get('lexical_boundaries_need_review') and not u.get('namespace_context_ambiguous')
def main():
 inputs={n:sha(F/n) for n in ['preflight-manifest.json','prior-witnesses.json','historical-ledger-index.json','all59-source-envelope-indices.json']}
 assert inputs['preflight-manifest.json']=='473aed1877baf120c43d7fa9615505be3f894c2368dfcc0b0591c3ce547b69d0'
 prior=load(F/'prior-witnesses.json');history=load(F/'historical-ledger-index.json')['rows'];idx=load(F/'all59-source-envelope-indices.json')
 existing=[];exact=[]
 for r in prior['historical_roots']:
  for link in r.get('exact_historical_inventory_links',[]):
   row={'file':r['file'],'historical_source_key':r['historical_source_key'],'basis':link.get('basis'),'inventory':link['inventory'],'inventory_line':link['line'],'inventory_key':link['normalized_source_key']}
   (existing if link.get('basis')=='PATH_AND_EXACT_UNIQUE_DECLARED_SPELLING' else exact).append(row)
 potential=[]
 for module,indices in idx.items():
  for u in indices['head']['units']:
   short=u.get('source_name');parts=u.get('canonical_parts')
   if not safe(u) or not short:continue
   unique=sum(q['source_name']==short for q in indices['head']['units'])==1 and sum(q['source_name']==short for q in indices['actual_PRbase']['units'])<=1
   if not unique:continue
   path=module.replace('.','/')+'.lean'
   for row in history:
    if row['file']==path and row['normalized_source_key']==short.removeprefix('_root_.') and row['normalized_source_key']!='.'.join(parts):
     potential.append({'file':path,'source_name':short,'source_canonical_parts':parts,'inventory':row['inventory'],'inventory_line':row['line'],'inventory_key':row['normalized_source_key'],'permitted_label':'SOURCE_SPELLING_CANDIDATE_NOT_CANONICAL_IDENTITY'})
 result={'status':'PROVISIONAL_R2_DATA_ONLY_SEMANTIC_LABEL_REVIEW','input_root':str(F),'source_head':prior['head'],'actual_PRbase':prior['actual_PRbase'],'input_sha256':inputs,'code_sha256':{n:sha(H/(n+'.source.txt')) for n in ['attach_current_failures.py','failure_preflight.py','source_context.py']},'historical_inventory_links_total':len(existing)+len(exact),'historical_unique_spelling_fallback_links':len(existing),'historical_exact_full_source_component_links':len(exact),'historical_spelling_candidates':existing,'historical_exact_component_links':exact,'all59_potential_future_fallback_links':len(potential),'all59_potential_future_spelling_candidates':potential,'original_inventory_rows':dict(Counter(r['inventory'] for r in history)),'rule':'Only leading _root_. normalization plus full source components may be an exact canonical/source-key link. Unique declared spelling within a file is retained only as a separately labelled candidate. No Lean Name or inheritance acceptance inferred.','reviewed_helpers_executed_or_imported':False,'native_executed':False}
 with (OUT/'keylink-observations.json').open('x') as f:json.dump(result,f,indent=2);f.write('\n')
 print(json.dumps({k:result[k] for k in ['status','historical_inventory_links_total','historical_unique_spelling_fallback_links','historical_exact_full_source_component_links','all59_potential_future_fallback_links','original_inventory_rows']},indent=2))
if __name__=='__main__':main()
