from pathlib import Path
import json,re,hashlib,collections,datetime
P=Path('/private/tmp/sg1-round3-return-review');G=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4/campaign/gates/106-sg1-dedup')
def sha(b):return hashlib.sha256(b).hexdigest()
def load(p):return json.loads(p.read_text())
checks=[]
for folder,count in [('round3-closure-repairs',36),('round3-extra-repairs',40),('round3-prefix-repair',42),('round3-pair-bound-applied',42),('round3-image-repoint',28)]:
 d=G/'review'/folder;defs=(d/'control-definitions.txt').read_text().splitlines();assert len(defs)*2==count and len(set(defs))==len(defs);want={(n,m)for n in defs for m in ['point','abstract']}
 pos=(d/'Controls-unsealed-v1.out').read_text();neg=(d/'Controls-sealed-v1.out').read_text();ps=re.findall(r'(?m)^CONTROL\|([^|]+)\|(point|abstract)\|PASS\|kernelChecked=(\S+)$',pos);ns=re.findall(r'(?m)^CONTROL\|([^|]+)\|(point|abstract)\|FAIL$',neg);er=re.findall(r'error: RFL_CONTROL\|([^|]+)\|(point|abstract)\|Tactic `rfl` failed',neg)
 assert len(ps)==len(ns)==len(er)==count and{(n,m)for n,m,_ in ps}==set(ns)==set(er)==want and len({name for _,_,name in ps})==count
 for label,out,exitcode,errors in [('unsealed',pos,0,0),('sealed',neg,1,count)]:
  run=load(d/('Controls-'+label+'-v1-run.json'));source=(d/('Controls-'+label+'-v1.lean.txt')).read_bytes();assert run['exit']==exitcode and run['errors']==errors and sha(source)in json.dumps(run)and sha(out.encode())in json.dumps(run)
 src=(d/'Controls-unsealed-v1.lean.txt').read_text();assert 'addDecl (.thmDecl'in src and 'goal.mvarId!.refl'in src and not any(x in src for x in ['withTransparency','unsafe def','set_option debug.skipKernelTC'])
 checks.append({'generation':folder,'definitions':len(defs),'positive_identities':count,'negative_identities':count,'all_exact_goals_and_kernel_names':True,'native_receipts_reviewed_not_rerun':True})
old=G/'evidence/round2/guard-strong-seal';o=(old/'Controls-sealed.out').read_text();assert len(re.findall(r'error: Tactic `rfl` failed',o))==4 and (old/'Controls-unsealed.lean.txt').read_text().count(':= by rfl')==4
replays=[]
for folder,stem,n,sorries in [('current-replay-r3','msg5',329,66),('final-replay-msg6','msg6',26,0),('final-replay-msg7','msg7',2,0)]:
 d=G/'evidence'/folder;r=load(d/'receipt.json');assert r['result']=='PASS'and r['pipeline_exit']==r['failures']==r['error_rows']==r['static_mismatches']==0 and r['modules']==n and r['static_total']==sorries
 raw=(d/('replay-'+stem+'.log')).read_text();rows=re.findall(r'(?m)^(\S+) exit=(\d+) errors=(\d+) sorry=(\d+)$',raw);order=(d/('down-'+stem+'.txt')).read_text().splitlines();assert len(rows)==n and[a[0]for a in rows]==order and all(a[1]=='0'and a[2]=='0'for a in rows)and sum(int(a[3])for a in rows)==sorries
 launches=(d/('replay-'+stem+'-launches.log')).read_text().splitlines();names=[re.search(r'(?:-j4\s+)+(\S+)\.lean(?:\s|$)',l).group(1)for l in launches];assert names==order and len(names)==n
 for e in r['evidence']:
  b=(d/e['path']).read_bytes();assert(len(b),sha(b))==(e['bytes'],e['sha256'])
 static=(d/('replay-'+stem+'-static.txt')).read_text();assert static==f'modules {n}, mismatches 0, static total {sorries}\n'
 replays.append({'generation':stem,'source':r['head'],'modules':n,'successful_rows':n,'effective_j4_launches':n,'static_admissions':sorries,'receipt_hashes_exact':True})
d=G/'review/round3-current-source-screen25-final79';bi=load(d/'base-index.json');hi=load(d/'head-index.json');bc=load(d/'base-candidates.json');hc=load(d/'head-candidates.json');delta=load(d/'pair-delta.json');classed=load(d/'head-delta-classification.json')['rows']
assert(len(bi),len(hi),len(bc),len(hc))==(1956,1947,2013,1995)
key=lambda r:(r['a'],r['b'],r['kind'],r['cross_file'])
bm={key(r):r for r in bc};hm={key(r):r for r in hc};assert len(bm)==len(bc)and len(hm)==len(hc)
new=set(hm)-set(bm);gone=set(bm)-set(hm);changed={k for k in set(bm)&set(hm)if bm[k]!=hm[k]};assert(len(new),len(gone),len(changed))==(2,20,13)
assert{key(r)for r in delta['new']}==new and{key(r)for r in delta['gone']}==gone
assert len(classed)==35 and collections.Counter(r['change']for r in classed)=={'new':2,'gone':20,'changed':13}
assert{key(r['row'])for r in classed if r['change']=='new'}==new and{key(r['row'])for r in classed if r['change']=='gone'}==gone
assert[{k:v for k,v in r.items()if k!='offset'}for r in bi if r['kind']=='term']==[{k:v for k,v in r.items()if k!='offset'}for r in hi if r['kind']=='term']and len([r for r in bi if r['kind']=='term'])==435 and[r for r in bc if r['kind']=='term']==[r for r in hc if r['kind']=='term']and len([r for r in bc if r['kind']=='term'])==259
fam=load(G/'review/round3-final-packet/family-accounting.json');a=set(fam['prior_named_affected_set']);b={r['name']for r in fam['FE_LIVE_1_current_Hardness_members']};assert len(a)==49 and len(b)==5 and not(a&b)and set(fam['named_affected_union'])==a|b and fam['named_affected_union_count']==54 and'clA5_live_prefix'in a
host=load(G/'review/round3-host-accounting-addon/disjoint-accounting.json');c=set(host['old_named_affected_set']);e={r['name']for r in host['accepted_host_affected_members']};assert len(c)==35 and len(e)==14 and not(c&e)and c|e==a
res={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'controls':checks,'original_2definitions_4controls_reconciled':True,'replay_chain':replays,'all357_launches_exact_order_j4':True,'screen_base_head':[1956,1947,2013,1995],'all35_delta_identities_classified':True,'term435_spans_259candidates_identical':True,'reproduced_chars_from_frozen_records':[delta['base']['reproduced_chars'],delta['head']['reproduced_chars']],'screen_not_rerun':True,'named_35_plus14_plus5_disjoint_54':True,'F4_Hardness_member_already_in_union':True,'no_new_debt_or_gate_decision':True}
(P/'receipts-screen-family-check.json').write_text(json.dumps(res,indent=2)+'\n');print(json.dumps(res,indent=2))
