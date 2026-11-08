from pathlib import Path
import json,gzip,collections,hashlib,datetime
P=Path('/private/tmp/mig-post234-compiled-accounting');ctx=json.loads((P/'preparation.json').read_text());c=json.loads((P/'map-base.json').read_text());ci={};attrs={};simp=collections.defaultdict(list);marks=[]
for l in gzip.open(P/'Base-ciattrs.out.gz','rt'):
 if l.startswith(('CI|','ATTR|','SIMP_RULE|')):
  tag,n,j=l.split('|',2);r=json.loads(j)
  if tag=='SIMP_RULE':simp[n].append(r)
  else:
   dest=ci if tag=='CI'else attrs;assert n not in dest;dest[n]=r
 elif l.startswith(('CICOMPLETE|','SIMPCOMPLETE')):marks.append(l.strip())
assert set(ci)==set(attrs)==set(c) and marks==[f'CICOMPLETE|constants={len(c)}|simp_environment_unchanged=true','SIMPCOMPLETE']
for n in c:
 assert ci[n]['levelParams']==c[n]['levelParams']and ci[n]['unsafe']==c[n]['unsafe']and ci[n]['partial']==c[n]['partial']
 a=attrs[n];b=c[n];assert a['simp']==b['simp']and a['simp_unfold']==b['unfold']and a['protected']==b['protected']and a['instance_priority']==b['instancePriority']and a['reducibility']==b['reducibility']
 c[n]['structural_CI']=ci[n];c[n]['reflected_attributes']=attrs[n]
base=P/'snapshot-base-before.json';before=json.loads(base.read_text());snap=Path(ctx['base_snapshot']);after={str(q.relative_to(snap)):{'bytes':q.stat().st_size,'sha256':hashlib.sha256(q.read_bytes()).hexdigest()}for q in sorted(snap.rglob('*.olean'))};assert before==after and len(after)==895
(P/'snapshot-base-after-basejobs.json').write_text(json.dumps(after,indent=2)+'\n')
(P/'map-base-complete.json').write_text(json.dumps(c,indent=2)+'\n');(P/'effective-simp-base.json').write_text(json.dumps(dict(simp),indent=2)+'\n')
summary={'checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source':ctx['campaign_base'],'all5760_primary_and_context_CI_rows_exact_main_inventory':len(c)==5760,'primary12_count':sum(r['owner']in ctx['primary_owners']for r in c.values()),'Finite_context_count':sum(r['owner']in ctx['context_owners']for r in c.values()),'CI_and_reflected_attributes_exact_coverage':True,'primary12_effective_simp_rules':sum(len(v)for n,v in simp.items()if c[n]['owner']in ctx['primary_owners']),'Finite_context_effective_simp_rules':sum(len(v)for n,v in simp.items()if c[n]['owner']in ctx['context_owners']),'all895_baseline_objects_unchanged_after_two_jobs':True,'no_theorem_proof_values_rendered':True,'HEAD_not_run':True}
(P/'base-ciattrs-checkpoint.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
