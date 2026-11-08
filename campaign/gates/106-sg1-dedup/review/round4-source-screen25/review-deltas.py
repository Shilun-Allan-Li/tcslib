from pathlib import Path
import collections,datetime,hashlib,json,subprocess,time
OUT=Path(__file__).resolve().parent
ROOT=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4')
OLD=ROOT/'campaign/gates/106-sg1-dedup/review/round3-current-source-screen25-final79'
C=json.loads((OUT/'capture.json').read_text())
sha=lambda b:hashlib.sha256(b).hexdigest()
now=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
def read(p):return json.loads(p.read_text())
def save(n,x):(OUT/n).write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
def command(name,cmd):
 tick=time.time();start=now();q=subprocess.run(cmd,cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
 (OUT/(name+'.out')).write_bytes(q.stdout);(OUT/(name+'.stderr.out')).write_bytes(q.stderr)
 save(name+'-run.json',dict(command=cmd,start_utc=start,end_utc=now(),seconds=time.time()-tick,exit=q.returncode,stdout_sha256=sha(q.stdout),stderr_sha256=sha(q.stderr)))
 assert q.returncode==0,(name,q.returncode,q.stderr.decode())
 return q.stdout.decode()
for side in ['base','head']:
 r=read(OUT/(side+'-run.json'));assert r['exit']==0 and r['fresh_execution'] and r['full_population']==25 and r['source_commit']==C[side]
 assert sha((OUT/(side+'.out')).read_bytes())==r['output_sha256']
command('analyze-run',['python3','-I',str(OUT/'analyze-screens.py')])
for name,head,base in [('canonical-pairdiff-primary',OUT/'head.out',OUT/'base.out'),('canonical-pairdiff-previous79',OUT/'head.out',OLD/'head.out')]:
 command(name,['python3','-I',str(ROOT/'devtools/seyoon/pairdiff.py'),str(head),str(base)])
d=read(OUT/'pair-delta.json');old_d=read(OLD/'pair-delta.json');classified_old=read(OLD/'head-delta-classification.json')['rows']
indexes={label:{r['label']:r for r in read(folder/(side+'-index.json'))} for label,folder,side in [('old_base',OLD,'base'),('old_head',OLD,'head'),('base',OUT,'base'),('head',OUT,'head')]}
rows={label:read(folder/(side+'-candidates.json')) for label,folder,side in [('old_base',OLD,'base'),('old_head',OLD,'head'),('base',OUT,'base'),('head',OUT,'head')]}
key=lambda r:(r['a'],r['b'])
maps={s:{key(r):r for r in v} for s,v in rows.items()}
# All eligible common normalized bodies are identical across the upstream generation.
index_deltas={}
for old,cur in [('old_base','base'),('old_head','head')]:
 a,b=indexes[old],indexes[cur];changed=[k for k in sorted(a.keys()&b.keys()) if a[k]['normalized_body']!=b[k]['normalized_body']]
 index_deltas[old+'-to-'+cur]=dict(added=sorted(b.keys()-a.keys()),removed=sorted(a.keys()-b.keys()),common_normalized_bodies_changed=changed)
 assert not changed
api_labels=set(index_deltas['old_base-to-base']['added']+index_deltas['old_base-to-base']['removed'])
f4_labels={'SAT.lean::sat_live_prefix','Hardness.lean::clA5_live_prefix'}
assert api_labels=={'Finite.lean::exists_first_entry_of_fixed','Catalog.lean::redirectTM_spaceUsedByTape'}
assert set(index_deltas['old_head-to-head']['added']+index_deltas['old_head-to-head']['removed'])==api_labels|f4_labels
save('eligible-body-progression.json',dict(index_deltas=index_deltas,method='Unmodified v3 parser-only index; compare complete normalized bodies, never declaration offsets as source identity. Eligible membership is a threshold measurement, not an authored/compiler declaration census.'))
def delta(a,b):
 return dict(new=[b[k] for k in sorted(b.keys()-a.keys())],gone=[a[k] for k in sorted(a.keys()-b.keys())],changed=[dict(old=a[k],current=b[k]) for k in sorted(a.keys()&b.keys()) if a[k]!=b[k]])
historical=delta(maps['old_head'],maps['head']);partition=[]
for change,rs in historical.items():
 for x in rs:
  r=x['current'] if change=='changed' else x;ends={r['a'],r['b']};k=key(r)
  family='F4' if ends&f4_labels else 'upstream API' if ends&api_labels else None
  assert family,(change,r)
  if family=='F4':
   assert change=='gone'
   assessment='Exact old live-prefix implementations now cite public runFrom_state_ne_none_of_le. The current forwarding bodies are below v3 eligibility, so these directed edges disappear. Both source declarations and complete headers survive. Four of the ten incident BASE rows also meet the older Catalog.f2_loop_live_prefix outside the five PR files; that current-campaign candidate remains under its distinct watch/context. No global kind retirement, count of deleted declarations, or general debt approval.'
  else:
   assert change=='new' and k in {(r['a'],r['b']) for r in read(OUT/'upstream-BASE-pair-delta.json')['new']}
   assessment='Same upstream-only fixed-LIVE-stop API edge is already present in fresh BASE. Four preserved old private proofs are exact whole-configuration singleton/predicate FE-LIVE-1 instances, subject to the existing bounded user ruling/schedule. This is not an SG1 R4 proof addition.'
  partition.append(dict(change=change,row=x,family=family,assessment=assessment))
save('previous79-to-current078-partition.json',dict(old_head=C['previous_head'],head=C['head'],raw_delta=historical,classified_rows=partition,scope='Every raw difference between historical final79 and current078, same fixed25; upstream API versus F4 separated by exact body progression.'))
# Carry old dispositions only after exact raw row/measurement equivalence.
def old_match(change,x):
 for o in classified_old:
  if o['change']!=change:continue
  if change=='changed':
   if o['row']['base']==x['base'] and o['row']['head']==x['head']:return o
  elif o['row']==x:return o
 return None
primary=[]
for change,rs in [('new',d['new']),('gone',d['gone']),('changed',d['changed_measurements'])]:
 for x in rs:
  o=old_match(change,x)
  if o:
   primary.append(dict(change=change,row=x,group=o['group'],assessment=o['assessment'],source='Exact raw row/base-head measurement equality to historical final79 classification; retained source chunks independently checked.'))
  else:
   r=x['head'] if change=='changed' else x
   assert change=='gone' and {r['a'],r['b']}&f4_labels,(change,x)
   primary.append(dict(change=change,row=x,group='F4: public backward-liveness theorem replaces private proof',assessment='The old152-character Bool-specialized reconstruction now directly cites MultiTapeTM.runFrom_state_ne_none_of_le. Its complete private header/name remains; canonical original156-character proof and old Catalog.f2_loop_live_prefix context remain. The latter is outside the five PR files and grants no new debt permission. This directed candidate removal is implementation reuse, not a deleted declaration or fresh debt acknowledgment.',source='Actual current BASE/HEAD raw outputs and F4 complete-chunk lineage.'))
assert sum(x['source'].startswith('Exact raw') for x in primary)==len(classified_old)
save('head-delta-classification.json',dict(scope='Every current BASE/HEAD raw directed delta and changed retained measurement; source-identical previous35 dispositions carried only after exact measurement checks; F4 additions reviewed separately.',rows=primary,counts=dict(collections.Counter(x['group'] for x in primary))))
# Preserve one record per retained current row, including candidates with no new semantic disposition.
api_keys={key(r) for r in read(OUT/'upstream-BASE-pair-delta.json')['new']}
primary_present={key(x['row']['head'] if x['change']=='changed' else x['row']):x for x in primary if x['change']!='gone'}
allrows=[]
for r in rows['head']:
 k=key(r)
 if k in primary_present:
  x=primary_present[k];status='Current PR delta independently dispositioned';assessment=x['assessment'];group=x['group']
 elif k in api_keys:
  status='Upstream-only existing FE-LIVE-1 candidate';group='Whole-configuration fixed LIVE-stop first entry';assessment='Exact existing six-row upstream context, unchanged between current BASE/HEAD; see explicit four-site premise mapping and existing ruling. No new acknowledgment.'
 else:
  assert k in maps['old_head'] and maps['old_head'][k]==r,(k,'not historical identical')
  for label in k:assert indexes['head'][label]['normalized_body']==indexes['old_head'][label]['normalized_body']
  status='Historical identical retained raw candidate';group=r['kind']+('/cross-file' if r['cross_file'] else '/in-file');assessment='Both normalized endpoint bodies and the entire directed measurement equal historical final79. This retains the candidate and its prior separately scoped records; it does not accept debt, infer equivalence, clear a major, or establish global absence.'
 allrows.append(dict(row=r,relative_to_current_BASE='new' if k not in maps['base'] else 'changed retained' if maps['base'][k]!=r else 'unchanged retained',status=status,group=group,assessment=assessment))
assert len(allrows)==d['head']['candidates']
save('all-HEAD-candidate-classification.json',dict(scope='All current HEAD raw directed candidates, uncapped. Historical-identical status is a provenance measurement and deliberately grants no blanket debt acceptance.',rows=allrows,counts=dict(collections.Counter(x['status'] for x in allrows))))
# Every file and ordered file-pair bucket, including weighted characters, is retained without top-N caps.
weights={};matrix={}
for side in ['base','head']:
 files=collections.defaultdict(lambda:dict(incident_directed_rows=0,shared_chars=0,outgoing_rows=0,incoming_rows=0))
 for path in C['population']:files[path]
 pairs=collections.defaultdict(lambda:dict(rows=0,shared_chars=0))
 for r in rows[side]:
  a=indexes[side][r['a']]['path'];b=indexes[side][r['b']]['path']
  for f in set([a,b]):files[f]['incident_directed_rows']+=1;files[f]['shared_chars']+=r['shared']
  files[a]['outgoing_rows']+=1;files[b]['incoming_rows']+=1;pairs[(a,b,r['kind'])]['rows']+=1;pairs[(a,b,r['kind'])]['shared_chars']+=r['shared']
 weights[side]=[dict(path=p,**files[p]) for p in sorted(files,key=lambda p:(-files[p]['shared_chars'],p))]
 matrix[side]=[dict(a=a,b=b,kind=k,**v) for (a,b,k),v in sorted(pairs.items())]
save('weighted-candidate-accounting.json',dict(scope='Inclusive per-file weights may overlap; directed rows and shared-character sums are raw screening measurements, not independent proof/debt counts. All file/pair buckets included.',summary={s:d[s] for s in ['base','head']},files=weights,ordered_file_pair_matrix=matrix))
print(json.dumps(dict(primary=dict(new=len(d['new']),gone=len(d['gone']),changed=len(d['changed_measurements'])),prior35_exactly_carried=len(classified_old),historical_partition=dict(collections.Counter(x['family'] for x in partition)),all_HEAD_rows=len(allrows),statuses=dict(collections.Counter(x['status'] for x in allrows))),indent=2))
