from pathlib import Path
import collections,datetime,hashlib,json,subprocess,time
OUT=Path(__file__).resolve().parent;ROOT=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');OLD=ROOT/'campaign/fills/mig1/landing/screen-current25-final'
read=lambda p:json.loads(p.read_text());save=lambda n,x:(OUT/n).write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n');sha=lambda b:hashlib.sha256(b).hexdigest()
C=read(OUT/'capture.json');D=read(OUT/'pair-delta.json');progress=read(OUT/'previousB1-to-currentHEAD-delta.json');key=lambda r:(r['a'],r['b']);std=lambda x:dict(a=x['target'],b=x['source'],shared=x['shared_chars'],denominator=x['source_body_chars'],printed_percent=x['rounded_percent'],kind=x['kind'],cross_file=x['cross_file'])
indexes={s:{x['label']:x for x in read(OUT/(s+'-index.json'))} for s in ['base','head']};oldindex=read(OLD/'head-screen-index.json');oldrows={key(std(x)):std(x) for x in read(OLD/'head-all-candidates.json')};oldclasses={(x['target'],x['source']):x for x in read(OLD/'vs-base-classifications.json')}
resource='Use of published pairDiagTM_computes with concrete coefficient/witness packaging; the Catalog space conjunct now directly cites the merged pairDiagTM_spaceUsed zero-space fact. The old zero-tape resource HOLD is historical and not carried. Six71/79-character directed matches are public-API consumer applications, not reconstructed transition/space proofs. No general debt waiver.'
redirect='Exact published redirect per-tape equality is now at its approved Wrappers home. The two larger branch/timed-space bounds share card/membership interface syntax with this172-character reader; their total bound/ledger conclusions differ from per-tape equality. The old Catalog-home HOLD is resolved by merged #234 and is historical. No new debt acceptance.'
cond='Material1027-character overlap remains in two distinct native conditional setup proofs. Both now apply published exists_first_halt, branch shape/initCfg equations and explicit field readers. Shared branch-view transports, singleton-output transport and caller-specific initial/final Cfg.ext scaffolding are retained. Untimed control/rewind concludes an existential rightCfg endpoint; timed capture/read/rewind additionally proves≤2T+5 and a different timedBranchCfg endpoint. The shared first-halt fact is already a public citation, not a Nat.find reproof. No exact published contract for the entire different host endpoints was exposed by these inspected chunks; no new API/debt/global absence is inferred.'
endpoint='The574/1122 match follows explicit reuse of public exists_first_halt, initCfg/field equations and native start normalization. lenStart captures arbitrary output, takes a back step and quantitatively rewinds; emCall_right_endpoint performs a right scan and absorbs the completed run to its advertised deadline. They establish different machine/configuration/time endpoints. The generic first-halt proof is not repeated; concrete endpoint reader scaffolding remains disclosed without a blanket debt exemption.'
new=[]
for r in D['new']:
 k=key(r);o=oldclasses.get(k)
 if 'Catalog.lean::computesFunInTime_pairDup_spaceUsed' in k or (o and o['group']=='G12'):
  group='R12 current published zero-space/witness consumers';assessment=resource;origin='Fresh inspected API-based resource wrapper, updates historical G12.'
 elif r['b']=='Wrappers.lean::redirectTM_spaceUsedByTape':group='R13 approved redirect home/current card-reader consumers';assessment=redirect;origin='Exact old raw measurements rebound to current approved home; actual current canonical proof read.'
 elif k==('Composition.lean::condTM_start','Wrappers.lean::timed_start'):group='R19 conditional reader/transport scaffold';assessment=cond;origin='Both complete current statements/proofs read against published contracts.'
 elif k==('Primitives.lean::lenStart','Loop.lean::emCall_right_endpoint'):group='R20 distinct capture/scan endpoint scaffolding';assessment=endpoint;origin='Both complete current statements/proofs read against published contracts.'
 else:
  assert o and std(o)==r,(k,'missing old row')
  for label in k:assert oldindex[label]['body_sha256']==sha(indexes['head'][label]['normalized_body'].encode()),(label,'changed endpoint')
  group=o['group']+' '+o['group_title'];assessment=o['disposition'];origin='Exact historical row measurement AND both normalized endpoint bodies verified unchanged; historical status is preserved, not new acceptance.'
 new.append(dict(change='new',row=r,group=group,assessment=assessment,origin=origin))
oldchanged=read(OLD/'vs-base-changed-metrics.json');oldchanges={(x['head']['target'],x['head']['source']):dict(base=std(x['earlier']),head=std(x['head'])) for x in oldchanged};changed=[]
for x in D['changed_measurements']:
 r=x['head'];k=key(r)
 if k in [('Loop.lean::emCall_first_entry','Primitives.lean::emitter_first_entry'),('Primitives.lean::emitter_first_entry','Loop.lean::emCall_first_entry')]:
  group='R21 direct public fixed-LIVE-stop compatibility citations';assessment='Both surviving private headers now directly cite exists_first_entry_of_fixed. The two reciprocal100% rows shrink403→63 characters. This is one public-call spelling in two compatibility adapters, not two retained Nat.find/fixedness implementations; source declaration deletion and global family retirement are not inferred.'
 elif k==('Composition.lean::condTM_start','Simulation.lean::leftCfg_apply'):
  group='R22 reader-based Cfg normalization overlap';assessment='The match drops125→95/188 as condTM_start replaces foreign reductions with explicit readers/transports. Its initial/final configuration normalization is not Action.apply/leftCfg commutation; inspected source uses existing initCfg/field equations. The residual field-reader/extensionality idiom is retained, not globally waived.'
 else:
  assert oldchanges.get(k)==x,(k,'new changed measurement not classified');group='Historical exact changed measurement';assessment='The exact old/current measurement pair equals the historical BASE/B1 record. Prior separately scoped source/family dispositions remain visible; this provenance does not accept all retained debt or certify semantic equivalence.'
 changed.append(dict(change='changed',row=x,group=group,assessment=assessment))
gone=[]
for r in D['gone']:
 status={label:('outside current v3 eligible population' if label not in indexes['head'] else 'current eligible body changed' if indexes['base'][label]['normalized_body']!=indexes['head'][label]['normalized_body'] else 'eligible body unchanged') for label in key(r)}
 assert any(v!='eligible body unchanged' for v in status.values()),r
 gone.append(dict(change='gone',row=r,endpoint_status=status,assessment='Directed textual edge removed by the inspected MIG source fates/body changes. Leaving eligibility can mean declaration removal, shortening, or a changed label; this edge is not one independently retired declaration. Complete source fates and runtime/public constraints are in sibling post234-source-QA-final. No new debt acknowledgment.'))
save('current-delta-classification.json',dict(scope='Every58 new/1145 gone/30 changed directed row retained uncapped. Historical source-read groups reused only on exact body/measurement equivalence; obsolete resource/home HOLD wording updated with merged public APIs.',new=new,gone=gone,changed=changed))
# All small B1 progression rows get an explicit updated reason; full rows stay preserved.
prog=[]
for status,rs in progress.items():
 for r in rs:
  row=r['current'] if status=='changed' else r;k=key(row)
  if 'redirectTM_spaceUsedByTape' in ' '.join(k):why=redirect
  elif any('first_entry' in z or 'catalogFirstEntry' in z for z in k):why='Existing FE-LIVE-1 implementations now use the merged generic public first-entry theorem. The whole-config fixed LIVE-stop predicate/singleton premise is unchanged. Short public-call twins persist at63 characters; old larger proof-fragment edges disappear. Proposed retirement applies to implementations on merge, not to all source names or global copies.'
  elif 'splitEmbed_cut' in ' '.join(k):why='Public fixed-LIVE-stop first-entry reuse and explicit configuration readers replace the old step-fragment reconstruction; these removed edges are not declaration deletions.'
  elif 'condTM_start' in ' '.join(k):why=cond if status=='new' else 'Explicit public state/tape/head/initCfg readers and approved carrier transports replace foreign reductions. The old rightCfg_apply-like fragment disappears and the leftCfg_apply match becomes95/188; concrete configuration conclusions differ.'
  elif 'lenStart' in ' '.join(k):why=endpoint
  else:why=resource
  prog.append(dict(change=status,row=r,assessment=why))
save('previousB1-progression-classification.json',dict(rows=prog,scope='All6 new/13 gone/3 changed progression rows, not a semantic all-library absence/debt assertion.'))
# Retain every actual HEAD candidate with provenance/assessment; no blanket old-debt acceptance.
newmap={key(x['row']):x for x in new};changedmap={key(x['row']['head']):x for x in changed};allhead=[];body_updates=[]
for r in read(OUT/'head-candidates.json'):
 k=key(r)
 if k in newmap:status='Current new row explicitly classified';assessment=newmap[k]['assessment'];group=newmap[k]['group']
 elif k in changedmap:status='Current changed retained row explicitly classified';assessment=changedmap[k]['assessment'];group=changedmap[k]['group']
 else:
  assert oldrows.get(k)==r,(k,'untracked current row')
  same=all(label in oldindex and oldindex[label]['body_sha256']==sha(indexes['head'][label]['normalized_body'].encode()) for label in k)
  status='Historical identical retained candidate' if same else 'Historical measurement with updated approved proof body'
  group=r['kind']+('/cross-file' if r['cross_file'] else '/in-file');assessment='Existing raw candidate and its exact directed measurement are preserved with their separately scoped prior records. This provenance grants no semantic equivalence, new debt acknowledgment, major clearance or global absence.'
  if not same:body_updates.append(r)
 allhead.append(dict(row=r,status=status,group=group,assessment=assessment))
save('all-HEAD-candidate-classification.json',dict(rows=allhead,counts=dict(collections.Counter(x['status'] for x in allhead)),scope='All615 actual rows. Historical status is provenance, not blanket acceptance.'));save('retained-measurements-updated-bodies.json',body_updates)
weights={};matrices={}
for side in ['base','head']:
 files={p:dict(incident_rows=0,shared_chars=0,outgoing_rows=0,incoming_rows=0) for p in C['population']};matrix=collections.defaultdict(lambda:dict(rows=0,shared_chars=0))
 for r in read(OUT/(side+'-candidates.json')):
  a=indexes[side][r['a']]['path'];b=indexes[side][r['b']]['path']
  for p in {a,b}:files[p]['incident_rows']+=1;files[p]['shared_chars']+=r['shared']
  files[a]['outgoing_rows']+=1;files[b]['incoming_rows']+=1;matrix[(a,b,r['kind'])]['rows']+=1;matrix[(a,b,r['kind'])]['shared_chars']+=r['shared']
 weights[side]=[dict(path=p,**v) for p,v in sorted(files.items(),key=lambda x:(-x[1]['shared_chars'],x[0]))];matrices[side]=[dict(a=a,b=b,kind=k,**v) for (a,b,k),v in sorted(matrix.items())]
save('weighted-candidate-accounting.json',dict(summary={s:D[s] for s in ['base','head']},files=weights,ordered_file_pair_matrix=matrices,interpretation='Complete inclusive weights overlap, and directed rows are not semantic duplicate/declaration/debt counts. No caps.'))
for name,head,earlier in [('canonical-pairdiff-current',OUT/'head.out',OUT/'base.out'),('canonical-pairdiff-B1',OUT/'head.out',OLD/'head.out')]:
 cmd=['python3','-I',str(ROOT/'devtools/seyoon/pairdiff.py'),str(head),str(earlier)];tick=time.time();q=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.PIPE);(OUT/(name+'.out')).write_bytes(q.stdout);(OUT/(name+'.stderr.out')).write_bytes(q.stderr);save(name+'-run.json',dict(command=cmd,seconds=time.time()-tick,exit=q.returncode,tool_sha256=sha((ROOT/'devtools/seyoon/pairdiff.py').read_bytes()),stdout_sha256=sha(q.stdout),stderr_sha256=sha(q.stderr)));assert q.returncode==0
print(json.dumps(dict(new=len(new),gone=len(gone),changed=len(changed),all_HEAD=len(allhead),classification_counts=dict(collections.Counter(x['status'] for x in allhead)),retained_measurements_with_updated_bodies=len(body_updates)),indent=2))
