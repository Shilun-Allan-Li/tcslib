from pathlib import Path
import json,re,hashlib,difflib,datetime
OUT=Path(__file__).resolve().parent;ROOT=OUT.parents[4];WT=Path('/Users/seyoonr/.codex/worktrees/ab34-sg1/tcslib-arora-barak-ch3-4')
prior=json.loads((ROOT/'campaign/gates/106-sg1-dedup/review/round2-findings-review/mechanical-repoint-candidates.json').read_text())
assert len(prior)==13
bodies={
'sat_pt_pair_input':'  exact PolyTimeComputable.pairEncode hf polyTimeComputable_id\n',
'sat_pt_pair':'  exact PolyTimeComputable.pairEncode hf hg\n',
'clNative_pair':'  exact PolyTimeComputable.pairEncode hf hg\n',
'sat_pt_append':'  exact PolyTimeComputable.append hf hg\n',
'clNative_append':'  exact PolyTimeComputable.append hf hg\n',
'sat_pt_unaryLength':'  exact polyTimeComputable_unary\n',
'clNative_unary':'  exact polyTimeComputable_polyUnary C e\n',
'clNative_linear':'  exact polyTimeComputable_of_linear h\n',
'clA5_pt_const':'  exact polyTimeComputable_const w\n',
'clA5_pt_cond':'  exact polyTimeComputable_ite hp hf hg\n',
'clA5_pt_and':'  exact polyTimeComputable_and hp hq\n'}
mapbody='''  have he : Complexity.pairMapSnd g = (fun z => match pairDecode z with
      | some (a, b) => pairEncode a (g b)
      | none => []) := funext (Complexity.pairMapSnd.eq_1 g)
  rw [← he]
  exact PolyTimeComputable.pairMapSnd hg
'''
bodies.update({'sat_pt_mapSnd':mapbody,'clNative_map':mapbody})
newdocs={
'sat_pt_mapSnd':'''/-- The published threaded-map closure preserves the first field while applying a
polynomial-time function to the payload, with empty output on malformed pairs. -/''',
'clNative_linear':'''/-- Linear-time computation is polynomial-time, by
`Complexity.polyTimeComputable_of_linear`. -/''',
'clNative_map':'''/-- Threaded payload mapping preserves polynomial time, including malformed inputs,
by `Complexity.PolyTimeComputable.pairMapSnd`. -/''',
'clNative_pair':'''/-- Two separately computed polynomial-time fields can be paired on their shared
input, by `Complexity.PolyTimeComputable.pairEncode`. -/''',
'clNative_append':'''/-- Concatenating polynomial-time field computations preserves polynomial time,
by `Complexity.PolyTimeComputable.append`. -/''',
'clNative_unary':'''/-- The exact unary polynomial `1^(C * (|x| + 1)^e)` is polynomial-time computable,
by `Complexity.polyTimeComputable_polyUnary`. -/''',
'clA5_pt_cond':'''/-- Polynomial-time branching on a polynomial-time bit preserves polynomial time,
by `Complexity.polyTimeComputable_ite`. -/'''}
changes=[];ctx={'status':'Authorized13 private proof-only canonical closure repoints; no extra source scope','worktree':str(WT),'snapshot':'/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/oleans-msg4','head_verified_readonly':'478cd3a8dfb46094b9d8b971662f2ddadb1eccdb','at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':{}}
for rel in sorted({r['file'] for r in prior}):
 src=WT/rel;raw=src.read_text();tag='SAT' if rel.endswith('/SAT.lean') else 'Hardness'
 expected=ROOT/'campaign/gates/106-sg1-dedup/review/round2-current/head-source'/(rel+'.txt');assert raw==expected.read_text(),rel
 (OUT/(tag+'-before.lean.txt')).write_text(raw)
 edits=[]
 for row in prior:
  if row['file']!=rel:continue
  name=row['name'];m=re.search(r'(?m)^private lemma '+re.escape(name)+r'\b',raw);assert m,name
  ds=raw.rfind('/--',0,m.start());de=raw.index('-/',ds)+2;assert raw[de:m.start()].strip()==''
  proof=raw.index(':= by',m.start())+len(':= by');eol=raw.index('\n',proof);assert raw[proof:eol].strip()==''
  end=raw.find('\n\n/--',eol);assert end>=0,name
  oldbody=raw[eol+1:end+1];newbody=bodies[name]
  olddoc=raw[ds:de];newdoc=newdocs.get(name,olddoc)
  edits.extend([(eol+1,end+1,newbody),(ds,de,newdoc)])
  changes.append({'file':rel,'name':name,'old_line':raw[:m.start()].count('\n')+1,'header':raw[m.start():proof],'old_body':oldbody,'new_body':newbody,'old_doc':olddoc,'new_doc':newdoc,'doc_changed':newdoc!=olddoc})
 after=raw
 for a,b,replacement in sorted(edits,reverse=True):after=after[:a]+replacement+after[b:]
 (OUT/(tag+'-after.lean.txt')).write_text(after)
 (OUT/(tag+'.patch')).write_text(''.join(difflib.unified_diff(raw.splitlines(True),after.splitlines(True),fromfile='a/'+rel,tofile='b/'+rel)))
 ctx['files'][rel]={'before_sha256':hashlib.sha256(raw.encode()).hexdigest(),'after_sha256':hashlib.sha256(after.encode()).hexdigest(),'archive_tag':tag}
(OUT/'changes.json').write_text(json.dumps(changes,indent=2)+'\n');(OUT/'context.json').write_text(json.dumps(ctx,indent=2)+'\n')
print(json.dumps({'files':ctx['files'],'proofs':len(changes),'doc_updates':sum(x['doc_changed'] for x in changes)},indent=2))
