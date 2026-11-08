from pathlib import Path
import json, subprocess, hashlib, datetime
p=Path(__file__).resolve().parents[1]
R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4')
H='1096e50b4e105392737ec52939b1db0cdbd9316d'; B='9b5dcf46408db681bcbc721930ef2203fa6bc47d'
def j(n): return json.loads((p/n).read_text())
def sha(b): return hashlib.sha256(b).hexdigest()
def put(n,d):
 f=p/n; f.parent.mkdir(parents=True,exist_ok=True); f.write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n')
def git(*args): return subprocess.check_output(['git','-C',str(R),*args])
def leanmap(c):
 assert git('rev-parse',c+'^{commit}').decode().strip()==c
 git('cat-file','-e',c+'^{commit}')
 return {r.split('\t',1)[1]:r.split()[2] for r in git('ls-tree','-r',c).decode().splitlines() if r.split('\t',1)[1].endswith('.lean')}
b=leanmap(B); h=leanmap(H)
assert b==j('evidence/source-QA119/current/BASE-ALL-LEAN-BLOBS.json')
assert h==j('evidence/source-QA119/current/HEAD-ALL-LEAN-BLOBS.json')
s=j('evidence/actual-validation162/inputs/passed-Nlad2/source-before.json')
a=j('anchors/MAC8/object-hashes.json')
ib=j('evidence/actual-validation162/inputs/passed-Nlad2/input-before.json')
ia=j('evidence/actual-validation162/inputs/passed-Nlad2/input-after.json')
o=j('evidence/actual-validation162/inputs/passed-Nlad2/output.json')
assert h=={k:v['git_blob'] for k,v in s.items()}
assert b==j('anchors/MAC8/Lean-tree.json') and a==ib==ia
capture_binding=j('bindings/FULL-SCREEN-SOURCE-CAPTURES.json')
capture_binding['phases']={'BASE':48,'LADNER':49}
capture_binding['capture_side_alias']={'BASE':'BASE','LADNER':'HEAD'}
caps=capture_binding['rows']; capchecks=[]
for r in caps:
 f=p/r['capture']; data=f.read_bytes(); assert len(data)==r['bytes'] and sha(data)==r['sha256']
 r['capture_side']='BASE' if r['phase']=='BASE' else 'HEAD'
 if r['path'].startswith('TCSlib'):
  m=b if r['phase']=='BASE' else h
  assert m[r['path']]==r['git_blob']
  if r['phase']=='LADNER': assert s[r['path']]['sha256']==r['sha256'] and s[r['path']]['bytes']==r['bytes']
 capchecks.append({'capture':r['capture'],'sha256':sha(data),'bytes':len(data),'git_blob':r['git_blob'],'matches_declared_source_origin':True})
put('bindings/FULL-SCREEN-SOURCE-CAPTURES.json',capture_binding)
changed=[k for k in sorted(set(b)|set(h)) if b.get(k)!=h.get(k)]
added=sorted(set(o)-set(a)); removed=sorted(set(a)-set(o)); rewritten=[k for k in sorted(set(a)&set(o)) if a[k]!=o[k]]
assert changed==['TCSlib/Complexity/Diagonalization.lean','TCSlib/Complexity/Diagonalization/Ladner.lean']
assert added==['TCSlib/Complexity/Diagonalization/Ladner.olean'] and not removed
assert rewritten==['TCSlib/Complexity/Diagonalization.olean']
headpaths={r['path'] for r in caps if r['phase']=='LADNER'}
homes=[str(x.relative_to(p/'evidence/actual-validation162/inputs/source-homes'))[:-4] for x in (p/'evidence/actual-validation162/inputs/source-homes').rglob('*.lean.txt')]
assert len(homes)==15 and set(homes)<=headpaths
put('bindings/SOURCE-OBJECT-EVIDENCE-CHECK.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'read_only_git_validation':{'BASE':B,'HEAD':H,'rev_parse_and_cat_file_checked':True,'BASE_Lean_paths':len(b),'HEAD_Lean_paths':len(h),'all_source_QA_Git_blob_rows_exact':True,'all_Nlad2_1004_blob_rows_exact':True,'all_MAC8_1003_blob_rows_exact':True,'changed_source_paths':changed,'unchanged_existing_source_paths':len(b)-1},'objects':{'MAC8':len(a),'Nlad2_output':len(o),'input_before_after_exact_MAC8':True,'added':added,'removed':removed,'rewritten_old_objects':rewritten,'all_other_894_old_objects_byte_hash_exact':True,'owner_object_sha256':o[added[0]]},'captures':{'full_rows':capchecks,'all15_cited_TCS_homes_in_HEAD49':sorted(homes),'BASE_Ladner_absence':'TCSlib/Complexity/Diagonalization/Ladner.lean' not in b,'no_invented_empty_BASE_file':not (p/'source/BASE/TCSlib/Complexity/Diagonalization/Ladner.lean.txt').exists()},'limits':['Git blob/source/object-map binding only; no new Lean execution or copied olean objects.','Full owned-type/AX scope remains selected17, not a global compiled census.','Joint prospective source a342 is not a replacement for standalone1096/Nlad2 audit evidence.']})
query=j('names/PINNED-QUERY.json'); hits=(p/'names/PINNED-name-and-shape-hits.txt').read_text().splitlines(); rows=[]; captures={}
for line in hits:
 c,path,lineno,text=line.split(':',3); key=(c,path)
 if key not in captures:
  data=git('show',c+':'+path); blob=git('rev-parse',c+':'+path).decode().strip(); digest=sha(data)
  out='names/candidates/'+digest+'/'+path+'.txt'; f=p/out; f.parent.mkdir(parents=True,exist_ok=True)
  if not f.exists(): f.write_bytes(data)
  captures[key]={'commit':c,'path':path,'blob':blob,'sha256':digest,'bytes':len(data),'capture':out}
 assert captures[key]['commit'] in {r['commit'] for r in query['refs']}
 data=(p/captures[key]['capture']).read_text().splitlines(); assert data[int(lineno)-1]==text
 rows.append({'commit':c,'path':path,'line':int(lineno),'text':text,'capture':captures[key]['capture']})
put('names/CANDIDATE-CAPTURES-AND-DISPOSITIONS.json',{'source_query':'names/PINNED-QUERY.json','full_query_stdout':'names/PINNED-name-and-shape-hits.txt','all_uncapped_rows_match_actual_source_lines':True,'row_count':len(rows),'source_commit_path_count':len(captures),'unique_captured_payload_count':len({r['capture'] for r in captures.values()}),'capture_rows':list(captures.values()),'full_hit_rows':rows,'dispositions':[{'path':'TCSlib/Complexity/Diagonalization/Ladner.lean','disposition':'Planned new owner; matches include its seventeen declarations and literal padding/log definition. Exact source1096 is separately current. Joint/local/records occurrences are candidate enumeration only.'},{'path':'TCSlib/Complexity/CircuitComplexity.lean','disposition':'Module Contents text summarizes NP not subset P/poly implies P != NP; no Ladner definitions or intermediate-language theorem.'},{'path':'TCSlib/Complexity/CircuitComplexity/PSubsetPPoly.lean','disposition':'P_ne_NP_of_not_NP_subset_PPoly has premise not (NP subset BoolCircuit.PPoly) and conclusion P != NP. This is the circuit containment implication, not a padded intermediate-language construction.'},{'path':'TCSlib/Complexity/ClassNP/Nondeterminism.lean','disposition':'P_ne_NP_of_EXP_ne_NEXP has premise EXP != NEXP and conclusion P != NP, a nondeterministic padding implication; no Ladner intermediate-language construction.'}],'limits':'Bounded available-ref literal-name/shape candidate enumeration. These unrelated candidates are not new proof dependencies and are not silently added to the declared48/49 consumer screen. No semantic-global absence or all-repository duplication clearance is claimed.'})
print(json.dumps({'maps':{'BASE':len(b),'HEAD':len(h),'MAC8':len(a),'Nlad2':len(o)},'current_captures':len(capchecks),'name_rows':len(rows),'unique_name_source_payloads':len({r['capture'] for r in captures.values()})}))
