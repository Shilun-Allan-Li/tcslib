from pathlib import Path
import hashlib,json,re,difflib,shutil
O=Path('/private/tmp/ab34-overnight-sg1-harvest');R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4')
def sha(b):return hashlib.sha256(b).hexdigest()
def getchunk(s,n):
 m=re.search(r'(?m)^(?:private )?(?:lemma|theorem) '+re.escape(n)+r'\b',s)
 if not m:raise ValueError(n)
 a=s.rfind('/--',0,m.start());ends=[i for pat in ['\n/--','\n/-!','\nend ','\nnamespace '] if (i:=s.find(pat,m.end()))>=0];e=min(ends)
 return s[a:e].rstrip()
work={
'TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean':{
 'step_output_prefix':('Turing.MultiTapeTM.step_output_prepend','  exact MultiTapeTM.step_output_prepend H c pre'),
 'runFrom_output_prefix':('Turing.MultiTapeTM.runFrom_output_prepend','  exact MultiTapeTM.runFrom_output_prepend H c pre t'),
 'runFrom_output_extends':('Turing.MultiTapeTM.output_prefix','  obtain ⟨o, ho⟩ := MultiTapeTM.output_prefix H c (Nat.zero_le t)\n  exact ⟨o, by simpa only [MultiTapeTM.runFrom_zero] using ho.symm⟩'),
 'runFrom_of_halted':('Turing.MultiTapeTM.runFrom_of_halt','  exact MultiTapeTM.runFrom_of_halt (tm := H) c h'),
 'state_isSome_of_runFrom':('Turing.MultiTapeTM.runFrom_state_ne_none_of_le','  have hl := MultiTapeTM.runFrom_state_ne_none_of_le H c t\n    (by rw [hf]; exact Option.some_ne_none _) j hj\n  cases hq : (H.runFrom c j).state with\n  | some q => exact ⟨q, rfl⟩\n  | none => exact False.elim (hl hq)')},
'TCSlib/Complexity/ClassNP/SAT.lean':{
 'sat_first_halt':('Turing.MultiTapeTM.exists_first_halt',"  have hh := (FinTM.computesInTime_iff _ _ _ _).mp h\n  obtain ⟨t, ht, hg, he⟩ := MultiTapeTM.exists_first_halt M.tm (M.tm.initCfg x) hh.1\n  refine ⟨t, ht, hg, ?_, ?_⟩\n  · rw [he]; exact hh.1\n  · rw [he]; exact hh.2"),
 'sat_call_first_halt':('Turing.MultiTapeTM.exists_first_halt',"  obtain ⟨u, hu, hg, he⟩ := MultiTapeTM.exists_first_halt tm cfg hhalt\n  have hp : 0 < u := by\n    by_contra hn\n    have hz : u = 0 := by omega\n    have hs := congrArg Cfg.state he\n    rw [hz, MultiTapeTM.runFrom_zero, hhalt] at hs\n    exact hstart hs\n  exact ⟨u, hp, hu, hg, he⟩")},
'TCSlib/Complexity/CookLevin/Hardness.lean':{
 'clA5_call_first_halt':('Turing.MultiTapeTM.exists_first_halt',"  obtain ⟨u, hu, hg, he⟩ := MultiTapeTM.exists_first_halt tm cfg hhalt\n  have hp : 0 < u := by\n    by_contra hn\n    have hz : u = 0 := by omega\n    have hs := congrArg Cfg.state he\n    rw [hz, MultiTapeTM.runFrom_zero, hhalt] at hs\n    exact hstart hs\n  exact ⟨u, hp, hu, hg, he⟩")}}
records=[];patches=[];project=O/'native-project';(project/'.lake').mkdir(parents=True,exist_ok=True)
packages=project/'.lake/packages'
if not packages.exists():packages.symlink_to(R/'.lake/packages',target_is_directory=True)
shutil.copyfile(R/'lean-toolchain',project/'lean-toolchain')
for path,targets in work.items():
 original=(O/'source'/(path+'.txt')).read_text();current=original
 for name,(api,body) in targets.items():
  old=getchunk(current,name);header=old.split(':= by',1)[0];new=header+':= by\n'+body
  if name in {'sat_call_first_halt','clA5_call_first_halt'}:
   olddoc=old.split('-/',1)[0]+'-/'
   newdoc='/-- A padded halting run can be cut at its first positive halt without changing\nany endpoint field. Apply `Turing.MultiTapeTM.exists_first_halt`; the live\ninitial state excludes time zero. -/'
   new=new.replace(olddoc,newdoc,1)
  oldheader=old[old.index('private lemma ' if 'private lemma ' in old else 'theorem '):].split(':= by',1)[0]
  newheader=new[new.index('private lemma ' if 'private lemma ' in new else 'theorem '):].split(':= by',1)[0]
  assert oldheader==newheader
  current=current.replace(old,new,1)
  records.append({'path':path,'name':name,'published_API':api,'source_pin':'9b5dcf46408db681bcbc721930ef2203fa6bc47d','original_source_sha256':sha(original.encode()),'header_sha256':sha(oldheader.encode()),'old_chunk':old,'proposed_chunk':new,'old_chunk_sha256':sha(old.encode()),'proposed_chunk_sha256':sha(new.encode()),'header_exact':True,'new_import_API_name_statement_route':False,'status':'source-reviewed exact mechanical draft; native pending'})
 q=O/'proposed-source'/(path+'.txt');q.parent.mkdir(parents=True,exist_ok=True);q.write_text(current)
 patches+=difflib.unified_diff(original.splitlines(keepends=True),current.splitlines(keepends=True),fromfile='a/'+path,tofile='b/'+path)
 prints='\n\n'+'\n'.join('#print axioms '+('Turing.' if 'EmitIterEmbed' in path else 'Complexity.')+n for n in targets)+'\n'
 q=project/path;q.parent.mkdir(parents=True,exist_ok=True);q.write_text(current+prints)
 probe=O/'probes'/(path+'.txt');probe.parent.mkdir(parents=True,exist_ok=True);probe.write_text(current+prints)
(O/'mechanical-draft.patch').write_text(''.join(patches));(O/'mechanical-chunk-mappings.json').write_text(json.dumps(records,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'owners':len(work),'mechanical_roots':len(records),'imports_headers_names_exact':True,'native_pending':True,'snapshot':'whole oleans-mac8 root-supplied9b5'}))
