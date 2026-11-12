from pathlib import Path
import subprocess,os,tarfile,io,json,hashlib,re,difflib
O=Path(__file__).parent;E=O/'evidence';R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');S=Path(os.environ['TCSLIB_SCRATCH']);HEAD='f3c8c050ef98375bc237c72bde74f83d33833374';BASE='9b5dcf46408db681bcbc721930ef2203fa6bc47d';env=os.environ|{'GIT_OPTIONAL_LOCKS':'0'};W=O/'runtime/project';OV=O/'runtime/oleans-proposal';W.mkdir(parents=True)
H=lambda b:hashlib.sha256(b).hexdigest()
def git(*args):return subprocess.check_output(['git','-C',str(R),*args],env=env)
def save(n,a):(E/n).write_text(json.dumps(a,ensure_ascii=False,indent=2)+'\n')
paths=[p for p in git('ls-tree','-r','--name-only',HEAD).decode().splitlines() if p.endswith('.lean')];assert len(paths)==1003
archive=git('archive',HEAD,*paths,'lean-toolchain','lake-manifest.json');inventory=[]
with tarfile.open(fileobj=io.BytesIO(archive)) as tar:
 for m in tar.getmembers():
  p=Path(m.name);assert not p.is_absolute() and '..' not in p.parts
  if m.isdir():continue
  assert m.isfile();data=tar.extractfile(m).read();q=W/p;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(data);inventory.append({'path':m.name,'bytes':len(data),'sha256':H(data)})
(W/'.lake').mkdir();(W/'.lake/packages').symlink_to(R/'.lake/packages',target_is_directory=True);(E/'helpers').mkdir()
for name in ['leanelab.sh','leanelab-o.sh']:(E/'helpers'/name).write_bytes((R/'devtools/seyoon'/name).read_bytes())
for name in ['lean-toolchain','lake-manifest.json']:(E/'helpers'/name).write_bytes((W/name).read_bytes())
owner='TCSlib/Complexity/SpaceComplexity/ConfigCount.lean';consumer='TCSlib/Complexity/SpaceComplexity/Machines/MARMTime.lean';obase=(W/owner).read_text();mbase=(W/consumer).read_text();assert git('show',BASE+':'+consumer).decode()==mbase
# Locate all named/source candidates before proposing a reader, not after adding the hypothetical name.
search=[]
for path in paths:
 for i,l in enumerate((W/path).read_text().splitlines(),1):
  if re.search(r'core_eq|core_iff|core_eq_iff|ConfigCount\.core|(?:lemma|theorem) core(?:_|\b)',l):search.append({'path':path,'line':i,'text':l})
assert not any(re.match(r'(?:theorem|lemma) core_eq\b',x['text']) for x in search)
save('EXISTING-READER-SEARCH.json',{'source':HEAD,'tracked_Lean_population':1003,'raw_uncapped_candidates':search,'no_matching_named_constructor_or_equality_iff_reader_found':True,'existing_relevant_contracts':['core_step transports equal cores across one step','core_runFrom transports equal cores across runs','core_injOn rules out equal cores before halt','coreCode_inj constructs equal cores from a different opaque finite code under bounds'],'why_not_equivalent':'None of these existing contracts introduces core equality from exactly state/inputPos/workTapes/workTapePos equalities. coreCode_inj would require reading a second foreign code definition; Cfg.ext also needs output equality, intentionally absent from core. This is bounded source/statement inspection, not a semantic impossibility claim.'})
lemma=r'''/-- The core records exactly the state, input position, work tapes and work-head
positions of a configuration, in that order; it omits the output tape. -/
theorem core_eq (c : Cfg k Bool S x) :
    core c = (c.state, c.inputPos, c.workTapes, c.workTapePos) := by
  rfl
'''
marker='/-- The core after a step depends only on the core before it. -/';assert obase.count(marker)==1;ocand=obase.replace(marker,lemma+'\n'+marker);assert ocand.replace(lemma+'\n','')==obase;(W/owner).write_text(ocand)
start=mbase.index('open MultiTapeTM.ConfigCount in\n/-- **A run whose last tape only grows');stop=mbase.index('\nend Count',start);old=mbase[start:stop];new=old;header=old[:old.index(':= by\n')+len(':= by\n')]
s='''  have hex : ∃ t, (run t).state = none := ⟨T, hT⟩
  set T₀ := Nat.find hex with hT₀
  have hT0 : (run T₀).state = none := Nat.find_spec hex
  have hT0T : T₀ ≤ T := Nat.find_min' hex hT
  have hmin : ∀ t < T₀, (run t).state ≠ none := fun t ht => Nat.find_min hex ht'''
t='''  obtain ⟨T₀, hT0T, hmin, hfirst⟩ :=
    MultiTapeTM.exists_first_halt tm (tm.initCfg x) hT
  have hT0 : (run T₀).state = none := (congrArg Cfg.state hfirst).trans hT''';assert new.count(s)==1;new=new.replace(s,t)
s='''    simp only [MultiTapeTM.visitedByTapeHead, Finset.mem_image, Finset.mem_range] at this
    obtain ⟨t', ht', e⟩ := this
    exact ⟨t', by omega, e⟩''';t='''    exact (MultiTapeTM.mem_visitedByTapeHead_iff (tm := tm) (tm.initCfg x) t i z).mp this''';assert new.count(s)==1;new=new.replace(s,t)
s='    simp only [core, Prod.mk.injEq]';t='    simp only [core_eq, Prod.mk.injEq]';assert new.count(s)==1;new=new.replace(s,t)
a=new.index('  rw [show (Fintype.card St + 1)');new=new[:a]+'''  calc
    tm.runFrom (tm.initCfg x) ((Fintype.card St + 1) * (x.length + 2) * 3 ^ (K * (2 * B + 1)) *
        (2 * B + 1) ^ K * ((2 * P + 1) * (2 * P + 2))) = tm.runFrom (tm.initCfg x) T₀ := by
      rw [show (Fintype.card St + 1) * (x.length + 2) * 3 ^ (K * (2 * B + 1)) *
          (2 * B + 1) ^ K * ((2 * P + 1) * (2 * P + 2)) =
          T₀ + ((Fintype.card St + 1) * (x.length + 2) * 3 ^ (K * (2 * B + 1)) *
          (2 * B + 1) ^ K * ((2 * P + 1) * (2 * P + 2)) - T₀) by omega,
        MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hT0]
    _ = tm.runFrom (tm.initCfg x) T := hfirst
''';assert new.startswith(header);mcand=mbase[:start]+new+mbase[stop:];(W/consumer).write_text(mcand)
for path,base,cand in [(owner,obase,ocand),(consumer,mbase,mcand)]:
 for side,text in [('BASE-f3',base),('CANDIDATE',cand)]:
  p=E/'source'/side/(path+'.txt');p.parent.mkdir(parents=True,exist_ok=True);p.write_text(text)
(E/'proposed-core-eq.lean.txt').write_text(lemma);(E/'MARMTime-target-BASE.lean.txt').write_text(old);(E/'MARMTime-target-CANDIDATE.lean.txt').write_text(new)
api=''.join(difflib.unified_diff(obase.splitlines(keepends=True),ocand.splitlines(keepends=True),fromfile='a/'+owner,tofile='b/'+owner));cons=''.join(difflib.unified_diff(mbase.splitlines(keepends=True),mcand.splitlines(keepends=True),fromfile='a/'+consumer,tofile='b/'+consumer));(E/'API-only.patch').write_text(api);(E/'consumer-only.patch').write_text(cons);(E/'combined-proposal.patch').write_text(api+cons)
subprocess.run(['cp','-cR',str(S/'oleans-mac8'),str(OV)],check=True)
def objects(root):return {str(p.relative_to(root)):H(p.read_bytes()) for p in sorted((root/'TCSlib').rglob('*.olean'))}
a=objects(S/'oleans-mac8');b=objects(OV);assert len(a)==895 and a==b==json.loads((R/'campaign/status/2026-11-08-mig1-merge/object-hashes.json').read_text())
save('INPUT895-original.json',a);save('INPUT895-clone-before.json',b);save('SOURCE1003-f3.json',inventory);save('SOURCE-BINDING.json',{'source_HEAD':HEAD,'snapshot_BASE':BASE,'producer':owner,'consumer':consumer,'new_reader':'Turing.MultiTapeTM.ConfigCount.core_eq','public_API_hypothesis_only':True,'non_simp':True,'existing_core_definition_full_source_preserved':True,'producer_all_other_source_exact_f3':True,'consumer_original_doc_header_and_all_other_source_exact':True,'consumer_complete_source_BASE9b5_f3_exact_before_repair':True,'original_producer_sha256':H(obase.encode()),'candidate_producer_sha256':H(ocand.encode()),'original_consumer_sha256':H(mbase.encode()),'candidate_consumer_sha256':H(mcand.encode()),'target_old_sha256':H(old.encode()),'target_new_sha256':H(new.encode()),'no_gate129_or_three_reader_dependency':True,'no_import_header_definition_attribute_change':True,'one_own_job_at_a_time':True,'localcap':3,'machinecap':5})
print('Prepared one core constructor-reader hypothesis and complete MARMTime candidate over exactf3/wholeMAC8; no source/Git writes.')
