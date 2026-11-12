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
owner='TCSlib/Complexity/TuringMachine/Build/NDClockHost.lean';consumer='TCSlib/Complexity/TuringMachine/Build/NDClockHostRun.lean';obase=(W/owner).read_text();cbase=(W/consumer).read_text();assert git('show',BASE+':'+owner).decode()==obase and git('show',BASE+':'+consumer).decode()==cbase
search=[]
for path in paths:
 for i,l in enumerate((W/path).read_text().splitlines(),1):
  if re.search(r'bootCfg|runCfg_init|runCfg_eq|hostCfg_eq',l):search.append({'path':path,'line':i,'text':l})
save('EXISTING-READER-SEARCH.json',{'source':HEAD,'source_population':1003,'all_raw_candidate_hits':search,'bounded_disposition':'Existing initCfg_eq_bootCfg/boot_run/rewind_run expose the phase contracts, but no named halted-boot constructor equation or initialized-run configuration equation was located. yard is an allowed reducible abbrev; no yard reader needed. Existing NDTM.initCfg_eq and Cfg.init field equations cover the imported initialization reads in the proposed owner lemma. This is candidate enumeration plus source inspection, not a semantic absence claim.'})
boot=r'''/-- A halted yardstick configuration is the rewind configuration with its output on the
extra tape and with the attempt bank blank. -/
theorem bootCfg_of_halt (c : Cfg S.k Bool S.State x) (hc : c.state = none) :
    bootCfg (A := A) c =
      hostCfg (some .rew) c.inputPos c.workTapes c.workTapePos (fun _ _ => none)
        (fun _ => 0) (bufferTape c.output) c.output.length [] := by
  simp only [bootCfg, hc, Option.map_none, Option.getD_none]
'''
run=r'''/-- The attempt configuration of the initial machine has the initial control and input
position, a blank attempt bank, and no captured output, at the given yardstick position. -/
theorem runCfg_initCfg (j : ℤ) (sT : Fin S.k → ℤ → Option Bool) (sP : Fin S.k → ℤ) :
    runCfg m (A.tm.initCfg x) j sT sP =
      hostCfg (some (.run (some A.tm.q₀) none)) 1 sT sP (fun _ _ => none)
        (fun _ => 0) (yard m) j [] := by
  have hw : (A.tm.initCfg x).workTapes = (fun _ _ => none) := by
    funext i z
    rw [NDTM.initCfg_eq, Cfg.init_workTapes]
  have hp : (A.tm.initCfg x).workTapePos = (fun _ => 0) := by
    funext i
    rw [NDTM.initCfg_eq, Cfg.init_workTapePos]
  rw [runCfg, hw, hp]
  simp only [NDTM.initCfg_eq, Cfg.init_state, Cfg.init_inputPos, Cfg.init_output, capOf]
'''
marker='/-- A boot step is a step of `S`, its emission appended to the yardstick tape.';assert obase.count(marker)==1;ocand=obase.replace(marker,boot+'\n'+marker);marker='/-- Before the timeout, a host step is a step of `A` under the same coin.';assert ocand.count(marker)==1;ocand=ocand.replace(marker,run+'\n'+marker);assert ocand.replace(boot+'\n','').replace(run+'\n','')==obase;(W/owner).write_text(ocand)
a=cbase.index('/-- **Startup**');b=cbase.index('/-- **One-shot run**',a);old=cbase[a:b];header=old[:old.index(':= by\n')+len(':= by\n')]
new=header+r'''  classical
  obtain ⟨hhalt, houtT⟩ := (FinTM.computesInTime_iff _ _ _ _).mp hS
  obtain ⟨tS, htS, hlive, hfirst⟩ :=
    MultiTapeTM.exists_first_halt S.tm (S.tm.initCfg x) hhalt
  let cS := S.tm.runFrom (S.tm.initCfg x) tS
  have hcS : cS.state = none := (congrArg Cfg.state hfirst).trans hhalt
  have hout : cS.output = List.replicate m true := (congrArg Cfg.output hfirst).trans houtT
  refine ⟨tS + (m + 2), by omega, cS.workTapes, cS.workTapePos, fun w hw => ?_⟩
  have ht : (w.take tS).length = tS := List.length_take_of_le (by omega)
  have hboot := boot_run (A := A) (loop := loop) (S.tm.initCfg x) (w.take tS)
    (fun t h => hlive t (by omega))
  rw [ht] at hboot
  rw [initCfg_eq_bootCfg, ← List.take_append_drop tS w, NDTM.runWith_append, hboot,
    bootCfg_of_halt _ hcS, hout, List.length_replicate,
    rewind_run m _ _ _ _ _ (w.drop tS) (by simp only [List.length_drop, hw]; omega),
    moveInputPos_inLeft cS.inputPos (by have := cS.inputPos.isLt; omega)]
  exact (runCfg_initCfg (S := S) (A := A) m 0 cS.workTapes cS.workTapePos).symm

''';ccand=cbase[:a]+new+cbase[b:];(W/consumer).write_text(ccand)
for path,base,cand in [(owner,obase,ocand),(consumer,cbase,ccand)]:
 for side,text in [('BASE-f3',base),('CANDIDATE',cand)]:
  p=E/'source'/side/(path+'.txt');p.parent.mkdir(parents=True,exist_ok=True);p.write_text(text)
(E/'proposed-readers.lean.txt').write_text(boot+'\n'+run);(E/'proposed-boot-reader.lean.txt').write_text(boot);(E/'proposed-run-reader.lean.txt').write_text(run);(E/'startup-target-BASE.lean.txt').write_text(old);(E/'startup-target-CANDIDATE.lean.txt').write_text(new)
api=''.join(difflib.unified_diff(obase.splitlines(keepends=True),ocand.splitlines(keepends=True),fromfile='a/'+owner,tofile='b/'+owner));cons=''.join(difflib.unified_diff(cbase.splitlines(keepends=True),ccand.splitlines(keepends=True),fromfile='a/'+consumer,tofile='b/'+consumer));(E/'API-only.patch').write_text(api);(E/'consumer-only.patch').write_text(cons);(E/'combined-proposal.patch').write_text(api+cons)
subprocess.run(['cp','-cR',str(S/'oleans-mac8'),str(OV)],check=True)
def objects(root):return {str(p.relative_to(root)):H(p.read_bytes()) for p in sorted((root/'TCSlib').rglob('*.olean'))}
a=objects(S/'oleans-mac8');b=objects(OV);assert len(a)==895 and a==b==json.loads((R/'campaign/status/2026-11-08-mig1-merge/object-hashes.json').read_text())
save('INPUT895-original.json',a);save('INPUT895-clone-before.json',b);save('SOURCE1003-f3.json',inventory);save('SOURCE-BINDING.json',{'source_HEAD':HEAD,'snapshot_BASE':BASE,'producer':owner,'consumer':consumer,'proposed_readers':['Turing.ClockHost.bootCfg_of_halt','Turing.ClockHost.runCfg_initCfg'],'public_API_hypothesis_only':True,'non_simp':True,'existing_definitions_imports_headers_attributes_all_source_preserved':True,'producer_all_other_source_exact_f3':True,'consumer_original_doc_header_and_all_other_source_exact':True,'consumer_complete_source_BASE9b5_f3_exact_before_repair':True,'producer_complete_source_BASE9b5_f3_exact_before_repair':True,'original_producer_sha256':H(obase.encode()),'candidate_producer_sha256':H(ocand.encode()),'original_consumer_sha256':H(cbase.encode()),'candidate_consumer_sha256':H(ccand.encode()),'target_old_sha256':H(old.encode()),'target_new_sha256':H(new.encode()),'no_gate129_or_core_proposal_dependency':True,'one_own_job_at_a_time':True,'localcap':3,'machinecap':5})
print('Prepared two minimal ND configuration-reader hypotheses and complete startup candidate over exactBASE/f3 and wholeMAC8; no source/Git writes.')
