from pathlib import Path
import os,subprocess,tarfile,io,json,hashlib,difflib
O=Path(__file__).parent;E=O/'evidence';R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');S=Path(os.environ['TCSLIB_SCRATCH']);P=Path('/private/tmp/ab34-scan-bwd-reader-proposal/evidence');BASE='9b5dcf46408db681bcbc721930ef2203fa6bc47d';D64='d64dff4fbef865d815c6a561ce8037ea1bae07a2';env=os.environ|{'GIT_OPTIONAL_LOCKS':'0'};W=O/'runtime/project';OV=O/'runtime/oleans-proposal';W.mkdir(parents=True)
H=lambda b:hashlib.sha256(b).hexdigest()
def git(*args):return subprocess.check_output(['git','-C',str(R),*args],env=env)
def save(n,a):(E/n).write_text(json.dumps(a,ensure_ascii=False,indent=2)+'\n')
paths=[p for p in git('ls-tree','-r','--name-only',BASE).decode().splitlines() if p.endswith('.lean')];assert len(paths)==1003
archive=git('archive',BASE,*paths,'lean-toolchain','lake-manifest.json');rows=[]
with tarfile.open(fileobj=io.BytesIO(archive)) as tar:
 for m in tar.getmembers():
  path=Path(m.name);assert not path.is_absolute() and '..' not in path.parts
  if m.isdir():continue
  assert m.isfile();data=tar.extractfile(m).read();p=W/path;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data);rows.append({'path':m.name,'bytes':len(data),'sha256':H(data)})
(W/'.lake').mkdir();(W/'.lake/packages').symlink_to(R/'.lake/packages',target_is_directory=True);(E/'helpers').mkdir()
for name in ['leanelab.sh','leanelab-o.sh']:(E/'helpers'/name).write_bytes((R/'devtools/seyoon'/name).read_bytes())
for name in ['lean-toolchain','lake-manifest.json']:(E/'helpers'/name).write_bytes((W/name).read_bytes())
oldrun=(P/'tools/run_one.py').read_text();assert 'O=Path(__file__).parent' in oldrun
(O/'run_one.py').write_text(oldrun.replace('whole complete895 MAC8 clone with only executed Scan reader compilation when applicable','whole complete895 MAC8 clone with sequential hypothetical Simulation/Catalog/Scan reader compilations, no snapshot composition'))
sim='TCSlib/Complexity/TuringMachine/Simulation.lean';cat='TCSlib/Complexity/TuringMachine/Build/Catalog.lean';scan='TCSlib/Complexity/TuringMachine/Build/Scan.lean';inp='TCSlib/Complexity/TuringMachine/Build/InputLength.lean'
control=r'''/-- A control action has the requested input movement and successor state,
with no work-tape writes or head movement and no output symbol. -/
theorem controlAction_eq {k : ℕ} {S : Type} (m : SignType) (q : Option S) :
    controlAction (k := k) m q =
      (⟨m, fun _ => (none, 0), none, q⟩ : Action k Bool S) := by
  rfl
'''
move=r'''/-- An input-only action has the requested input movement and live successor,
with no work-tape writes or head movement and no output symbol. -/
theorem inputMoveAction_eq {k : ℕ} {Symbol State : Type*} (inp : SignType) (q : State) :
    inputMoveAction (k := k) (Symbol := Symbol) inp q =
      (⟨inp, fun _ => (none, 0), none, some q⟩ : Action k Symbol State) := by
  rfl
'''
markers={sim:'/-- Read position `i + 1` as the optional `i`-th input symbol, including the',cat:'/-- **One step of a non-writing one-tape action**'}
lemmas={sim:control,cat:move};changed=[]
for path in [sim,cat,scan,inp]:
 base=(W/path).read_text();assert git('show',D64+':'+path).decode()==base
 if path in lemmas:
  marker=markers[path];assert base.count(marker)==1;cand=base.replace(marker,lemmas[path]+'\n'+marker)
 elif path==scan:cand=(P/'source/CANDIDATE'/(path+'.txt')).read_text()
 else:
  cand=(P/'source/CANDIDATE'/(path+'.txt')).read_text();old='      cases inp <;> rfl) back rfl';new='''      cases inp <;> rw [inputMoveAction_eq, FinTM.controlAction_eq]
      all_goals
        apply Action.ext <;>
          simp only [Action.mapState_inputTape, Action.mapState_workTapes,
            Action.mapState_output, Action.mapState_state, Option.map_some]) back rfl''';assert cand.count(old)==1;cand=cand.replace(old,new)
 (W/path).write_text(cand)
 for side,text in [('BASE',base),('CANDIDATE',cand)]:
  p=E/'source'/side/(path+'.txt');p.parent.mkdir(parents=True,exist_ok=True);p.write_text(text)
 changed.append({'path':path,'BASE_sha256':H(base.encode()),'candidate_sha256':H(cand.encode())})
(E/'proposed-controlAction_eq.lean.txt').write_text(control);(E/'proposed-inputMoveAction_eq.lean.txt').write_text(move);(E/'proposed-inputFoldTM_tr_bwd.lean.txt').write_bytes((P/'proposed-public-reader.lean.txt').read_bytes())
(E/'proposal.patch').write_text(''.join(''.join(difflib.unified_diff((E/'source/BASE'/(p+'.txt')).read_text().splitlines(keepends=True),(E/'source/CANDIDATE'/(p+'.txt')).read_text().splitlines(keepends=True),fromfile='a/'+p,tofile='b/'+p)) for p in [sim,cat,scan,inp]))
heads=json.loads((P/'PREPARATION.json').read_text())['InputLength_full_target_guard_heads'];candidate=(W/inp).read_text();doc=candidate.rfind('/--',0,candidate.index('theorem exists_inputLengthTM :'));end=candidate.rindex('\nend Turing');guard=candidate[:doc]+'section InputLengthThreeReaderBoundary\nattribute [local irreducible] '+' '.join(heads)+'\n\n'+candidate[doc:end]+'\nend InputLengthThreeReaderBoundary\n'+candidate[end:];(W/'InputLengthSealed.lean').write_text(guard);(E/'InputLength-full-target-sealed.lean.txt').write_text(guard)
(W/'VisibilityProbe.lean').write_text('''import Lean
import TCSlib.Complexity.TuringMachine.Build.CounterLoop
open Lean Elab Command in
run_cmd do
  let e ← getEnv
  for n in [`Turing.Action.ext, `Turing.Action.eta, `Turing.Action.mapState_inputTape,
      `Turing.Action.mapState_workTapes, `Turing.Action.mapState_output,
      `Turing.Action.mapState_state] do
    logInfo m!"VISIBLE|{n}|{e.contains n}"
''')
subprocess.run(['cp','-cR',str(S/'oleans-mac8'),str(OV)],check=True)
def objects(root):return {str(p.relative_to(root)):H(p.read_bytes()) for p in sorted((root/'TCSlib').rglob('*.olean'))}
a=objects(S/'oleans-mac8');b=objects(OV);assert a==b==json.loads((R/'campaign/status/2026-11-08-mig1-merge/object-hashes.json').read_text()) and len(a)==895
save('INPUT895-original.json',a);save('INPUT895-clone-before.json',b);save('SOURCE1003-BASE.json',rows);save('SOURCE-BINDING.json',{'BASE':BASE,'D64':D64,'all_four_BASE_owners_equal_both_pins':True,'candidates':changed,'new_public_readers_hypothetical_only':['Turing.FinTM.controlAction_eq','Turing.inputMoveAction_eq','Turing.inputFoldTM_tr_bwd'],'all_three_non_simp':True,'no_existing_def_import_header_change':True,'consumer_full_guard_heads':heads,'previous_single_reader_manifest_sha256':H((P/'MANIFEST.json').read_bytes()),'runtime_base_whole_objects':895,'one_own_job_at_a_time':True,'localcap':3,'machinecap':5})
print('Prepared complete private four-owner3-reader candidate and fresh wholeMAC8 clone; no source/Git writes.')
