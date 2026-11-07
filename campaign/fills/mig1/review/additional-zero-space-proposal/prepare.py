"""Prepare exactly two unapproved zero-space facts and bounded probes."""
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import sys
sys.dont_write_bytecode=True
OUT=Path(__file__).resolve().parent;ROOT=OUT.parents[4]
WT=Path(os.environ['TCSLIB_SCRATCH'])/'wt-natbits';SNAP=Path(os.environ['TCSLIB_SCRATCH'])/'oleans-mac3'
spec=importlib.util.spec_from_file_location('decls',OUT.parent/'checkpoint05-2026-11-07/compare.py')
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
SEAL='attribute [local irreducible] Turing.MultiTapeTM.spaceUsed Turing.MultiTapeTM.initCfg\nattribute [-simp] Turing.MultiTapeTM.initCfg\n'
def save(n,s):
    p=OUT/n;assert not p.exists(),p;p.write_text(s)
facts={}
rhs={}
sources={}
for home,short,qualified,ending in [
    ('Encoding','pairDiagTM','Turing.pairDiagTM','end Turing\n'),
    ('Build/Primitives','incFixedTM','Turing.FinTM.incFixedTM','end FinTM\nend Turing\n')]:
    f='TCSlib/Complexity/TuringMachine/'+home+'.lean';t=(WT/f).read_text();sources[f]=hashlib.sha256(t.encode()).hexdigest()
    d=next(d for d in m.decls(t) if d['name']==qualified)
    last=d['start']-1+max(i+1 for i,l in enumerate(d['code'].splitlines()) if l.strip())
    prefix='\n'.join(t.splitlines()[:last])+'\n'
    theorem=f'''theorem {short}_spaceUsed (x : List Bool) (t : ℕ) :
    {short}.tm.spaceUsed ({short}.tm.initCfg x) t = 0 := by
  exact MultiTapeTM.spaceUsed_zero_tapes_eq_zero _ _ rfl
'''
    facts[qualified]=theorem
    save(home.replace('/','-')+'-home.lean.txt',prefix+'\nsection ProposedZeroSpace\n'+SEAL+theorem+'\nend ProposedZeroSpace\n'+ending+'\n#print axioms '+qualified+'_spaceUsed\n')
    body='\n'.join(t.splitlines()[d['start']-1:last]).split('where\n',1)[1]
    rhs[short]='{\n'+body+'\n}'
availability='''import TCSlib.Complexity.TuringMachine.Build.Primitives
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let roots := ["Turing.pairDiagTM", "Turing.FinTM.incFixedTM"]
  for (name, info) in env.constants.toList do
    if roots.any (fun root => name.toString.startsWith root) then
      logInfo m!"{name} : {info.type}"
  for wanted in ["Turing.pairDiagTM_spaceUsed", "Turing.FinTM.incFixedTM_spaceUsed"] do
    if env.constants.toList.any (fun item => item.1.toString = wanted) then
      logInfo m!"REQUESTED {wanted}: PRESENT"
    else
      logInfo m!"REQUESTED {wanted}: ABSENT"
#check Turing.MultiTapeTM.spaceUsed_zero_tapes_eq_zero
'''
save('Availability.lean.txt',availability)
consumers='''import TCSlib.Complexity.TuringMachine.Build.Primitives
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Turing Turing.FinTM
attribute [local irreducible] Turing.pairDiagTM Turing.FinTM.incFixedTM
'''+SEAL+'''
namespace AdditionalZeroSpaceConsumers
-- Exact proposed interfaces are parameters here; owner proofs are tested separately.
theorem pairDup_constant_space
    (pairDiagTM_spaceUsed : ∀ x t, pairDiagTM.tm.spaceUsed (pairDiagTM.tm.initCfg x) t = 0)
    (x : List Bool) (t bound : ℕ) :
    pairDiagTM.tm.spaceUsed (pairDiagTM.tm.initCfg x) t ≤ bound := by
  rw [pairDiagTM_spaceUsed]
  exact Nat.zero_le _
theorem incFixed_constant_space
    (incFixedTM_spaceUsed : ∀ x t, incFixedTM.tm.spaceUsed (incFixedTM.tm.initCfg x) t = 0)
    (x : List Bool) (t bound : ℕ) :
    incFixedTM.tm.spaceUsed (incFixedTM.tm.initCfg x) t ≤ bound := by
  rw [incFixedTM_spaceUsed]
  exact Nat.zero_le _
end AdditionalZeroSpaceConsumers
#print axioms AdditionalZeroSpaceConsumers.pairDup_constant_space
#print axioms AdditionalZeroSpaceConsumers.incFixed_constant_space
'''
save('Consumers.lean.txt',consumers)
controls='''import TCSlib.Complexity.TuringMachine.Build.Primitives
open Turing Turing.FinTM
example : pairDiagTM.k = 0 := by rfl
example : pairDiagTM = '''+rhs['pairDiagTM']+''' := by rfl
example : incFixedTM.k = 0 := by rfl
example : incFixedTM = '''+rhs['incFixedTM']+''' := by rfl
example (tm : MultiTapeTM 1 Bool Unit) (c : Cfg 1 Bool Unit ([] : List Bool)) (t : ℕ) :
    tm.spaceUsed c t = ∑ i, tm.spaceUsedByTape c t i := by rfl
example : (fun (tm : MultiTapeTM 1 Bool Unit) (c : Cfg 1 Bool Unit ([] : List Bool)) (t : ℕ) =>
    tm.spaceUsed c t) = fun tm c t => ∑ i, tm.spaceUsedByTape c t i := by rfl
example (tm : MultiTapeTM 1 Bool Unit) (x : List Bool) :
    tm.initCfg x = Cfg.init tm.q₀ x := by rfl
example : (fun (tm : MultiTapeTM 1 Bool Unit) (x : List Bool) => tm.initCfg x) =
    fun tm x => Cfg.init tm.q₀ x := by rfl
'''
save('Controls-unsealed.lean.txt',controls)
save('Controls-sealed.lean.txt',controls.replace('open Turing Turing.FinTM\n','open Turing Turing.FinTM\nattribute [local irreducible] Turing.pairDiagTM Turing.FinTM.incFixedTM\n'+SEAL,1))
context=dict(unapproved=True,api_worktree=str(WT),api_head_identified_by_maintainer='1160c18f03fd318f0dec25738790935fa61379d4',
             snapshot=str(SNAP),adoption=json.loads((ROOT/'campaign/status/2026-11-07-linear-merge/receipt.json').read_text()),
             source_sha256=sources,compiled_sha256={f:hashlib.sha256((SNAP/(f.removesuffix('.lean')+'.olean')).read_bytes()).hexdigest() for f in sources},
             machine_names=list(facts),proposed_names=[n+'_spaceUsed' for n in facts],new_imports=[],consumer_limit='Hypothetical interface parameters, not new library constants.')
save('context.json',json.dumps(context,indent=2)+'\n')
print('Prepared exact Encoding/Primitives owner prefixes, availability, two interface consumers and8 controls.')
