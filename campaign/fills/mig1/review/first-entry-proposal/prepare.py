"""Prepare bounded unapproved probes; no repository source or compiled tree changes."""
import hashlib
import json
import os
from pathlib import Path

OUT=Path(__file__).resolve().parent
ROOT=OUT.parents[4]
WT=Path(os.environ['TCSLIB_SCRATCH'])/'wt-natbits'
SNAP=Path(os.environ['TCSLIB_SCRATCH'])/'oleans-mac3'
SEAL='attribute [local irreducible] Turing.MultiTapeTM.runFrom Turing.MultiTapeTM.step\n'
THEOREM='''theorem exists_first_entry_of_fixed {k : ℕ} {Symbol State : Type*}
    {input : List Symbol} (tm : MultiTapeTM k Symbol State)
    (stop : State → Prop) (c d : Cfg k Symbol State input) (T : ℕ)
    (hfix : ∀ z : Cfg k Symbol State input,
      (∃ q, z.state = some q ∧ stop q) → tm.step z = z)
    (hd : ∃ q, d.state = some q ∧ stop q) (hT : tm.runFrom c T = d) :
    ∃ t ≤ T, (∀ j < t, ¬∃ q, (tm.runFrom c j).state = some q ∧ stop q) ∧
      tm.runFrom c t = d := by
  classical
  have hh : ∃ t, ∃ q, (tm.runFrom c t).state = some q ∧ stop q :=
    ⟨T, by rw [hT]; exact hd⟩
  let t := Nat.find hh
  have ht : t ≤ T := Nat.find_min' hh (by rw [hT]; exact hd)
  have hs : ∃ q, (tm.runFrom c t).state = some q ∧ stop q := Nat.find_spec hh
  have hfixed : tm.step (tm.runFrom c t) = tm.runFrom c t := hfix _ hs
  have hconst (n : ℕ) : tm.runFrom (tm.runFrom c t) n = tm.runFrom c t := by
    induction n with
    | zero => exact runFrom_zero
    | succ n ih => rw [runFrom_succ_eq_step, hfixed]; exact ih
  refine ⟨t, ht, fun j hj => Nat.find_min hh hj, ?_⟩
  have he := tm.runFrom_add c t (T - t)
  rw [Nat.add_sub_of_le ht, hT, hconst] at he
  exact he.symm
'''

def save(name,text):
    p=OUT/name
    assert not p.exists(),p
    p.write_text(text)

owner=(WT/'TCSlib/Complexity/TuringMachine/Finite.lean').read_text()
imports='\n'.join(l for l in owner.splitlines() if l.startswith('import '))+'\n'
prefix=owner[:owner.index('/-- **A new initial state changes no run**')]
home=prefix+'\nsection FirstEntryProposalSeal\n'+SEAL+THEOREM+'\nend FirstEntryProposalSeal\nend MultiTapeTM\nend Turing\n\n#print axioms Turing.MultiTapeTM.exists_first_entry_of_fixed\n'
save('Owner-home-v1.lean.txt',home)
save('Proposed-contract.lean.txt',THEOREM)
files=['TCSlib/Complexity/TuringMachine/Finite.lean',
       'TCSlib/Complexity/TuringMachine/Deterministic.lean',
       'TCSlib/Complexity/TuringMachine/Build/Loop.lean',
       'TCSlib/Complexity/TuringMachine/Build/Primitives.lean']
context=dict(unapproved=True,pre_shipped=False,
             api_worktree=str(WT),api_head_identified_by_maintainer='1160c18f03fd318f0dec25738790935fa61379d4',
             git_not_invoked=True,snapshot=str(SNAP),
             adoption_receipt='campaign/status/2026-11-07-linear-merge/receipt.json',
             snapshot_adoption=json.loads((ROOT/'campaign/status/2026-11-07-linear-merge/receipt.json').read_text()),
             owner_imports=imports.splitlines(),
             source_sha256={f:hashlib.sha256((WT/f).read_bytes()).hexdigest() for f in files},
             compiled_sha256={f:hashlib.sha256((SNAP/(f.removesuffix('.lean')+'.olean')).read_bytes()).hexdigest() for f in files},
             toolchain=(WT/'lean-toolchain').read_text().strip(),
             local_lean_slots=os.environ.get('TCSLIB_LEAN_SLOTS'))
save('context.json',json.dumps(context,indent=2)+'\n')
print('Prepared owner proof and context; review archived source before running.')
