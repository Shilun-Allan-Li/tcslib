"""Insert exactly the approved source theorem; preserve every pre-existing byte."""
from pathlib import Path
import json,hashlib,difflib,subprocess,os,datetime
out=Path(__file__).resolve().parent;root=out.parents[4];wt=Path('/Users/seyoonr/.codex/worktrees/ab34-followup-api/tcslib-arora-barak-ch3-4');source=wt/'TCSlib/Complexity/TuringMachine/Finite.lean';proposal=root/'campaign/fills/mig1/review/first-entry-proposal/Proposed-contract.lean.txt';before=source.read_bytes();approved=proposal.read_bytes();assert b'exists_first_entry_of_fixed' not in before
assert before==subprocess.run(['git','-C',str(wt),'show','HEAD:TCSlib/Complexity/TuringMachine/Finite.lean'],stdout=subprocess.PIPE,check=True,env=dict(os.environ,GIT_OPTIONAL_LOCKS='0')).stdout
head=subprocess.run(['git','-C',str(wt),'rev-parse','HEAD'],stdout=subprocess.PIPE,check=True,env=dict(os.environ,GIT_OPTIONAL_LOCKS='0')).stdout.decode().strip();assert head=='1160c18f03fd318f0dec25738790935fa61379d4';subprocess.run(['git','-C',str(wt),'cat-file','-e',head+'^{commit}'],check=True)
doc=b'''/-- A run ending in a designated live stop state first enters the stop states by its deadline,
and that first entry is already the final configuration, provided every stop configuration is
fixed by one step.

**Proof sketch.** Choose the least stop-state time with `Nat.find`. Minimality gives the
strict earlier-time cut. The fixed-step hypothesis keeps every subsequent configuration equal
to that first entry; `runFrom_add` then identifies it with the given final configuration. -/
'''
insert=doc+approved.rstrip()+b'\n\n';marker=b'/-- **A new initial state changes no run**';pos=before.index(marker);assert before.index(b'theorem exists_first_halt')<pos
current=before[:pos]+insert+before[pos:];assert current.replace(insert,b'',1)==before;source.write_bytes(current);assert source.read_bytes()==current
(out/'before-Finite.lean.txt').write_bytes(before);(out/'actual-Finite.lean.txt').write_bytes(current);(out/'inserted-approved-theorem.lean.txt').write_bytes(insert);(out/'approved-contract.lean.txt').write_bytes(approved)
(out/'source.patch').write_text(''.join(difflib.unified_diff(before.decode().splitlines(keepends=True),current.decode().splitlines(keepends=True),fromfile='a/TCSlib/Complexity/TuringMachine/Finite.lean',tofile='b/TCSlib/Complexity/TuringMachine/Finite.lean')))
H=lambda b:hashlib.sha256(b).hexdigest();(out/'source-receipt.json').write_text(json.dumps({'at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source':str(source),'worktree':str(wt),'base_commit_verified':head,'before_sha256':H(before),'after_sha256':H(current),'approved_proposal_sha256':H(approved),'approved_header_and_proof_exact_bytes':True,'all_old_bytes_restored_by_removing_only_insert':True,'insert_before_old_line':before[:pos].count(b'\n')+1,'first_new_doc_line':current[:pos].count(b'\n')+1,'first_new_theorem_line':current[:pos+len(doc)].count(b'\n')+1,'new_public_theorem':'Turing.MultiTapeTM.exists_first_entry_of_fixed','no_other_source_file_owned_or_edited':True},indent=2)+'\n');print((out/'source-receipt.json').read_text())
