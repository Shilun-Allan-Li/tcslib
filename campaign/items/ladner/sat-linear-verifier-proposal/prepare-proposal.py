from pathlib import Path
import subprocess,hashlib,json,os
r=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');out=Path('/private/tmp/ab34-ladner-sat-reader-proposal');out.mkdir();w=out/'project';(w/'.lake').mkdir(parents=True);(w/'.lake/packages').symlink_to(Path(os.environ['TCSLIB_REPO'])/'.lake/packages',target_is_directory=True)
base=subprocess.check_output(['git','-C',str(r),'rev-parse','9b5dcf464']).decode().strip();subprocess.run(['git','-C',str(r),'cat-file','-e',base+'^{commit}'],check=True)
p='TCSlib/Complexity/ClassNP/SAT.lean';s=subprocess.check_output(['git','-C',str(r),'show',base+':'+p]).decode()
anchor='''theorem SAT_mem_NP : SAT ∈ NP := by
  refine ⟨1, 1, satVerifier false, satVerifier_of_poly false satVerdict_false_poly, ?_⟩
  intro x
  simpa only [Nat.pow_one, Nat.one_mul] using sat_verifier_equiv x
'''
assert s.count(anchor)==1
addition='''
/-- SAT has a polynomial-time verifier whose certificate has exactly one more bit
than the instance. This records the explicit certificate size of `SAT_mem_NP`.
[AB09, §2.1] -/
theorem SAT_exists_linear_verifier :
    ∃ V : Language Bool, V ∈ P ∧
      ∀ x : List Bool, x ∈ SAT ↔
        ∃ u : List Bool, u.length = x.length + 1 ∧ x ++ u ∈ V := by
  exact ⟨satVerifier false, satVerifier_of_poly false satVerdict_false_poly,
    sat_verifier_equiv⟩
'''
new=s.replace(anchor,anchor+addition)
(out/'BASE-SAT.lean.txt').write_text(s);(out/'hypothetical-SAT.lean.txt').write_text(new);(out/'proposed-reader.lean.txt').write_text(addition)
(w/p).parent.mkdir(parents=True);(w/p).write_text(new+'\n#print axioms Complexity.SAT_exists_linear_verifier\n')
for f in ['lean-toolchain','lake-manifest.json','lakefile.toml']:
 if (r/f).exists():(w/f).write_bytes((r/f).read_bytes())
(out/'request.json').write_text(json.dumps({'status':'HYPOTHETICAL UNAPPROVED PUBLIC API; no source changes','base':base,'source_path':p,'name':'Complexity.SAT_exists_linear_verifier','source_sha256':hashlib.sha256(new.encode()).hexdigest(),'exact_existing_witness':'satVerifier false','existing_proofs':['satVerifier_of_poly false satVerdict_false_poly','sat_verifier_equiv'],'imports_unchanged':True,'placement':'immediately after SAT_mem_NP','no_machine_or_statement_changes':True},indent=2)+'\n')
import difflib
(out/'proposed-reader.patch').write_text(''.join(difflib.unified_diff(s.splitlines(True),new.splitlines(True),fromfile='a/'+p,tofile='b/'+p)))
print(out)
