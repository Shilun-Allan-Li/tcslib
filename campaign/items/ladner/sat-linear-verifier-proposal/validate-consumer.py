from pathlib import Path
import os,subprocess,json,time,hashlib,shutil
out=Path('/private/tmp/ab34-ladner-sat-reader-proposal');w=out/'project';s=Path(os.environ['TCSLIB_SCRATCH']);overlay=out/'whole-hypothetical-overlay';inp=s/'oleans-mac8';helper=Path('/Users/seyoonr/.codex/worktrees/ab34-followup-api/tcslib-arora-barak-ch3-4/devtools/seyoon')
def objects(p):return {str(f.relative_to(p)):hashlib.sha256(f.read_bytes()).hexdigest() for f in sorted(p.rglob('*.olean'))}
before=objects(inp);assert len(before)==895;(out/'input-895.json').write_text(json.dumps(before,indent=2)+'\n');assert not overlay.exists();subprocess.run(['cp','-cR',str(inp),str(overlay)],check=True);assert objects(overlay)==before
for ext in ['.olean','.ilean','.c','.trace']:(overlay/('TCSlib/Complexity/ClassNP/SAT'+ext)).unlink(missing_ok=True)
def run(name,cmd):
 t=time.monotonic()
 with (out/(name+'.log')).open('wb') as f:r=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT)
 b=(out/(name+'.log')).read_bytes();v={'command':cmd,'exit':r.returncode,'errors':b.count(b'error:'),'sorry':b.count(b"declaration uses 'sorry'"),'seconds':time.monotonic()-t,'log_sha256':hashlib.sha256(b).hexdigest()};v['pass']=v['exit']==0 and v['errors']==0 and v['sorry']==0;(out/(name+'.json')).write_text(json.dumps(v,indent=2)+'\n');print(name,v['pass'],flush=True);assert v['pass']
run('compiled-owner',['bash',str(helper/'leanelab-o.sh'),str(w),str(overlay),'TCSlib/Complexity/ClassNP/SAT.lean',str(overlay)])
source=Path('/private/tmp/ab34-ladner-readers-v2/Conditional-linear-SAT-search.lean.txt').read_text();pre=source[:source.index('-- Conditional sharp-SAT consumer only.')]
consumer=pre+'''-- Hypothetical named owner-reader consumed through the existing sharp search host.
example : ∃ (a d b : ℕ) (E : FinTM Bool), E.DecidesInTime SAT
    (fun n => b * 2 ^ (n + 1) *
      (a * (n + (n + 1) + 1) ^ d + (n + (n + 1) + 1) ^ 2)) := by
  obtain ⟨V, hV, hcert⟩ := SAT_exists_linear_verifier
  obtain ⟨a, d, MV, hMV⟩ := mem_P_iff.mp hV
  obtain ⟨b, E, hE⟩ := exists_proj_decider 1 1 V _ MV hMV
  simp only [Nat.pow_one, Nat.one_mul] at hE
  have hLang : {x : List Bool | ∃ u : List Bool,
      u.length = x.length + 1 ∧ x ++ u ∈ V} = SAT :=
    Set.ext fun x => (hcert x).symm
  rw [hLang] at hE
  exact ⟨a, d, b, E, hE⟩

#print axioms Complexity.SAT_exists_linear_verifier
'''
(w/'Consumer.lean').write_text(consumer);(out/'Consumer.lean.txt').write_text(consumer)
run('actual-named-consumer',['bash',str(helper/'leanelab.sh'),str(w),str(overlay),'Consumer.lean'])
assert objects(inp)==before;after=objects(overlay);assert set(after)==set(before);changed=[p for p in before if before[p]!=after[p]];assert changed==['TCSlib/Complexity/ClassNP/SAT.olean'];(out/'overlay-accounting.json').write_text(json.dumps({'input_unchanged':True,'objects':895,'changed':changed,'scope':'whole895 clone; hypotheticalSAT owner compiled, consumer native; NOT downstream replay or approvedsnapshot'},indent=2)+'\n')
print('COMPLETE proposed SAT reader and actual named consumer PASS',flush=True)
