from pathlib import Path
import re,json
O=Path('/private/tmp/ab34-ro1-integration');W=Path('/Users/seyoonr/.codex/worktrees/ab34-sg1/tcslib-arora-barak-ch3-4')
changes={};rows=[]
def record(p,s,note):
    old=changes.get(p,(W/p).read_text())
    if old!=s:rows.append({'path':p,'kind':note,'before_sha256_source_preserved':True});changes[p]=s
p='TCSlib/Complexity/TuringMachine/Build/Primitives.lean';s=(W/p).read_text()
# Original simp closed every numeric time. Retain the outer two-step reader and
# cite the generic one-step equation for the inner run, rather than treating a
# raw simp-equation pair as a literal-one proof.
for name in ['fwdMap_block','fwdMap_emit','fwdMap_parse']:
    m=re.search(r'^private lemma '+name+r'\b',s,re.M);assert m
    n=re.search(r'^private (?:lemma|theorem|def)\b',s[m.end():],re.M)
    end=m.end()+n.start() if n else len(s);chunk=s[m.start():end]
    if name=='fwdMap_block':
        assert chunk.count('simp only [MultiTapeTM.runFrom_one]')==1
        chunk=chunk.replace('simp only [MultiTapeTM.runFrom_one]',"rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_one]")
    elif name=='fwdMap_emit':
        chunk,count=re.subn(r'(\s*)simp only \[List.length_nil, Nat.mul_zero, zero_add,\s*MultiTapeTM.runFrom_one\]',
            lambda z:z[1]+'rw [MultiTapeTM.runFrom_succ_eq_step\x27, MultiTapeTM.runFrom_one]',chunk)
        assert count==2,count
    else:
        old='refine ⟨2, by simp only [List.length_cons, List.length_nil]; omega, ?_⟩\n        simp only [MultiTapeTM.runFrom_one]'
        assert chunk.count(old)==1
        chunk=chunk.replace(old,'refine ⟨2, by simp only [List.length_cons, List.length_nil]; omega, ?_⟩\n        rw [MultiTapeTM.runFrom_succ_eq_step\x27, MultiTapeTM.runFrom_one]')
    s=s[:m.start()]+chunk+s[end:]
record(p,s,'numeric-time simp closure: keep outer successor reader, canonical inner one-step')
for p in [str(p.relative_to(W)) for p in (W/'TCSlib').rglob('*.lean')]:
    s=changes.get(p,(W/p).read_text())
    def normalize(m):
        z=m.group()
        if 'MultiTapeTM.runFrom_one' in z and 'List.length_nil' in z and 'Nat.zero_add' not in z and 'zero_add' not in z:
            return z.replace('List.length_nil','List.length_nil, Nat.zero_add')
        return z
    s=re.sub(r'simp only \[[^\]]*\]',normalize,s)
    s=s.replace('simp only [clCountCarry, MultiTapeTM.runFrom_one, clCount_carry_step]',
                'simp only [clCountCarry, Nat.zero_add, MultiTapeTM.runFrom_one, clCount_carry_step]')
    record(p,s,'normalize zero-plus-one before simplifier matches literal-one reader')
R=O/'revision3';assert not R.exists();R.mkdir()
for p,s in changes.items():
    a=R/'before'/(p+'.txt');a.parent.mkdir(parents=True,exist_ok=True);a.write_text((W/p).read_text())
    a=R/'after'/(p+'.txt');a.parent.mkdir(parents=True,exist_ok=True);a.write_text(s)
for p,s in changes.items():(W/p).write_text(s)
(R/'edits.json').write_text(json.dumps(rows,indent=2)+'\n');print('revision3 owners',len(changes))
