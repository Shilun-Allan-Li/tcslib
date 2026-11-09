from pathlib import Path
import json
O=Path('/private/tmp/ab34-ro1-integration');W=Path('/Users/seyoonr/.codex/worktrees/ab34-sg1/tcslib-arora-barak-ch3-4');R=O/'revision6';R.mkdir();rows=[]
for rel,n in [('ClassNP/SAT',2),('CookLevin/Hardness',1),('ClassP/Examples',1)]:
 p='TCSlib/Complexity/'+rel+'.lean';s=(W/p).read_text();old='simp only [MultiTapeTM.runFrom_one]';assert s.count(old)==n,(p,s.count(old))
 new='simp only [Nat.zero_add, MultiTapeTM.runFrom_one]' if rel=='ClassP/Examples' else 'rw [MultiTapeTM.runFrom_one]'
 before=R/'before'/(p+'.txt');before.parent.mkdir(parents=True,exist_ok=True);before.write_text(s);s=s.replace(old,new)
 after=R/'after'/(p+'.txt');after.parent.mkdir(parents=True,exist_ok=True);after.write_text(s);(W/p).write_text(s)
 rows.append({'path':p,'sites':n,'before':old,'after':new,'reason':'literal-one reader after zero-plus-one normalization, no statement change'})
(R/'edits.json').write_text(json.dumps(rows,indent=2)+'\n')
