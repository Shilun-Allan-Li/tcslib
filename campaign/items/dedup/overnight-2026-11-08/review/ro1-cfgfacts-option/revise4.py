from pathlib import Path
import json
O=Path('/private/tmp/ab34-ro1-integration');W=Path('/Users/seyoonr/.codex/worktrees/ab34-sg1/tcslib-arora-barak-ch3-4');p='TCSlib/Complexity/TuringMachine/Build/Primitives.lean';s=(W/p).read_text()
old="    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_one]\n    rw [hs, MultiTapeTM.step_of_some rfl]"
new="    simp only [List.length_nil, Nat.mul_zero, zero_add]\n    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_one]\n    rw [hs, MultiTapeTM.step_of_some rfl]"
assert s.count(old)==1
R=O/'revision4';R.mkdir();(R/'Primitives.before.lean.txt').write_text(s);s=s.replace(old,new);(R/'Primitives.after.lean.txt').write_text(s);(W/p).write_text(s)
(R/'edits.json').write_text(json.dumps([{'path':p,'kind':'normalize original length expression before canonical inner one-step','before':old,'after':new}],indent=2)+'\n')
