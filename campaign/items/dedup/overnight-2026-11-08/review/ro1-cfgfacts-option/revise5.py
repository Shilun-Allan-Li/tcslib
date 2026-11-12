from pathlib import Path
O=Path('/private/tmp/ab34-ro1-integration');W=Path('/Users/seyoonr/.codex/worktrees/ab34-sg1/tcslib-arora-barak-ch3-4');p='TCSlib/Complexity/ClassNP/Nondeterminism.lean';s=(W/p).read_text();old='  simp only [MultiTapeTM.runFrom_one]';new="  rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_one]";assert s.count(old)==2
R=O/'revision5';R.mkdir();(R/'Nondeterminism.before.lean.txt').write_text(s);s=s.replace(old,new);(R/'Nondeterminism.after.lean.txt').write_text(s);(W/p).write_text(s)
(R/'reason.txt').write_text('Two run-time-2 contracts retain the outer successor equation and consume the canonical one-step inner reader. Original headers and all data definitions unchanged.\n')
