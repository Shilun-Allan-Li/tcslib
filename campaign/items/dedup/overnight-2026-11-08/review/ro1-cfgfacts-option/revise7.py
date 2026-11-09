from pathlib import Path
import json,re
O=Path('/private/tmp/ab34-ro1-integration');W=Path('/Users/seyoonr/.codex/worktrees/ab34-sg1/tcslib-arora-barak-ch3-4');changes={};rows=[];missing=[]
def exact(rel,old,new,n=1):
 p='TCSlib/Complexity/'+rel+'.lean';s=changes.get(p,(W/p).read_text())
 if s.count(old)!=n:missing.append((p,old,s.count(old),n));return
 rows.append({'path':p,'kind':'explicit canonical reader replaces an implicit step/run-one conversion','before':old,'after':new,'sites':n});changes[p]=s.replace(old,new)
exact('SpaceComplexity/Machines/Clean','  have hstart : (cleanTM M q₁).runFrom (Cfg.init (.init q) V) 1 = simCfg M q V 0 :=\n    init_step M q₁ q V',
      '  have hstart : (cleanTM M q₁).runFrom (Cfg.init (.init q) V) 1 = simCfg M q V 0 := by\n    rw [MultiTapeTM.runFrom_one]\n    exact init_step M q₁ q V')
exact('TuringMachine/Build/Loop','show (emCallRightTM M).tm.runFrom (emCallRightCfg M c) 1 = _ from hs',
      'show (emCallRightTM M).tm.runFrom (emCallRightCfg M c) 1 = _ from\n    (MultiTapeTM.runFrom_one _ _).trans hs')
exact('TuringMachine/Build/StepBlock','    change (seekTM k).step ((seekTM k).step _) = _\n    rw [first, second]',
      '    rw [MultiTapeTM.runFrom_succ_eq_step\x27, MultiTapeTM.runFrom_one, first, second]')
exact('TuringMachine/Build/StepBlock','    · change ((seekTM k).step _).state ≠ _\n      rw [first]',
      '    · rw [MultiTapeTM.runFrom_one, first]')
exact('TuringMachine/Build/StepBlock','      from first]',
      '      from (MultiTapeTM.runFrom_one _ _).trans first]')
exact('TuringMachine/Universal','    exact timed_clock_start cfg bs bits halt hs',
      '    rw [MultiTapeTM.runFrom_one]\n    exact timed_clock_start cfg bs bits halt hs')
exact('TuringMachine/Universal','    rw [hcfg]\n    simpa using h0',
      '    rw [MultiTapeTM.runFrom_one, hcfg]\n    simpa using h0')
exact('TuringMachine/Robustness/ObliviousCandidate','    simpa only [hu, ↓reduceIte] using macroCfg_check W a base u 0',
      '    rw [MultiTapeTM.runFrom_one]\n    simpa only [hu, ↓reduceIte] using macroCfg_check W a base u 0')
assert not missing,missing
R=O/'revision7';R.mkdir()
for p,s in changes.items():
 a=R/'before'/(p+'.txt');a.parent.mkdir(parents=True,exist_ok=True);a.write_text((W/p).read_text());a=R/'after'/(p+'.txt');a.parent.mkdir(parents=True,exist_ok=True);a.write_text(s)
for p,s in changes.items():(W/p).write_text(s)
(R/'edits.json').write_text(json.dumps(rows,indent=2,ensure_ascii=False)+'\n');print('revision7 owners',len(changes))
