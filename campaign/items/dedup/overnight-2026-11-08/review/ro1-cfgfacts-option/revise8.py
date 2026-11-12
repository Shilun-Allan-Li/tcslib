from pathlib import Path
import re,json
O=Path('/private/tmp/ab34-ro1-integration');W=Path('/Users/seyoonr/.codex/worktrees/ab34-sg1/tcslib-arora-barak-ch3-4');p='TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean';s=(W/p).read_text();home='TCSlib.Complexity.TuringMachine.CfgFacts'
g=json.loads((O/'current-import-graph.json').read_text());m=p[:-5].replace('/','.');todo=[home];seen=set()
while todo:
 n=todo.pop()
 if n not in seen:seen.add(n);todo.extend(g.get(n,[]))
assert m not in seen
assert ('import '+home) not in s
imports=list(re.finditer(r'^import[^\n]*\n',s,re.M));pos=imports[-1].end();new=s[:pos]+'import '+home+'\n'+s[pos:]
R=O/'revision8';R.mkdir();(R/'ObliviousCandidate.before.lean.txt').write_text(s);(R/'ObliviousCandidate.after.lean.txt').write_text(new);(W/p).write_text(new)
(R/'held-import.json').write_text(json.dumps({'path':p,'addition':'import '+home,'status':'HELD HYPOTHETICAL / not authorized to publish','acyclic':True,'reason':'full closure preflight found this inline one-step conversion does not inherit the approved home'},indent=2)+'\n')
