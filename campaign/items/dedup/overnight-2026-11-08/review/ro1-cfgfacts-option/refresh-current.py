from pathlib import Path
import re,json,difflib,hashlib
O=Path('/private/tmp/ab34-ro1-integration');W=Path('/Users/seyoonr/.codex/worktrees/ab34-sg1/tcslib-arora-barak-ch3-4')
rows=[];graph={};patch=[]
for p in sorted((W/'TCSlib').rglob('*.lean')):
    rel=str(p.relative_to(W));s=p.read_text();old=(O/'source-before'/(rel+'.txt')).read_text();m=rel[:-5].replace('/','.')
    graph[m]=re.findall(r'^import\s+(\S+)',s,re.M)
    if s!=old:
        dst=O/'source-current'/(rel+'.txt');dst.parent.mkdir(parents=True,exist_ok=True);dst.write_text(s)
        rows.append({'path':rel,'baseline_sha256':hashlib.sha256(old.encode()).hexdigest(),'candidate_sha256':hashlib.sha256(s.encode()).hexdigest()})
        patch.extend(difflib.unified_diff(old.splitlines(True),s.splitlines(True),fromfile='a/'+rel,tofile='b/'+rel))
changed={r['path'] for r in rows};seen=set();active=set();order=[]
def visit(m):
    if m in active:raise RuntimeError('cycle: '+m)
    if m in seen:return
    active.add(m)
    for n in graph.get(m,[]):visit(n)
    active.remove(m);seen.add(m)
    p=m.replace('.','/')+'.lean'
    if p in changed:order.append(p)
for m in sorted(graph):visit(m)
def closure(m):
    todo=[m];seen=set()
    while todo:
        x=todo.pop()
        if x not in seen:seen.add(x);todo.extend(graph.get(x,[]))
    return seen
for r in rows:
    s=(W/r['path']).read_text();m=r['path'][:-5].replace('/','.')
    if 'MultiTapeTM.runFrom_one' in s:assert 'TCSlib.Complexity.TuringMachine.CfgFacts' in closure(m),r['path']
(O/'current-source-map.json').write_text(json.dumps(rows,indent=2)+'\n')
(O/'current-import-graph.json').write_text(json.dumps(graph,indent=2)+'\n')
(O/'current-owner-order.json').write_text(json.dumps(order,indent=2)+'\n')
(O/'current-held-candidate.patch').write_text(''.join(patch))
print('changed owners',len(rows),'graph acyclic; all cited generic APIs reachable')
