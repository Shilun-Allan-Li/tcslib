from pathlib import Path
import json,subprocess,sys,time,hashlib
O=Path('/private/tmp/ab34-ro1-integration')
g=json.loads((O/'current-import-graph.json').read_text())
changed=set(json.loads((O/'current-owner-order.json').read_text()))
todo={p[:-5].replace('/','.'):p for p in changed}
seen=set();active=set();order=[]
def visit(m):
    if m in active:raise RuntimeError('proposed graph cycle '+m)
    if m in seen:return
    active.add(m)
    for n in g.get(m,[]):visit(n)
    active.remove(m);seen.add(m)
    if m in todo:order.append(todo[m])
for m in sorted(todo):visit(m)
(O/'native-owner-order.json').write_text(json.dumps(order,indent=2)+'\n')
for i,p in enumerate(order,1):
    key=p[:-5].replace('/','__')
    source_hash=hashlib.sha256((Path('/Users/seyoonr/.codex/worktrees/ab34-sg1/tcslib-arora-barak-ch3-4')/p).read_bytes()).hexdigest()
    fresh=Path('/private/tmp/ab34-ro1-native-overlay')/(p[:-5]+'.olean')
    passed=False
    for receipt in (O/'native').glob(key+'__*.json'):
        r=json.loads(receipt.read_text())
        if r['exit']==0 and r['source_sha256']==source_hash and fresh.is_file() and r['fresh_olean_sha256']==hashlib.sha256(fresh.read_bytes()).hexdigest():passed=True
    if passed:
        print(f'OWNER_PREVIOUS_PASS {i}/{len(order)} {p}',flush=True);continue
    print(f'OWNER_START {i}/{len(order)} {p}',flush=True)
    attempt='attempt'+str(1+max([int(x.stem.split('__attempt')[-1]) for x in (O/'native').glob(key+'__attempt*.log')]+[0]))
    q=subprocess.run([sys.executable,'-I',str(O/'run-owner.py'),p,attempt])
    print(f'OWNER_END {i}/{len(order)} exit={q.returncode} {p}',flush=True)
    if q.returncode:
        print('STOPPED_ON_FIRST_FAILURE',flush=True);sys.exit(q.returncode)
print('ALL_CHANGED_OWNERS_PASS',flush=True)
