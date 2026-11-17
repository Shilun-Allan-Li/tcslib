from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import hashlib
import json
import re
import runpy
import subprocess
import sys

root = Path(__file__).parent
lib = {}
driver = (root/'seals.py').read_text()
start = driver.index('decl = ')
end = driver.index('rows = []',start)
import os as _os, json as _json
_GATE = Path(_os.environ['GATE']); _CFG = _json.loads((_GATE/'gate.json').read_text())
_KIT = Path(__file__).resolve().parents[1]
w = Path(_CFG['repo'])
tools = w/'devtools/seyoon'
out, overlay, candidate, freeze = map(Path,sys.argv[1:5])
mode = sys.argv[5]
r3 = _GATE/'replay/runtime'
scope = {'root':root,'tools':tools,'Path':Path,'native_source':candidate,'r3':r3.parent,'mode':mode}
exec(compile(driver[start:end], 'seals definitions', 'exec'), scope)
exec(compile(driver[driver.index('def forced('):driver.index("if mode == 'preflight-focus':")],
             'seals rule selection','exec'),scope)
focus, chunks, forced = scope['focus'], scope['names']['chunks'], scope['forced']
guard = scope['guard'].replace('GUARD_ACTIVE|{n}', 'GUARD_ACTIVE|ROOT_NAME|{n}')
metadata = {} if mode.startswith('preflight') else json.loads(Path(sys.argv[6]).read_text())['BOUNDARY']
out.mkdir()
rt = out/'runtime'
rt.mkdir()
(rt/'lean-toolchain').write_bytes((r3/'lean-toolchain').read_bytes())
(rt/'.lake').mkdir()
(rt/'.lake/packages').symlink_to((r3/'.lake/packages').resolve(),target_is_directory=True)

def digest(s):
    return hashlib.sha256(s).hexdigest()
def write(path,data):
    (out/path).write_text(json.dumps(data,ensure_ascii=False,indent=2)+'\n')

graph_script = candidate/'devtools/seyoon/graph.py'
if graph_script.is_file():
    imports_of=runpy.run_path(str(graph_script))['imports_of']
    def reachable(path):
        result=set()
        stack=list(imports_of(candidate/path))
        while stack:
            m=stack.pop()
            if m in result:
                continue
            result.add(m)
            loc=candidate/(m.replace('.','/')+'.lean')
            if loc.is_file():
                stack.extend(imports_of(loc))
        return result
    def exact_forced(path):
        modules=reachable(path)
        return {'Turing.'+n:flag for n,(home,flag) in scope['rules'].items()
                if 'TCSlib.Complexity.TuringMachine.'+home.replace('/','.') in modules}
else:
    exact_forced=forced

owners=[]
for row in json.loads(freeze.read_text())['owner_source']:
    rel = row['path']
    if mode.endswith('-two') and rel not in focus:
        continue
    src = candidate/rel
    if not src.is_file():
        assert mode.startswith('preflight'), rel
        src = r3/rel
    original = src.read_text()
    assert digest(original.encode())==row['sha256'],rel
    required = set(row['total_changed_or_added_from_campaign'])
    required.update('Turing.FinTM.'+n for n in focus.get(rel,()))
    positions = []
    for name,_,chunk in chunks(original):
        if name not in required:
            continue
        body = chunk.split('-/',1)[1].lstrip() if chunk.startswith('/--') else chunk
        if not re.match(r'(?:(?:private|protected|noncomputable)\s+)*(lemma|theorem)\s+',body):
            continue
        heads = exact_forced(rel)
        if metadata:
            assert name in metadata,name
            for d in metadata[name]['foreign_definitions']:
                if d['ordinary']:
                    heads[d['name']] = d['simp'] or d['unfold']
        assert heads,name
        assert original.count(chunk)==1
        decl_pos = original.index(chunk)
        tail = decl_pos+len(chunk)
        begin = decl_pos
        while prior:=re.search(r'(?m)^open [^\n]+ in\s*\n\s*\Z', original[:begin]):
            begin = prior.start()
        positions.append((begin,tail,name,heads))
    text = ''
    last = 0
    checks=[]
    for begin,tail,name,heads in sorted(positions):
        assert begin>=last
        text+=original[last:begin]
        first = text.count('\n')+1
        sealed = sorted(heads)
        removed = sorted(n for n in heads if heads[n])
        disable = 'attribute [-simp] '+' '.join(removed)+' in\n' if removed else ''
        text += 'section Gate129ReaderCheck\nattribute [local irreducible] '+' '.join(sealed)+'\n'
        text += disable + original[begin:tail]+'\n'
        g=guard.replace('HEAD_NAMES',scope['nlist'](sealed)).replace('ROOT_NAME',name)
        text += disable + g.lstrip() + 'end Gate129ReaderCheck\n'
        checks.append({'name':name,'heads':sealed,'simp_removed':removed,'probe_lines':[first,text.count('\n')],
            'source_lines':[original[:begin].count('\n')+1,original[:tail].count('\n')+1],
            'exact_proof_sha256':digest(original[begin:tail].encode())})
        last=tail
    text+=original[last:]
    filename=Path(rel).name
    (rt/filename).write_text(text)
    owners.append({'owner':rel,'file':filename,'source_sha256':row['sha256'],
        'probe_sha256':digest(text.encode()),'checks':checks})
write('REQUEST.json',{'mode':mode,'object_tree':str(overlay),'owners':owners})

def run(owner):
    f=owner['file']
    cmd=['bash',str(tools/'leanelab.sh'),str(rt),str(overlay),f]
    p=subprocess.run(cmd,capture_output=True)
    log=p.stdout+p.stderr
    (out/(f+'.log')).write_bytes(log)
    raw=log.decode()
    active={}
    for name,head in re.findall(r'GUARD_ACTIVE\|([^|\n]+)\|([^\n]+)',raw):
        active.setdefault(name,[]).append(head)
    diagnostics = []
    for m in re.finditer(r'^'+re.escape(f)+r':(\d+):\d+: error:',raw,re.M):
        line=int(m.group(1))
        responsible=next((z['name'] for z in owner['checks'] if z['probe_lines'][0]<=line<=z['probe_lines'][1]),None)
        diagnostics.append({'line':line,'root':responsible,'first_line':raw[m.start():].split('\n',1)[0]})
    counts_match=all(sorted(active.get(c['name'],[]))==c['heads'] for c in owner['checks'])
    ok = p.returncode==0 and not diagnostics and counts_match
    print(f, 'PASS' if ok else 'FAIL',len(owner['checks']),'proofs',len(diagnostics),'errors',flush=True)
    for entry in diagnostics:
        print(entry['root'],entry['first_line'],flush=True)
    return owner|{'exit':p.returncode,'pass':ok,'argv':cmd,'log_sha256':digest(log),'diagnostics':diagnostics,
        'verified_active_heads':active,'guard_rows_match':counts_match}

with ThreadPoolExecutor(max_workers=2) as pool:
    results=list(pool.map(run,owners))
passed=all(x['pass'] for x in results)
write('RESULT.json',{'pass':passed,'proof_count':sum(len(x['checks']) for x in owners),
    'owner_count':len(owners),'owners':results})
sys.exit(0 if passed else 1)
