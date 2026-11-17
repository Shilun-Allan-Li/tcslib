from pathlib import Path
import collections
import hashlib
import json
import re
import shutil
import subprocess
import sys

d=Path(__file__).parent
import os as _os, json as _json
_GATE = Path(_os.environ['GATE']); _CFG = _json.loads((_GATE/'gate.json').read_text())
_REPO = Path(_CFG['repo']); _KIT = Path(__file__).resolve().parents[1]
r3=_GATE/'base-src'  # the base revision's owners
f=d/'ship-r5'
r4=Path(sys.argv[1]) if len(sys.argv)>1 else f/'replay/runtime'
w=_REPO
out=Path(sys.argv[4]) if len(sys.argv)>4 else f/'qa'
out.mkdir()
freeze=Path(sys.argv[2]) if len(sys.argv)>2 else f/'SOURCE.json'
paths=[x['path'] for x in json.loads(freeze.read_text())['owner_source']]
raws={}
for label,root in (('BASE',r3),('HEAD',r4)):
    qa=out/label
    (qa/'scripts').mkdir(parents=True)
    for path in paths:
        target=qa/path
        target.parent.mkdir(parents=True,exist_ok=True)
        if label=='BASE' and not (root/path).exists():  # gate 149: a new owner is empty at base
            target.write_bytes(b'')
        else:
            shutil.copyfile(root/path,target)
    for s in ('style_lint','campaign_style_lint'):
        shutil.copyfile(w/'scripts'/(s+'.py'),qa/'scripts'/(s+'.py'))
    a=subprocess.run(['python3','-I','scripts/style_lint.py',*paths],cwd=qa,capture_output=True)
    b=subprocess.run(['python3','-I','scripts/campaign_style_lint.py','--check8b'],cwd=qa,capture_output=True)
    (out/(label+'-style.log')).write_bytes(a.stdout+a.stderr)
    (out/(label+'-campaign.log')).write_bytes(b.stdout+b.stderr)
    style=[]
    for line in a.stdout.decode().splitlines():
        if not line or re.search(r': \d+ lines \(> 1000',line):
            continue
        line=re.sub(r':\d+: ',': ',line)
        line=re.sub(r'proof is \d+ lines','proof is N lines',line)
        style.append(line)
    campaign=[]
    for line in b.stdout.decode().splitlines():
        m=re.match(r'^(WARN|FAIL)\s+(\S+)\s+(.*)',line)
        if m and not re.match(r'\d+ lines > 1000',m[3]):
            campaign.append(tuple(m.groups()))
    raws[label]={'style':style,'campaign':campaign,'style_exit':a.returncode,'campaign_exit':b.returncode}
deltas={}
for x in ('style','campaign'):
    a,b=[collections.Counter(raws[l][x]) for l in ('BASE','HEAD')]
    deltas[x]={'new':list((b-a).elements()),'removed':list((a-b).elements())}
(out/'LINT.json').write_text(json.dumps({'scopes':raws,'deltas':deltas},indent=2)+'\n')

scope={}
parser=(w/'devtools/seyoon/declfreeze.py').read_text()
exec(parser.split('a = chunks(open(sys.argv[1]).read())')[0],scope)
cleanup=(_KIT/'templates/prepare_boundaries.py').read_text()
exec(cleanup[cleanup.index('def clean(s):'):cleanup.index('for idx,m in enumerate(M,1):')],scope)
metadata_file=Path(sys.argv[3]) if len(sys.argv)>3 else f/'metadata/DATA.json'
metadata=json.loads(metadata_file.read_text())['BOUNDARY']
all_foreign={x['name']:x['owner'] for t in metadata.values() for x in t['foreign_definitions'] if x['ordinary']}
def list_items(code,start):
    depth=0
    prev=start
    for i in range(start,len(code)):
        c=code[i]
        if c in '[({':
            depth+=1
        elif c in '])}':
            if depth==0:
                yield code[prev:i]
                return
            depth-=1
        elif c==',' and depth==0:
            yield code[prev:i]
            prev=i+1
    raise ValueError('unclosed tactic list',code[start:start+100])
args=re.compile(r'\b(simp|simpa|dsimp|rw|erw|simp_all|simp_rw|grind|simp_arith)\b(?:\s+only)?\s*\[')
delta=re.compile(r'\b(unfold|delta)\s+([^\n;]+)')
hits=[]
seen=set()
for path in paths:
    text=(r4/path).read_text()
    mod=path[:-5].replace('/','.')
    tokens={}
    for n,home in all_foreign.items():
        if home!=mod:
            for t in (n,n.removeprefix('Turing.'),n.rsplit('.',1)[-1]):
                tokens[t]=n
    for n,_,chunk in scope['chunks'](text):
        if n not in metadata:
            continue
        seen.add(n)
        clean=scope['clean'](chunk)
        for op in args.finditer(clean):
            for a in list_items(clean,op.end()):
                item=a.lstrip()
                if item.startswith('-'):
                    continue
                key=re.match(r'(?:[←@]\s*)?(?:_root_\.)?([\w.]+)',item)
                if key and key[1] in tokens:
                    hits.append({'owner':path,'root':n,'operation':op[1],
                        'head':tokens[key[1]],'argument':item.strip()})
        for op in delta.finditer(clean):
            for word in op[2].split(' at ')[0].split():
                if word in tokens:
                    hits.append({'owner':path,'root':n,'operation':op[1],'head':tokens[word]})
assert seen==set(metadata)
(out/'FOREIGN-ARGUMENTS.json').write_text(json.dumps({'roots':len(seen),'ordinary_heads_considered':len(all_foreign),
    'explicit_read_candidates':hits,'is_a_syntax_sweep':True},indent=2)+'\n')
print('proof syntax sweep',len(seen),'roots',len(hits),'read candidates')
for h in hits:
    print(h)
print('normalized lint changes',deltas)
