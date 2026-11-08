"""Classify exact compiler deltas against authored source; keep all private IDs intact."""
from pathlib import Path
import base64
import collections
import difflib
import gzip
import hashlib
import json
import re

OUT=Path(__file__).resolve().parent
ROOT=OUT.parents[4]
diff=json.loads((OUT/'comparison-staged.json').read_text())
base=json.loads((OUT/'map-Base.json').read_text())
head=json.loads((OUT/'map-Head.json').read_text())
parser=ROOT/'devtools/seyoon/declfreeze.py'
ns={}
exec(compile(parser.read_text().split('\na = chunks(',1)[0],str(parser),'exec'),ns)
source={}
for label in ['base','head']:
    source[label]={}
    for owner in (OUT/'original9-owners.txt').read_text().splitlines():
        rel=owner.replace('.','/')+'.lean.txt'
        source[label][owner]=ns['chunks']((OUT/'source'/label/rel).read_text())


def authored(label,n,row):
    matches=[s for s,p,t in source[label][row['owner']]
             if (n.endswith('.'+s) if p else n==s)]
    assert len(matches)<=1
    return matches[0] if matches else None


classes={}
for tag,label in [('added','head'),('removed','base')]:
    classes[tag]=[]
    for n,row in diff[tag].items():
        source_name=authored(label,n,row)
        classes[tag].append(dict(name=n,owner=row['owner'],kind=row['kind'],private=row['private'],
                                 internal=row['internal'],category='authored private source lemma' if source_name else 'compiler-generated auxiliary',
                                 authored_name=source_name,axioms=row['axioms']))
    assert sum(x['authored_name'] is not None for x in classes[tag])==3
    assert all(x['private'] for x in classes[tag])
type_changes=[]
for n in diff['common_field_changes']['type_repr']:
    a,b=base['census'][n],head['census'][n]
    assert a['private'] and b['private'] and '._proof_' in n
    assert not authored('base',n,a) and not authored('head',n,b)
    type_changes.append(dict(name=n,owner=a['owner'],kind=a['kind'],category='private generated proof auxiliary',
                             before=a['type_repr'],after=b['type_repr']))
classes['retained_name_type_changes']=type_changes
classes['axiom_changes']={n:dict(before=base['census'][n]['axioms'],after=head['census'][n]['axioms'])
                           for n in diff['common_field_changes']['axioms']}
classes['scope']='Authored classification uses actual owner plus complete source-qualified suffix solely to locate source declarations. Compiler-name comparisons/deltas retain every exact private ID; no private-ID normalization or cross-context renaming is used. Other unmatched deltas are generated match/equation/simp/proof auxiliaries, not removed source APIs.'
(OUT/'delta-classification.json').write_text(json.dumps(classes,indent=2)+'\n')

changed=set(diff['common_field_changes']['type_repr'])
texts={}
for label in ['Base','Head']:
    raw=gzip.decompress(base64.decodebytes((OUT/(label+'-types-v1.out.gz.b64')).read_bytes())).decode()
    marks=list(re.finditer(r'^(TYPE_REPR|TYPECOMPLETE)\|([^|\n]+)(?:\|)?',raw,re.M))
    blocks=[]
    found=set()
    for i,m in enumerate(marks[:-1]):
        if m[2] in changed:
            blocks.append(raw[m.start():marks[i+1].start()]);found.add(m[2])
    assert found==changed
    texts[label]=''.join(blocks)
    (OUT/('changed-private-types-'+label+'.txt')).write_text(texts[label])
(OUT/'changed-private-types.patch').write_text(''.join(difflib.unified_diff(texts['Base'].splitlines(keepends=True),texts['Head'].splitlines(keepends=True),fromfile='Base exact raw private auxiliary types',tofile='Head exact raw private auxiliary types')))

receipt=ROOT/'campaign/gates/106-sg1-dedup/evidence/current-replay-r3/receipt.json'
replay=json.loads(receipt.read_text())
assert replay['result']=='PASS' and replay['pipeline_exit']==replay['failures']==replay['error_rows']==replay['static_mismatches']==0
assert replay['modules']==329 and replay['head']==diff['head'] and replay['snapshot_lean']==diff['base']
pins=[dict(path=str(receipt.relative_to(ROOT)),bytes=receipt.stat().st_size,sha256=hashlib.sha256(receipt.read_bytes()).hexdigest())]
for row in replay['evidence']:
    p=receipt.parent/row['path'];data=p.read_bytes()
    assert len(data)==row['bytes'] and hashlib.sha256(data).hexdigest()==row['sha256']
    pins.append(dict(path=str(p.relative_to(ROOT)),bytes=len(data),sha256=row['sha256']))
(OUT/'root-replay-evidence-pins.json').write_text(json.dumps(dict(origin='Root-owned replay; child only read/pinned completed receipts and artifact hashes',receipt=replay,pins=pins),indent=2)+'\n')
print(json.dumps(dict(added=collections.Counter(x['category'] for x in classes['added']),removed=collections.Counter(x['category'] for x in classes['removed']),private_auxiliary_type_changes=len(type_changes),root_replay_files_pinned=len(pins)),indent=2))
