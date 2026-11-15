#!/usr/bin/env python3
"""Compare admitted declaration names in the issued order and all new helpers."""
import importlib.util
import io
import json
from pathlib import Path
import re
import subprocess
import tarfile

spec=importlib.util.spec_from_file_location('headers','evidence/tools/check_headers.py')
h=importlib.util.module_from_spec(spec)
spec.loader.exec_module(h)
archive=subprocess.check_output(['git','archive',h.BASE,'TCSlib'])
source={}
with tarfile.open(fileobj=io.BytesIO(archive)) as tar:
    for entry in tar.getmembers():
        if entry.isfile() and entry.name.endswith('.lean'):
            source[entry.name]=tar.extractfile(entry).read().decode()
paths=[x.strip()+'.lean' for x in Path('evidence/issued/order.txt').read_text().splitlines() if x.strip()]
paths+=subprocess.check_output(['git','diff','--name-only',h.BASE,'--','TCSlib']).decode().splitlines()
paths+=subprocess.check_output(['git','ls-files','--others','--exclude-standard','TCSlib']).decode().splitlines()

def admissions(text,path):
    code,_=h.lex(text)
    decls=h.declarations(text)
    found={}
    for match in re.finditer(r'\bsorry\b',code):
        parent=next((x for x in decls if x['start']<=match.start()<x['end']),None)
        if parent is None: raise RuntimeError(('unattributed admission',path,match.start()))
        key=path+':'+parent['name']
        found[key]=dict(path=path,name=parent['name'],line=text[:match.start()].count('\n')+1)
    return found

before,after={},{}
for path in sorted(set(paths)):
    if path in source: before.update(admissions(source[path],path))
    if Path(path).exists(): after.update(admissions(Path(path).read_text(),path))
out=Path('evidence/admissions')
out.mkdir(parents=True,exist_ok=True)
removed=sorted(set(before)-set(after))
added=sorted(set(after)-set(before))
result=dict(base_count=len(before),current_count=len(after),removed=removed,added=added,
            base=list(before.values()),current=list(after.values()))
(out/'checkpoint1.json').write_text(json.dumps(result,indent=2)+'\n')
print('BASE',len(before),'CURRENT',len(after),'REMOVED',len(removed),'ADDED',len(added))
for name in removed: print('REMOVED',name)
for name in added: print('ADDED',name)
assert len(before)==32 and len(after)==28 and not added
assert {x.rsplit(':',1)[1] for x in removed}=={
    'spDecStr_wrongKey','specialScheme_wrongKey','specialScheme_multiMessageSecure',
    'nestedSpecial_wrongKeyBot'}
