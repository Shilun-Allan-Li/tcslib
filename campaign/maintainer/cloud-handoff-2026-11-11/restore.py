#!/usr/bin/env python3
"""Verify or extract the handoff data into an empty scratch directory."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import zipfile

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--extract',type=Path,help='An empty destination in scratch space.')
parser.add_argument('--verify',action='store_true',help='Verify all archives and objects.')
args=parser.parse_args()
root=Path(__file__).resolve().parent
manifest=json.loads((root/'MANIFEST.json').read_text())
assert manifest['format']=='ab34-content-archive-v1'
sha=lambda raw:hashlib.sha256(raw).hexdigest()

def relative(name):
    p=Path(name)
    assert name and not p.is_absolute() and '..' not in p.parts,name
    return p

entries=manifest['entries']
objects=manifest['objects']
assert len(entries)==manifest['logical_files'] and len(objects)==manifest['unique_objects']
by_object={}
for name,row in entries.items():
    relative(name)
    assert row['sha256'] in objects and row['bytes']==objects[row['sha256']]['bytes'],name
    by_object.setdefault(row['sha256'],[]).append((name,row))
assert set(by_object)==set(objects)
dest=args.extract
if dest is not None:
    dest=dest.resolve()
    assert not dest.exists() or (dest.is_dir() and not any(dest.iterdir())),dest
    dest.mkdir(parents=True,exist_ok=True)
verified=set()
for name,archive in manifest['archives'].items():
    assert re.fullmatch(r'payload-\d+\.zip',name),name
    p=root/name
    assert p.stat().st_size==archive['bytes'] and sha(p.read_bytes())==archive['sha256'],name
    selected={k:v for k,v in objects.items() if v['archive']==name}
    assert len(selected)==archive['objects']
    assert all(re.fullmatch(r'[0-9a-f]{64}',k) and v['member']=='objects/'+k for k,v in selected.items())
    with zipfile.ZipFile(p) as data:
        assert set(data.namelist())=={v['member'] for v in selected.values()}
        for digest,row in selected.items():
            raw=data.read(row['member'])
            assert len(raw)==row['bytes'] and sha(raw)==digest,digest
            assert digest not in verified
            verified.add(digest)
            if dest is not None:
                for logical,item in by_object[digest]:
                    target=dest/relative(logical)
                    target.parent.mkdir(parents=True,exist_ok=True)
                    with target.open('xb') as out:
                        out.write(raw)
                    os.chmod(target,item['mode'] & 0o777)
assert verified==set(objects)
verb='Extracted and verified' if dest is not None else 'Verified'
print(verb,len(entries),'logical files in',len(manifest['archives']),'archives.')
