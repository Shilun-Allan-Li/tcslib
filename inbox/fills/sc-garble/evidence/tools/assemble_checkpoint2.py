#!/usr/bin/env python3
"""Assemble and verify the complete, explicitly partial checkpoint-2 payload."""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

BASE='fbd37f447596d4207c8d08b7ef7602f57fe95198'
PIN='7d85785c2e98f0bfdec081a875a9343f06043a8a'
root=Path.cwd()
payload=Path('/private/tmp/sc-garble-runtime/checkpoint2/sc-garble')
replay=Path('/private/tmp/sc-garble-runtime/replay-checkpoint2')
signature_results=Path('evidence/logs/checkpoint2-check/results.jsonl')
assert signature_results.exists(), 'signature check is still waiting/running'
all_results=[json.loads(x)for x in signature_results.read_text().splitlines()]
assert len(all_results)==8 and all(x['exit']==0 and x['errors']==0 for x in all_results)
last_signature=all_results[-1]
assert last_signature['exit']==0 and last_signature['errors']==0,last_signature
head=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
assert head.startswith('fb7971f88')
assert not subprocess.check_output(['git','diff','--name-only','--','TCSlib'])
assert not subprocess.check_output(['git','diff','--cached','--name-only'])
if payload.exists(): shutil.rmtree(payload)
(payload/'patches').mkdir(parents=True)
subprocess.run(['git','format-patch','--full-index','--output-directory',str(payload/'patches'),
                BASE+'..HEAD'],check=True)
commits=subprocess.check_output(['git','rev-list','--reverse',BASE+'..HEAD'],text=True).splitlines()
rows=[]
for commit in commits:
    fields=subprocess.check_output(['git','show','-s',
        '--format=%H%x09%an%x09%ae%x09%aI%x09%cn%x09%ce%x09%cI',commit],text=True).strip().split('\t')
    raw=subprocess.check_output(['git','cat-file','commit',commit])
    assert b'\ngpgsig ' not in raw
    rows.append(fields+['none'])
(payload/'patches/COMMITS.tsv').write_text(
    'hash\tauthor_name\tauthor_email\tauthor_date\tcommitter_name\tcommitter_email\tcommitter_date\tsigning\n'+
    ''.join('\t'.join(row)+'\n' for row in rows))

# Replay in an isolated Git clone without any Lean or dependency cache.
can_reuse_replay = replay.exists() and Path('evidence/replay/checkpoint2.log').exists()
if can_reuse_replay:
    can_reuse_replay = subprocess.check_output(['git','rev-parse','HEAD'],cwd=replay,text=True).strip()==head
    can_reuse_replay = can_reuse_replay and 'PASS: every unsigned commit hash reproduced exactly.' in Path('evidence/replay/checkpoint2.log').read_text()
if can_reuse_replay:
    print('REPLAY PASS retained for unchanged source head',head)
else:
    if replay.exists(): shutil.rmtree(replay)
    replaylog=Path('evidence/replay/checkpoint2.log')
    replaylog.parent.mkdir(parents=True,exist_ok=True)
    with replaylog.open('w') as log:
        subprocess.run(['git','clone','--shared','--no-checkout',str(root),str(replay)],
                       check=True,stdout=log,stderr=subprocess.STDOUT)
        subprocess.run(['git','checkout','--detach',BASE],cwd=replay,
                       check=True,stdout=log,stderr=subprocess.STDOUT)
        patches=sorted((payload/'patches').glob('*.patch'))
        assert len(patches)==len(rows)
        for row,patch in zip(rows,patches):
            env=os.environ.copy()
            env.update(GIT_COMMITTER_NAME=row[4],GIT_COMMITTER_EMAIL=row[5],GIT_COMMITTER_DATE=row[6])
            subprocess.run(['git','-c','commit.gpgsign=false','am',str(patch)],cwd=replay,env=env,
                           check=True,stdout=log,stderr=subprocess.STDOUT)
            actual=subprocess.check_output(['git','rev-parse','HEAD'],cwd=replay,text=True).strip()
            log.write('EXPECTED '+row[0]+' ACTUAL '+actual+'\n')
            assert actual==row[0]
        log.write('PASS: every unsigned commit hash reproduced exactly.\n')

files=subprocess.check_output(['git','diff','--name-only',BASE,head,'--','TCSlib'],text=True).splitlines()
line_rows=[]
for file in files:
    data=subprocess.check_output(['git','show',head+':'+file])
    dest=payload/'src'/file
    dest.parent.mkdir(parents=True,exist_ok=True)
    dest.write_bytes(data)
    old=subprocess.run(['git','show',BASE+':'+file],stdout=subprocess.PIPE,stderr=subprocess.DEVNULL)
    line_rows.append((file,len(old.stdout.decode().splitlines()) if old.returncode==0 else 0,
                      len(data.decode().splitlines())))
    assert all(len(line)<=100 for line in data.decode().splitlines()) and line_rows[-1][2]<=1000
for kind in ['FAIL','WARN']:
    before={s for s in Path('evidence/logs/lint-base.log').read_text().splitlines() if s.startswith(kind)}
    after={s for s in Path('evidence/logs/lint-checkpoint2-final.log').read_text().splitlines() if s.startswith(kind)}
    assert before==after,(kind,before-after,after-before)

# Record the actual scoped slot traffic without altering any host lock.
slotlog=Path('/Users/seyoonr/.lean-slots/slots.log')
Path('evidence/logs/slots.log').write_text(''.join(
    line for line in slotlog.read_text().splitlines(True) if 'tag=sc-garble ' in line))
shutil.copytree('evidence',payload/'evidence',ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
signatures=Path('evidence/declarations/checkpoint2-signatures.txt').read_text()
table='\n'.join('| `'+path+'` | '+str(a)+' | '+str(b)+' |' for path,a,b in line_rows)
report=Path('evidence/checkpoint2-report-template.md').read_text().replace('{head}',head).replace('{table}',table).replace('{signatures}',signatures.rstrip())
(payload/'REPORT.md').write_text(report)

def manifest(folder):
    paths=sorted(p for p in folder.rglob('*') if p.is_file() and p!=folder/'SHA256SUMS')
    (folder/'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+
        p.relative_to(folder).as_posix()+'\n' for p in paths))
    listed=[line[66:] for line in (folder/'SHA256SUMS').read_text().splitlines()]
    assert listed==[p.relative_to(folder).as_posix() for p in paths]
    result=subprocess.run(['shasum','-a','256','-c','SHA256SUMS'],cwd=folder,
                          text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    assert result.returncode==0,result.stdout
    print('MANIFEST PASS',folder,len(paths),'files')

manifest(payload/'evidence')
manifest(payload)
print('PAYLOAD',payload)
print('SOURCE_HEAD',head)
