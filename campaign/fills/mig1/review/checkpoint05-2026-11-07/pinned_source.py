"""Recover pinned base bytes from immutable cp02 records, with no Git invocation."""
import hashlib
import json
from pathlib import Path
import re

OUT=Path(__file__).resolve().parent
REPO=OUT.parents[4]
PRIOR=OUT.parent/'checkpoints-2026-11-07'
BASE=json.loads((REPO/'campaign/fills/mig1/dispatch.json').read_text())['lean_base']
FILES=(REPO/'campaign/fills/mig1/inputs/owned-files.txt').read_text().splitlines()


def replay(text,state):
    lines=text.splitlines(keepends=True);i=0;changed=[]
    while i<len(lines):
        m=re.match(r'diff --git a/(\S+) b/(\S+)\n',lines[i])
        if not m:i+=1;continue
        a,b=m.groups();assert a==b and a in FILES,(a,b)
        old=state[a].splitlines(keepends=True);new=[];pos=0;i+=1;hunks=0
        while i<len(lines) and not lines[i].startswith('diff --git '):
            h=re.match(r'@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@',lines[i])
            if not h:i+=1;continue
            start,count,nstart,ncount=[int(x) if x is not None else 1 for x in h.groups()]
            assert start-1>=pos
            new.extend(old[pos:start-1]);pos=start-1
            assert len(new)==nstart-1
            consumed=produced=0;i+=1;hunks+=1
            while i<len(lines) and (consumed<count or produced<ncount):
                line=lines[i];tag=line[0];assert tag in ' +-',line
                if tag in ' -':
                    assert pos<len(old) and old[pos]==line[1:],(a,pos+1,line)
                    pos+=1;consumed+=1
                if tag in ' +':new.append(line[1:]);produced+=1
                i+=1
            assert consumed==count and produced==ncount
        assert hunks>0
        new.extend(old[pos:]);state[a]=''.join(new);changed.append(a)
    return changed


def reverse_patch(text):
    result=[]
    for l in text.splitlines(keepends=True):
        m=re.match(r'@@ -(\d+(?:,\d+)?) \+(\d+(?:,\d+)?) @@(.*)',l)
        if m:result.append('@@ -'+m[2]+' +'+m[1]+' @@'+m[3]+'\n')
        elif l.startswith('+'):result.append('-'+l[1:])
        elif l.startswith('-'):result.append('+'+l[1:])
        else:result.append(l)
    return ''.join(result)


def base_sources():
    prior=json.loads((PRIOR/'source-comparison.json').read_text())
    receipt=json.loads((PRIOR/'receipt.json').read_text())
    assert BASE==prior['base']==receipt['pinned_base']
    root=PRIOR/'cp02/fill-mig1-mega-cp02'
    state={f:(root/'source'/(f+'.txt')).read_text() for f in FILES}
    for f,s in state.items():
        assert hashlib.sha256(s.encode()).hexdigest()==prior['checkpoints']['cp02'][f]['sha256']
    original=state.copy()
    patches=sorted((root/'patches').glob('*.patch'))
    for p in reversed(patches):replay(reverse_patch(p.read_text()),state)
    restored=state.copy()
    for p in patches:replay(p.read_text(),restored)
    assert original==restored
    return state
