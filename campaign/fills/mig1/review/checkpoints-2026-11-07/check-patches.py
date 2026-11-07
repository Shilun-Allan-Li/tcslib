"""Validate cumulative textual patches in memory, without applying Git patches."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

OUT=Path(__file__).resolve().parent
REPO=OUT.parents[4]
BASE=json.loads((REPO/'campaign/fills/mig1/dispatch.json').read_text())['lean_base']
FILES=(REPO/'campaign/fills/mig1/inputs/owned-files.txt').read_text().splitlines()


def replay(text, state):
    lines=text.splitlines(keepends=True);i=0;changed=[];head=re.match(r'From ([0-9a-f]{40}) ',lines[0]).group(1)
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
                    assert pos<len(old) and old[pos]==line[1:],(a,pos+1,old[pos] if pos<len(old) else '',line)
                    pos+=1;consumed+=1
                if tag in ' +':new.append(line[1:]);produced+=1
                i+=1
            assert consumed==count and produced==ncount
        assert hunks>0
        new.extend(old[pos:]);state[a]=''.join(new);changed.append(a)
    return dict(patch_commit_header=head,files=changed,all_hunks_exact=True)


def main():
    state={f:subprocess.check_output(['git','-C',str(REPO),'show',BASE+':'+f],text=True) for f in FILES}
    results={}
    for cp in ['cp01','cp02']:
        # Each archive is cumulative, so independently replay its entire series from base.
        current=state.copy();root=OUT/cp/('fill-mig1-mega-'+cp)
        rows=[]
        for patch in sorted((root/'patches').glob('*.patch')):
            rows.append(dict(path=patch.name,**replay(patch.read_text(),current)))
        for f,text in current.items():assert text==(root/'source'/(f+'.txt')).read_text(),(cp,f)
        expected_head=(root/'HEAD.txt').read_text().strip()
        assert rows[-1]['patch_commit_header']==expected_head
        assert len(list((root/'source').rglob('*.lean.txt')))==len(FILES)
        bundle=(root/'fill-mig1-mega.bundle').read_bytes()
        header=bundle[:bundle.index(b'\n\n')].decode()
        assert BASE in header and expected_head in header
        results[cp]=dict(patches=rows,snapshots_exactly_match_patch_reconstruction=True,
                        bundle_header=header,bundle_sha256=hashlib.sha256(bundle).hexdigest(),
                        limitation='Bundle pack data not imported or independently reconstructed; commit IDs are delivered metadata.')
    (OUT/'patch-consistency.json').write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps(results,indent=2))


if __name__=='__main__':main()
