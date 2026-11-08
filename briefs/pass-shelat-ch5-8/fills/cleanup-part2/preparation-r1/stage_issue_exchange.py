"""Stage only the reviewed cleanup outbox, preserving the shared exchange."""
from pathlib import Path
import datetime
import hashlib
import json
import re
import subprocess
import sys

PREP=Path(__file__).resolve().parent
MAIN=Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4')
EXCHANGE=MAIN.parent/'tcslib-exchange'
SOURCE=MAIN/'briefs/pass-shelat-ch5-8/fills/cleanup-part2/issued-r1'
PREFIX='outbox/fills/cleanup-part2/'
DEST=EXCHANGE/PREFIX
BRANCH='exchange/pass-shelat-ch5-8'


def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def git(repo,*args): return subprocess.check_output(['git','-C',str(repo),*args],text=True).strip()
def mutate(*args):
    result=subprocess.run(['git','-C',str(EXCHANGE),*args],capture_output=True,text=True)
    if result.returncode:
        print(result.stdout+result.stderr)
        raise SystemExit(result.returncode)
    return result


def verify_tree(repo,commit,prefix,expected):
    raw=subprocess.check_output(['git','-C',str(repo),'ls-tree','-r','-z',commit,'--',prefix])
    got={}
    for record in raw.split(b'\0'):
        if not record: continue
        meta,path=record.split(b'\t',1)
        mode,kind,blob=meta.decode().split()
        assert kind=='blob' and mode=='100644'
        relative=path.decode().removeprefix(prefix)
        assert relative in expected
        data=expected[relative].read_bytes()
        assert hashlib.sha1(f'blob {len(data)}\0'.encode()+data).hexdigest()==blob,relative
        got[relative]=blob
    assert set(got)==set(expected)


def main():
    records=sys.argv[1]
    assert re.fullmatch(r'[0-9a-f]{40}',records)
    expected={str(p.relative_to(SOURCE)):p for p in SOURCE.rglob('*') if p.is_file()}
    assert len(expected)==299 and not DEST.exists()
    verify_tree(MAIN,records,'briefs/pass-shelat-ch5-8/fills/cleanup-part2/issued-r1/',expected)
    assert git(EXCHANGE,'branch','--show-current')==BRANCH
    assert not git(EXCHANGE,'diff','--cached','--name-only') and not git(EXCHANGE,'diff','--name-only')
    before={}
    raw=subprocess.check_output(['git','-C',str(EXCHANGE),'ls-files','--others','--exclude-standard','-z'])
    for name in raw.decode().split('\0'):
        if name: before[name]=sha(EXCHANGE/name)
    mutate('pull','--rebase','origin',BRANCH)
    assert not DEST.exists()
    for relative,source in expected.items():
        target=DEST/relative
        target.parent.mkdir(parents=True,exist_ok=True)
        target.write_bytes(source.read_bytes())
        assert sha(target)==sha(source)
    paths=sorted(PREFIX+r for r in expected)
    mutate('add','--',*paths)
    assert set(git(EXCHANGE,'diff','--cached','--name-only').splitlines())==set(paths)
    # --only prevents a concurrent unrelated staging action entering this commit.
    mutate('commit','--only','-m','Stage cleanup part 2 Claude fill r1','--',*paths)
    mutate('pull','--rebase','origin',BRANCH)
    head=git(EXCHANGE,'rev-parse','HEAD')
    verify_tree(EXCHANGE,head,PREFIX,expected)
    for path,digest in before.items(): assert sha(EXCHANGE/path)==digest,path
    mutate('push','origin',BRANCH)
    receipt={'status':'STAGED_FOR_USER_DISPATCH_NOT_DISPATCHED',
             'recorded_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
             'records_commit':records,'exchange_commit':head,'source_ancestor':'1aa5506f58f77c215e56d24311ec33bd931cacf1',
             'files':len(expected),'raw_git_blob_and_disk_bytes_equal':True,
             'sha256sums_sha256':sha(SOURCE/'SHA256SUMS'),
             'other_local_untracked_preserved':before,
             'other_tracked_files_edited_by_maintainer':False,'worker':'Claude'}
    (PREP/'stage-exchange-r1.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:receipt[k] for k in ['status','records_commit','exchange_commit','files','sha256sums_sha256']},indent=2))


if __name__=='__main__': main()
