"""Snapshot an immutable assigned exchange subtree; never execute received code."""
from pathlib import Path, PurePosixPath
import datetime
import hashlib
import json
import re
import subprocess
import sys
import zipfile

ROOT=Path(__file__).resolve().parent
EXCHANGE=Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-exchange')
MAIN=EXCHANGE.parent/'tcslib-pass-shelat-ch2-4'
PREFIX='inbox/fills/cleanup-part2/'


def sha(data):return hashlib.sha256(data).hexdigest()
def git(*args):return subprocess.check_output(['git','-C',str(EXCHANGE),*args])


def main():
    label,requested=sys.argv[1:]
    assert re.fullmatch(r'(?:cp[0-9]+|partial-r[0-9]+)',label)
    revision=git('rev-parse',requested+'^{commit}').decode().strip()
    assert re.fullmatch(r'[0-9a-f]{40}',revision)
    out=ROOT/label
    out.mkdir(exist_ok=False)
    entries={}
    for record in git('ls-tree','-r','-z',revision,'--',PREFIX).split(b'\0'):
        if not record:continue
        meta,name=record.split(b'\t',1)
        mode,kind,blob=meta.decode().split()
        assert mode in ['100644','100755'] and kind=='blob'
        name=name.decode(); assert name.startswith(PREFIX)
        relative=name[len(PREFIX):]; parts=PurePosixPath(relative).parts
        assert parts and not relative.startswith('/') and '..' not in parts
        assert relative not in entries
        entries[relative]={'git_blob':blob,'git_mode':mode}
    assert entries and len({s.casefold() for s in entries})==len(entries)
    archive=out/'received.zip'
    with archive.open('wb') as target:
        subprocess.run(['git','-C',str(EXCHANGE),'archive','--format=zip',revision,'--',PREFIX],stdout=target,check=True)
    snapshot=out/'payload'; snapshot.mkdir()
    rows=[]
    with zipfile.ZipFile(archive) as z:
        actual={}
        for info in z.infolist():
            if info.is_dir():continue
            assert info.filename.startswith(PREFIX)
            relative=info.filename[len(PREFIX):]
            assert relative in entries and relative not in actual
            data=z.read(info)
            assert hashlib.sha1(f'blob {len(data)}\0'.encode()+data).hexdigest()==entries[relative]['git_blob']
            target=snapshot/relative; target.parent.mkdir(parents=True,exist_ok=True)
            target.write_bytes(data)
            actual[relative]=data
            rows.append({'path':relative,'bytes':len(data),'sha256':sha(data),**entries[relative]})
        assert set(actual)==set(entries)
    # Keep the received manifest untouched, including its conventional ./ prefix.
    supplied={}; issues=[]
    for line in actual['PAYLOAD-SHA256SUMS'].decode().splitlines():
        digest,relative=line.split('  ',1)
        relative=PurePosixPath(relative).as_posix()
        assert relative not in supplied and re.fullmatch(r'[0-9a-f]{64}',digest)
        supplied[relative]=digest
        if relative not in actual or sha(actual[relative])!=digest:issues.append('Checksum mismatch: '+relative)
    missing=sorted(set(actual)-{'PAYLOAD-SHA256SUMS'}-set(supplied))
    extra=sorted(set(supplied)-set(actual))
    if missing:issues.append('Manifest omissions: '+repr(missing))
    if extra:issues.append('Manifest extra paths: '+repr(extra))
    for name in ['REPORT.md','PAYLOAD-SHA256SUMS']:(out/name).write_bytes(actual[name])
    owned=set((MAIN/'briefs/pass-shelat-ch5-8/fills/cleanup-part2/issued-r1/inputs/owned-files.txt').read_text().splitlines())
    src={p.removeprefix('src/') for p in actual if p.startswith('src/')}
    meta={'status':'IMMUTABLE_INTAKE_ONLY_REVIEW_PENDING',
        'recorded_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'delivery_commit':revision,'assigned_subtree':PREFIX,'label':label,
        'actual_route':'Claude Git commit on the exchange; maintainer Git archive, not a worker-uploaded ZIP',
        'commit_metadata':git('show','--no-patch','--format=%H%n%P%n%cI%n%s',revision).decode(),
        'files':len(rows),'bytes':sum(r['bytes'] for r in rows),'archive_sha256':sha(archive.read_bytes()),
        'report_sha256':sha(actual['REPORT.md']),'supplied_manifest_sha256':sha(actual['PAYLOAD-SHA256SUMS']),
        'supplied_manifest_rows':len(supplied),'payload_checksum_issues':issues,
        'source_snapshots':len(src),'source_missing_owned':sorted(owned-src),'source_outside_owned':sorted(src-owned),
        'patches':sorted(p for p in actual if p.startswith('patches/')),
        'received_programs_executed':False,'native_checks_performed':False,
        'review_limit':'Raw Git/ZIP/manifest/source-set integrity only; no proof acceptance, source application or worker claim adopted.'}
    (out/'files.json').write_text(json.dumps(rows,indent=2)+'\n')
    (out/'intake.json').write_text(json.dumps(meta,indent=2)+'\n')
    (out/'SNAPSHOT-COMPLETE').write_text(revision+'\n')
    print(json.dumps({k:meta[k] for k in ['label','delivery_commit','files','bytes','archive_sha256','report_sha256','source_snapshots','payload_checksum_issues']},indent=2))


if __name__=='__main__':main()
