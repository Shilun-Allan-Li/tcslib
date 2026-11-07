"""Correct two owner names; preserve the first closed pack and all frozen data."""
from pathlib import Path
import difflib
import hashlib
import json
import shutil

PREP=Path(__file__).resolve().parent
OLD=PREP/'issue-pack-r1'
NEW=PREP/'issue-pack-r2'
EVIDENCE=PREP/'issue-revision-r2'
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    assert sha(OLD/'SHA256SUMS')=='a289a58e622137c77554ba529424f5a9290f73658189402a348b544b1c9624c1'
    assert not NEW.exists() and not EVIDENCE.exists()
    shutil.copytree(OLD,NEW)
    EVIDENCE.mkdir()
    before=(OLD/'brief.md').read_text()
    after=before
    replacements={
        '`Sampling.two_pow_size_le_two_mul`':'`TCSlib.Cryptography.two_pow_size_le_two_mul` (in `Asymptotic/Sampling.lean`)',
        'public Sampling.abs_uexp_sub_le':'public `TCSlib.Cryptography.abs_uexp_sub_le` in `Asymptotic/Sampling.lean`'}
    for old,new in replacements.items():
        assert after.count(old)==1,(old,after.count(old))
        after=after.replace(old,new)
    (NEW/'brief.md').write_text(after)
    manifest=json.loads((NEW/'PACK-MANIFEST.json').read_text())
    for row in manifest['files']:
        path=NEW/row['path']
        if row['path']=='brief.md':
            row['bytes']=path.stat().st_size
            row['sha256']=sha(path)
        else:
            assert row['bytes']==path.stat().st_size and row['sha256']==sha(path)
    (NEW/'PACK-MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
    files=sorted(p for p in NEW.rglob('*') if p.is_file() and p.name!='SHA256SUMS')
    (NEW/'SHA256SUMS').write_text(''.join(sha(p)+'  '+str(p.relative_to(NEW))+'\n' for p in files))
    changed=[]
    for path in sorted(OLD.rglob('*')):
        if path.is_file() and sha(path)!=sha(NEW/path.relative_to(OLD)):
            changed.append(str(path.relative_to(OLD)))
    assert changed==['PACK-MANIFEST.json','SHA256SUMS','brief.md']
    for name in changed: (EVIDENCE/('previous-'+name)).write_bytes((OLD/name).read_bytes())
    (EVIDENCE/'owner-name-corrections.diff').write_text(''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='first-reviewed/brief.md',tofile='final/brief.md')))
    report={'status':'TWO_OWNER_NAME_PROSE_CORRECTIONS_NO_SCOPE_OR_TOOL_CHANGE',
        'source_ancestor':'1aa5506f58f77c215e56d24311ec33bd931cacf1',
        'changed_pack_files':changed,'other_pack_files_byte_identical':296,
        'old_checksum_sha256':sha(OLD/'SHA256SUMS'),'new_checksum_sha256':sha(NEW/'SHA256SUMS'),
        'old_pack_manifest_sha256':sha(OLD/'PACK-MANIFEST.json'),'new_pack_manifest_sha256':sha(NEW/'PACK-MANIFEST.json'),
        'old_brief_sha256':sha(OLD/'brief.md'),'new_brief_sha256':sha(NEW/'brief.md'),
        'frozen_inputs_tools_exceptions_native_limits_unchanged':True}
    (EVIDENCE/'revision.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__':main()
