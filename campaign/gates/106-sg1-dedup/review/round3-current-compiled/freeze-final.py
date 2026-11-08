"""Verify immutable baseline and six successful stages, then freeze final comparison."""
from pathlib import Path
import base64
import datetime
import gzip
import hashlib
import json

OUT=Path(__file__).resolve().parent
assert not (OUT/'MANIFEST.json').exists()
baseline=OUT/'BASE-MANIFEST.json'
assert hashlib.sha256(baseline.read_bytes()).hexdigest()=='a16b95f4fd3154fbe53850b005373baa06451198858c1be3b77c75a406de76c0'
manifest=json.loads(baseline.read_text())
for row in manifest['files']:
    p=OUT/row['path'];data=p.read_bytes()
    assert len(data)==row['bytes'] and hashlib.sha256(data).hexdigest()==row['sha256'],row['path']
for label in ['Base','Head']:
    for version in ['census-v1','types-v1','ciattrs-v1']:
        stem=label+'-'+version
        run=json.loads((OUT/(stem+'-run.json')).read_text())
        assert run['exit']==run['errors']==run['warnings']==0
        assert run['owner_artifacts_unchanged'] and run['input_still_exact']
        data=(OUT/(stem+'.out.gz.b64')).read_bytes()
        assert hashlib.sha256(data).hexdigest()==run['base64_sha256']
        compressed=base64.decodebytes(data)
        assert hashlib.sha256(compressed).hexdigest()==run['gzip_sha256']
        raw=gzip.decompress(compressed)
        assert hashlib.sha256(raw).hexdigest()==run['raw_utf8_sha256'] and len(raw)==run['raw_utf8_bytes']
        raw.decode('utf-8')
comparison=json.loads((OUT/'comparison-staged.json').read_text())
assert comparison['base_counts']['total']==7101 and comparison['head_counts']['total']==7065
assert comparison['base_counts']['nonprivate']==comparison['head_counts']['nonprivate']==1351
assert not any(comparison['nonprivate_common_field_changes'].values())
assert not comparison['axiom_set_growth'] and not comparison['added_nonstandard_axioms'] and not comparison['nonstandard_axiom_regressions']
assert comparison['nonstandard_name_sets_equal'] and not comparison['simp_rule_changes']
context=json.loads((OUT/'context.json').read_text())
source_checks=[]
for rel,expected in context['source_pins']['head'].items():
    p=Path(context['worktree'])/rel
    actual=hashlib.sha256(p.read_bytes()).hexdigest()
    assert actual==expected['sha256']
    source_checks.append(dict(path=rel,sha256=actual))
(OUT/'final-verification.json').write_text(json.dumps(dict(at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),baseline_payloads_unchanged=len(manifest['files']),six_successful_uncapped_stages_verified=True,source_checks=source_checks,no_nonprivate_metadata_drift=True,no_axiom_set_growth=True,constant_value_bodies_omitted=True,no_source_or_snapshot_writes=True),indent=2)+'\n')
files=[]
for p in sorted(OUT.rglob('*')):
    assert not p.is_symlink()
    if p.is_file():
        assert p.suffix!='.lean'
        data=p.read_bytes();data.decode('utf-8')
        files.append(dict(path=p.relative_to(OUT).as_posix(),bytes=len(data),sha256=hashlib.sha256(data).hexdigest()))
result=dict(status='Frozen current MAC4 to MSG5 original-nine-owner compiled comparison; no external gate clearance',at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),base=context['base'],head=context['head'],files=files)
data=(json.dumps(result,indent=2)+'\n').encode();(OUT/'MANIFEST.json').write_bytes(data)
print(json.dumps(dict(payloads=len(files),bytes=sum(x['bytes'] for x in files),manifest_sha256=hashlib.sha256(data).hexdigest()),indent=2))
