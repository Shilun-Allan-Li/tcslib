"""Resume frozen Gate06 seals with retry-only harnesses and coded diagnostics.

Usage: python3 -I run_seals_v3.py EVIDENCE RETRY_MANIFEST
Original valid attempts are reused by exact source fingerprint. Invalid attempts
remain intact. No exclusions, new axioms, or weakened seal-name sets are allowed.
"""
from pathlib import Path
import hashlib
import importlib.util
import json
import re
import subprocess
import sys

ERROR_RE = re.compile(r'\.lean:(\d+):(\d+): error(?:\(([^\n)]*)\))?:')
r, e, retry_path = Path.cwd(), Path(sys.argv[1]).resolve(), Path(sys.argv[2]).resolve()
sha = lambda raw: hashlib.sha256(raw).hexdigest()
original_raw = (e / 'seal-manifest.json').read_bytes()
m = json.loads(original_raw)
retry = json.loads(retry_path.read_text())
assert retry['original_manifest_sha256'] == sha(original_raw)
assert retry['library_verification'] == m['library_verification']
assert subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip() == m['library_verification']['head']
override = {p['module']:p for p in retry['probes']}
assert len(override) == len(retry['probes'])
assert set(override) <= {p['module'] for p in m['probes']}
bs_path = r / '.lake/ps-maintainer/gate06/build_seals.py'
spec = importlib.util.spec_from_file_location('seal_builder', bs_path)
bs = importlib.util.module_from_spec(spec);spec.loader.exec_module(bs)
decl = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec)\s+)*(theorem|lemma|def|instance|structure|inductive|abbrev|class|opaque|axiom|example)\s*([^\s(:{\[]*)")
out = e / 'runs-v3'
out.mkdir(exist_ok=True)
tool_save = out / 'run_seals_v3.py'
if tool_save.exists():
    assert tool_save.read_bytes() == Path(__file__).read_bytes()
else:
    tool_save.write_bytes(Path(__file__).read_bytes())
assert not (out / 'survey-summary.json').exists()
records=[]
for original in m['probes']:
    p = override.get(original['module'], original)
    for key in ('module','source','source_sha256','requested_names','requested_count','term_names',
                'collector_active_candidate_count','collector_irreducible_count'):
        assert p[key] == original[key], (p['module'], key)
    source = (r / p['source']).read_bytes()
    assert sha(source) == p['source_sha256']
    probe = Path(p['probe_path']).read_bytes()
    assert sha(probe) == p['probe_sha256']
    assert probe == Path(p['saved_source']).read_bytes()
    if p is original:
        label = 'pilot-PRFMAC' if p['module']=='TCSlib.Cryptography.Authentication.PRFMAC' else p['label']
        attempt_dir = e / 'runs'
        assert (attempt_dir / (label+'.json')).exists(), 'Only valid completed originals may be reused'
    else:
        label = p['label']
        attempt_dir = out
        if not (out / (label+'.json')).exists():
            subprocess.run(['python3','-I',str(r/'.lake/ps-maintainer/gate06/check_probe_v2.py'),
                            str(out),p['probe_module'],label],check=False)
    result_path = attempt_dir / (label+'.json')
    result = json.loads(result_path.read_text())
    assert result['source_sha256']==p['probe_sha256'] and result['source_unchanged']
    log_path = attempt_dir / (label+'.log')
    text=log_path.read_text()
    installed=re.findall(r'G06-SEAL label='+re.escape(p['label'])+r' requested=(\d+) active=(\d+) already_irreducible=(\d+) verified=(\d+)',text)
    expected=(str(p['requested_count']),str(p['collector_active_candidate_count']),str(p['collector_irreducible_count']),str(p['requested_count']))
    assert installed==[expected],(p['module'],'invalid installation',installed,expected)
    end=re.findall(r'G06-SEAL-END label='+re.escape(p['label'])+r' requested=(\d+) verified=(\d+)',text)
    assert end==[(str(p['requested_count']),str(p['requested_count']))],(p['module'],'invalid EOF verification',end)
    errors=[(int(n),int(c),code or None) for n,c,code in ERROR_RE.findall(text)]
    inverse={row['probe_line']:row['source_line'] for row in p['source_to_probe_lines']}
    assert all(n in inverse for n,_,_ in errors),(p['module'],'harness diagnostic',errors)
    assert (result['rc']==0 and result['fresh_nonempty_object']) if not errors else result['rc']!=0
    code=bs.blank_comments_strings(source.decode()).splitlines()
    starts=[(i+1,match.group(1),match.group(2)) for i,line in enumerate(code) if (match:=decl.match(line))]
    touched={v['normalized_spelling'] for v in p['touched_source_names']}
    existed=subprocess.run(['git','cat-file','-e',m['library_verification']['base']+':'+p['source']],capture_output=True).returncode==0
    details=[]
    for n,col,error_code in errors:
        ln=inverse[n]
        own=max((s for s in starts if s[0]<=ln),default=(0,'unknown','unknown'))
        details.append({'probe_line':n,'probe_column':col,'error_code':error_code,'source_line':ln,
                        'declaration_start':own[0],'kind':own[1],'source_name':own[2],'new_file':not existed,
                        'touched_by_source_name':not existed or own[2].removeprefix('_root_.') in touched,
                        'classification':'SOURCE_FAILURE_REQUIRES_REVIEW'})
    record={'module':p['module'],'label':label,'valid_harness':True,'requested':p['requested_count'],
            'active':p['collector_active_candidate_count'],'already_irreducible':p['collector_irreducible_count'],
            'rc':result['rc'],'errors':details,'source_failure':bool(errors),'result':result,
            'attempt_result':str(result_path),'attempt_log':str(log_path),
            'parsed_error_diagnostics':len(errors),'diagnostic_parser':ERROR_RE.pattern,
            'original_result_count_preserved':result['error_diagnostics'],
            'limit':'Touched flags are preliminary source-name matches; every failure needs manual source/base classification.'}
    records.append(record)
    (out/'survey-progress.json').write_text(json.dumps(records,indent=2)+'\n')
    print(f"SEAL-V3 {len(records)}/{len(m['probes'])} {p['module']} errors={len(errors)}",flush=True)
summary={'head':m['library_verification']['head'],'base':m['library_verification']['base'],
         'modules':len(records),'results':records,'passing_modules':sum(not v['source_failure'] for v in records),
         'failing_modules':sum(v['source_failure'] for v in records),'harness_failures':0,
         'earlier_invalid_attempts_preserved':True,'touched_failure_attestation':'NOT_YET_RECONCILED',
         'retry_manifest':str(retry_path),'limit':'Initial frozen survey; not merge clearance. All failures await classification/repair.'}
(out/'survey-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print('DONE initial whole-file seal survey v3',flush=True)
