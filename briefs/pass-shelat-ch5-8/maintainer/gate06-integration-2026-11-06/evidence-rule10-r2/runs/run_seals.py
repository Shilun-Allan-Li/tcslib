"""Run frozen Gate06 whole-file seals serially, retaining source failures.

Usage: python3 -I run_seals.py <evidence-rule10-dir>
Setup/harness failures stop the survey. Source failures are recorded for repair,
never silently counted as passing or excluded.
"""
from pathlib import Path
import hashlib
import importlib.util
import json
import re
import subprocess
import sys

r, e = Path.cwd(), Path(sys.argv[1]).resolve()
m = json.loads((e / 'seal-manifest.json').read_text())
assert subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip() == m['library_verification']['head']
bs_path = r / '.lake/ps-maintainer/gate06/build_seals.py'
spec = importlib.util.spec_from_file_location('seal_builder', bs_path)
bs = importlib.util.module_from_spec(spec);spec.loader.exec_module(bs)
decl = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec)\s+)*(theorem|lemma|def|instance|structure|inductive|abbrev|class|opaque|axiom|example)\s*([^\s(:{\[]*)")
out = e / 'runs'
out.mkdir(exist_ok=True)
(out / 'run_seals.py').write_bytes(Path(__file__).read_bytes())
assert not (out / 'survey-summary.json').exists()
records=[]
for p in m['probes']:
    source = (r / p['source']).read_bytes()
    assert hashlib.sha256(source).hexdigest() == p['source_sha256']
    probe = Path(p['probe_path']).read_bytes()
    assert hashlib.sha256(probe).hexdigest() == p['probe_sha256']
    assert probe == Path(p['saved_source']).read_bytes()
    label = 'pilot-PRFMAC' if p['module']=='TCSlib.Cryptography.Authentication.PRFMAC' else p['label']
    result_path = out / (label+'.json')
    if not result_path.exists():
        subprocess.run(['python3','-I',str(r/'.lake/ps-maintainer/gate06/check_probe.py'),str(out),p['probe_module'],label],check=False)
    result = json.loads(result_path.read_text())
    assert result['source_sha256']==p['probe_sha256'] and result['source_unchanged']
    text=(out/(label+'.log')).read_text()
    installed=re.findall(r'G06-SEAL label='+re.escape(p['label'])+r' requested=(\d+) active=(\d+) already_irreducible=(\d+) verified=(\d+)',text)
    expected=(str(p['requested_count']),str(p['collector_active_candidate_count']),str(p['collector_irreducible_count']),str(p['requested_count']))
    assert installed==[expected],(p['module'],'invalid installation',installed,expected)
    end=re.findall(r'G06-SEAL-END label='+re.escape(p['label'])+r' requested=(\d+) verified=(\d+)',text)
    assert end==[(str(p['requested_count']),str(p['requested_count']))],(p['module'],'invalid EOF verification',end)
    errors=[int(n) for n in re.findall(r'\.lean:(\d+):\d+: error:',text)]
    inverse={row['probe_line']:row['source_line'] for row in p['source_to_probe_lines']}
    assert all(n in inverse for n in errors),(p['module'],'harness diagnostic',errors)
    assert (result['rc']==0 and result['fresh_nonempty_object']) if not errors else result['rc']!=0
    code=bs.blank_comments_strings(source.decode()).splitlines()
    starts=[(i+1,match.group(1),match.group(2)) for i,line in enumerate(code) if (match:=decl.match(line))]
    touched={v['normalized_spelling'] for v in p['touched_source_names']}
    existed=subprocess.run(['git','cat-file','-e',m['library_verification']['base']+':'+p['source']],capture_output=True).returncode==0
    details=[]
    for n in errors:
        ln=inverse[n]
        own=max((s for s in starts if s[0]<=ln),default=(0,'unknown','unknown'))
        details.append({'probe_line':n,'source_line':ln,'declaration_start':own[0],'kind':own[1],
                        'source_name':own[2],'new_file':not existed,
                        'touched_by_source_name':not existed or own[2].removeprefix('_root_.') in touched,
                        'classification':'SOURCE_FAILURE_REQUIRES_REVIEW'})
    record={'module':p['module'],'label':label,'valid_harness':True,'requested':p['requested_count'],
            'active':p['collector_active_candidate_count'],'already_irreducible':p['collector_irreducible_count'],
            'rc':result['rc'],'errors':details,'source_failure':bool(errors),'result':result,
            'limit':'Touched flags are preliminary source-name matches. Every failure requires manual source/base classification; none is excluded here.'}
    records.append(record)
    (out/'survey-progress.json').write_text(json.dumps(records,indent=2)+'\n')
    print(f"SEAL {len(records)}/{len(m['probes'])} {p['module']} errors={len(errors)}",flush=True)
summary={'head':m['library_verification']['head'],'base':m['library_verification']['base'],
         'modules':len(records),'results':records,'passing_modules':sum(not v['source_failure'] for v in records),
         'failing_modules':sum(v['source_failure'] for v in records),'harness_failures':0,
         'touched_failure_attestation':'NOT_YET_RECONCILED','limit':'Initial frozen survey, not merge clearance. All failures await classification/repair.'}
(out/'survey-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print('DONE initial whole-file seal survey',flush=True)
