"""Run repository style mechanisms at the frozen final source; no Lean processes."""
from pathlib import Path
import collections
import hashlib
import importlib.util
import io
import json
import re
import subprocess
import sys
import tarfile

sys.dont_write_bytecode = True
r=Path.cwd();g=r/'.lake/ps-maintainer/gate06'
e=Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/evidence-style-final-r1')
prep=json.loads(Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/evidence-run/final-native-order-prep.json').read_text())
git=lambda *a:subprocess.check_output(['git','--no-optional-locks',*a])
assert git('rev-parse','HEAD').decode().strip()==prep['head']
assert not e.exists();e.mkdir()
base_dir=g/'style-base-final';base_dir.mkdir(exist_ok=False)
archive=git('archive','--format=tar',prep['base'],'--','TCSlib','TCSlib.lean')
with tarfile.open(fileobj=io.BytesIO(archive)) as saved:
    for p in saved.getmembers():
        if not p.name.endswith('.lean'):continue
        assert p.isfile() and '..' not in Path(p.name).parts and not Path(p.name).is_absolute()
        target=base_dir/p.name;target.parent.mkdir(parents=True,exist_ok=True)
        target.write_bytes(saved.extractfile(p).read())
tool=r/'scripts/style_lint.py'
spec=importlib.util.spec_from_file_location('final_repository_style',tool)
style=importlib.util.module_from_spec(spec);spec.loader.exec_module(style)
normalize=lambda s:re.sub(r'\b\d+ lines', '<count> lines',re.sub(r':\d+:',':<line>:',s))
rows=[]
for path in prep['changed_lean_files']:
    style.ROOT=r;head=style.lint(r/path)
    style.ROOT=base_dir;base=style.lint(base_dir/path) if (base_dir/path).exists() else []
    new=list((collections.Counter(map(normalize,head))-collections.Counter(map(normalize,base))).elements())
    rows.append({'file':path,'head':head,'base':base,'new_finding_keys':new,
                 'head_sha256':hashlib.sha256((r/path).read_bytes()).hexdigest(),
                 'base_exists':(base_dir/path).exists()})
style.ROOT=r
cmd=['python3','-I',str(tool),*prep['changed_lean_files']]
run=subprocess.run(cmd,cwd=r,capture_output=True,text=True)
(e/'style-head.log').write_text(run.stdout+run.stderr)
campaign=[]
for topic in ['Authentication','SecureComputation','Composability','Randomness']:
    for check8b in [False,True]:
        command=['python3','-I','scripts/campaign_style_lint.py','TCSlib/Cryptography/'+topic]+(['--check8b'] if check8b else [])
        done=subprocess.run(command,cwd=r,capture_output=True,text=True)
        label=topic+('-check8b' if check8b else '-plain')
        (e/(label+'.log')).write_text(done.stdout+done.stderr)
        campaign.append({'topic':topic,'check8b':check8b,'rc':done.returncode,'log':label+'.log'})
assert git('rev-parse','HEAD').decode().strip()==prep['head']
assert all(hashlib.sha256((r/v['file']).read_bytes()).hexdigest()==v['head_sha256'] for v in rows)
result={'head':prep['head'],'base':prep['base'],'changed_files':len(rows),'style_head_rc':run.returncode,
        'style_head_findings':sum(len(v['head']) for v in rows),
        'new_style_findings':sum(len(v['new_finding_keys']) for v in rows),'rows':rows,'campaign':campaign,
        'campaign_scope':'Four complete new prong directories, plain/check8b. Other changed files are covered by repository style comparison and source/API review; no all-library campaign-lint pass is asserted.'}
(e/'comparison.json').write_text(json.dumps(result,indent=2)+'\n')
for p in [Path(__file__),tool,r/'scripts/campaign_style_lint.py']:(e/p.name).write_bytes(p.read_bytes())
print(json.dumps({k:result[k] for k in ['head','changed_files','style_head_rc','style_head_findings','new_style_findings']}))
print(json.dumps({'campaign':campaign}))
