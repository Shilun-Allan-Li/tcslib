"""Run one root-coordinated S2 module with exact source/object evidence.

Usage: python3 -I s2_native.py WORKTREE EVIDENCE MODULE LABEL [compare-copy]
"""
from pathlib import Path
import datetime
import hashlib
import json
import os
import re
import subprocess
import sys
import time

r, e, module, label = Path(sys.argv[1]), Path(sys.argv[2]), sys.argv[3], sys.argv[4]
compare = len(sys.argv) > 5 and sys.argv[5] == 'compare-copy'
e.mkdir(parents=True, exist_ok=True)
log = e / (label + '.log')
assert not log.exists()
tree = Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/.lake/ps-maintainer/oleans-s2-final')
obj = tree / (module + '.olean')
sha = lambda raw: hashlib.sha256(raw).hexdigest()
raw = (r / (module + '.lean')).read_bytes()
old = sha(obj.read_bytes()) if obj.is_file() else None
head = subprocess.check_output(['git','-C',str(r),'rev-parse','HEAD'],text=True).strip()
env = os.environ.copy()
env['PATH'] = str(Path.home()/'.elan/bin') + os.pathsep + env['PATH']
env['TCSLIB_OLEANS'] = str(tree)
clock = lambda: datetime.datetime.now(datetime.timezone.utc).isoformat()
start, tick = clock(), time.monotonic()
with log.open('w') as f:
    f.write('START '+start+'\nHEAD '+head+'\nSOURCE_SHA256 '+sha(raw)+'\n')
    f.flush()
    p=subprocess.Popen(['/usr/bin/time','-l','bash','scripts/lean_check_tree.sh',module],cwd=r,env=env,stdout=f,stderr=subprocess.STDOUT)
    (e/(label+'.pid')).write_text(str(p.pid)+'\n')
    rc=p.wait()
    end=clock()
    f.write('\nEND '+end+' RC '+str(rc)+'\n')
text=log.read_text()
errors=len(re.findall(r'\.lean:\d+:\d+: error(?:\([^\n)]*\))?:',text))
rss=re.search(r'(\d+)\s+maximum resident set size',text)
new=sha(obj.read_bytes()) if rc==0 and obj.is_file() and obj.stat().st_size else None
result={'head':head,'module':module,'label':label,'start':start,'end':end,'rc':rc,
        'error_diagnostics':errors,'elapsed_seconds':round(time.monotonic()-tick,3),
        'source_sha256':sha(raw),'source_unchanged':(r/(module+'.lean')).read_bytes()==raw,
        'fresh_nonempty_object':new is not None,'before_object_sha256':old,'object_sha256':new,
        'compare_copy_required':compare,'reproduces_copied_object':old is not None and old==new,
        'peak_rss_bytes':int(rss.group(1)) if rss else None,'olean_tree':str(tree)}
(e/(label+'.json')).write_text(json.dumps(result,indent=2)+'\n')
(e/'s2_native.py').write_bytes(Path(__file__).read_bytes())
print(json.dumps(result),flush=True)
assert rc==0 and errors==0 and new is not None and result['source_unchanged']
if compare:
    assert old==new, 'Representative native rebuild differs from copied object'
