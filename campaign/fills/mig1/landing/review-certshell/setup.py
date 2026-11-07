"""Capture only the owned CertShell source and create a private complete read-only baseline overlay."""
from pathlib import Path
import datetime
import hashlib
import json
import os
import tempfile
OUT=Path(__file__).resolve().parent
ROOT=OUT.parents[4]
SCRATCH=Path(os.environ['TCSLIB_SCRATCH'])
SOURCE=SCRATCH/'wt-epad/TCSlib/Complexity/TuringMachine/Build/CertShell.lean'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert not (OUT/'setup.json').exists()
(OUT/'CertShell-start.lean.txt').write_bytes(SOURCE.read_bytes())
overlay=Path(tempfile.mkdtemp(prefix='tcslib-certshell-overlay-',dir='/private/tmp'))
import shutil
shutil.copytree(SCRATCH/'oleans-mra2',overlay,copy_function=os.link,dirs_exist_ok=True,symlinks=True)
context=dict(at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),owned_source=str(SOURCE),source_sha256=sha(SOURCE),
             supplied_branch='lean/mig1-mega-landing',supplied_head='af3273f75d7602c079169f321e4536a58c7bb034',
             initial_disjoint_repairs='Maintainer reports four pre-existing ofCfg state-premise repairs in this file; source capture is exact received starting state.',
             worktree=str(SCRATCH/'wt-epad'),snapshot=str(SCRATCH/'oleans-mra2'),complete_private_overlay=str(overlay),
             overlay_method='Complete hard-linked copy; plain probes write no olean. Any future compiled output first removes target hard links.',
             source_file_count=1,no_git_commands=True)
(OUT/'setup.json').write_text(json.dumps(context,indent=2)+'\n')
print(json.dumps(context,indent=2))
