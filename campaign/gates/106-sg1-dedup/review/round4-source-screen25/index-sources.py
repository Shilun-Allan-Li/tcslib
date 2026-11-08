"""Parser/index only: executes the trusted v3 prefix, never its tiling loop."""
from pathlib import Path
import hashlib, json, sys

OUT = Path(__file__).resolve().parent
ROOT = Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4')
capture = json.loads((OUT / 'capture.json').read_text())
tool = ROOT / 'scripts/copy-text-screen-v3.py'
source = tool.read_text()
assert hashlib.sha256(source.encode()).hexdigest() == capture['tools']['scripts/copy-text-screen-v3.py']
marker = 'pairs = []; total = 0'
assert source.count(marker) == 1
prefix = source.split(marker)[0]
for side in ['base', 'head']:
    sys.argv = [str(tool), capture['temporary_trees'][side], *capture['population']]
    namespace = {}
    exec(compile(prefix, str(tool) + ':parser-only', 'exec'), namespace)
    rows = []
    for (filepos, name, kind, body, _) in namespace['decls']:
        path, offset = filepos
        rows.append(dict(label=namespace['label'](path) + '::' + name,
                         path=path, offset=offset, name=name, kind=kind,
                         normalized_body=body, body_chars=len(body)))
    (OUT / (side + '-index.json')).write_text(json.dumps(rows, indent=2) + '\n')
    print(side, len(rows), flush=True)
