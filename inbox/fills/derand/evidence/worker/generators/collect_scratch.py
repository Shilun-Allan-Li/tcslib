"""Preserve all worker scratch inputs/prototypes without copying clones or packages."""
import hashlib
import json
from pathlib import Path
import shutil

scratch = Path('/private/tmp/derand-worker')
proof = Path('/Users/seyoonr/.codex/worktrees/derand-proof/tcslib-exchange')
out = proof / 'evidence/scratch'
out.mkdir(exist_ok=True)
paths = [p for p in scratch.iterdir() if p.is_file()]
for name in ['header-test', 'SR-02-proposal']:
    paths.extend(p for p in (scratch / name).rglob('*') if p.is_file())
rows = []
for source in sorted(paths):
    assert not source.is_symlink()
    relative = source.relative_to(scratch)
    target = out / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(source, target)
    rows.append(dict(original=str(source), delivered='worker/scratch/' + relative.as_posix(),
                     sha256=hashlib.sha256(target.read_bytes()).hexdigest()))
(out / 'inventory.json').write_text(json.dumps(rows, indent=2) + '\n')
(out / 'README.md').write_text(
    '# Scratch provenance\n\n'
    'This snapshot preserves every top-level worker scratch file, the header-test control,\n'
    'and the complete unaccepted SR-02 prototype. These are historical development material,\n'
    'not additional source changes. The accepted source is exclusively `src/` and the patches.\n'
    'Clones, package trees, issued inputs (preserved separately), and generated delivery\n'
    'payloads are excluded. All raw verification logs stay in their original evidence roots.\n'
    'The inventory gives original absolute paths and SHA256 values. Later delivery-only\n'
    'generators are also preserved in `worker/generators/`.\n')
print(f'SCRATCH PROVENANCE PASS: {len(rows)} source/prototype/tool files preserved')
