"""Freeze this chat's completed interface-probe artifacts; no native execution."""
from pathlib import Path
import hashlib
import json
import re

PREP = Path(__file__).resolve().parent
NATIVE = Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/.lake/ps-maintainer/cleanup-part2-prep/native')
DEST = PREP / 'preship-r1/interface'
DEST.mkdir(parents=True, exist_ok=False)
copied = []
for attempt, sub in [('attempt-1', ''), ('attempt-2', 'r2')]:
    target = DEST/attempt
    target.mkdir()
    source = NATIVE/sub
    for name in ['InterfaceProbe.lean', 'InterfaceProbe.log', 'InterfaceProbe.pid', 'InterfaceProbe.json', 'provenance.json']:
        path = source/name
        out = target/(name.removesuffix('.lean')+'.source.txt' if name.endswith('.lean') else name)
        out.write_bytes(path.read_bytes())
        copied.append({'path': str(out.relative_to(DEST)), 'bytes': out.stat().st_size,
                       'sha256': hashlib.sha256(out.read_bytes()).hexdigest()})
first = json.loads((DEST/'attempt-1/InterfaceProbe.json').read_text())
second = json.loads((DEST/'attempt-2/InterfaceProbe.json').read_text())
errors = re.findall(r'\berror(?:\([^)]*\))?:', (DEST/'attempt-1/InterfaceProbe.log').read_text())
assert first['return_code'] == 1 and not first['fresh_nonempty_object'] and len(errors) == 3
assert second['return_code'] == 0 and second['error_diagnostics'] == 0 and second['fresh_nonempty_object']
assert len(re.findall(r'^#check ', (DEST/'attempt-2/InterfaceProbe.source.txt').read_text(), re.M)) == 17
(DEST/'initial-error-count-correction.json').write_text(json.dumps({
    'attempt': 'attempt-1', 'original_receipt_preserved': True,
    'reported_error_diagnostics': first['error_diagnostics'], 'actual_error_diagnostics': len(errors),
    'reason': 'Initial counter matched error: but not error(lean.unknownIdentifier):. Return code already correctly recorded failure and no object.',
    'disposition': 'Invalid namespace spellings corrected in attempt-2; no initial native success claimed.'}, indent=2)+'\n')
(DEST/'REPORT.md').write_text('''# Existing-interface preflight

The successful second attempt checked 17 existing interfaces and two term-proof
reader applications against this chat's source/object-verified post-S2 tree.
It exited 0 with zero errors, a fresh nonempty object, 9.736 seconds elapsed and
2,328,952,832 bytes peak RSS on macOS. The two theorem axiom outputs are respectively
standard-only and axiom-free. The provenance snapshot verifies 115 imported local
source/object/direct-prerequisite records; it is not another cold bootstrap.

The initial attempt failed on three namespace spellings and produced no object.
Its original JSON underestimated diagnostic count because the first parser missed
`error(lean.unknownIdentifier):`; the separate correction records all three. The
initial return code and failure status were correct and remain unchanged.

The source ancestor is 1aa5506f58f77c215e56d24311ec33bd931cacf1. This checks only
selected existing reuse routes. New block/decoder/average/strategy interfaces are
assigned work, not APIs proved by this preflight. No cleanup implementation,
full baseline/root/Checks replay, Rule10 clearance or worker completion is inferred.
All copied source is stored as .source.txt, without changing campaign Lean files.

**Ready to run — selected existing interface routes passed; full worker verification remains.**
''')
for path in sorted(DEST.rglob('*')):
    if path.is_file() and str(path.relative_to(DEST)) not in {r['path'] for r in copied}:
        copied.append({'path': str(path.relative_to(DEST)), 'bytes': path.stat().st_size,
                       'sha256': hashlib.sha256(path.read_bytes()).hexdigest()})
(DEST/'MANIFEST.json').write_text(json.dumps({'status': 'ARCHIVED_NATIVE_INTERFACE_PREFLIGHT',
    'ancestor': '1aa5506f58f77c215e56d24311ec33bd931cacf1', 'files': copied}, indent=2)+'\n')
print(json.dumps({'files': len(copied), 'failed_attempts_retained': 1,
                  'successful_attempts': 1, 'manifest_sha256': hashlib.sha256((DEST/'MANIFEST.json').read_bytes()).hexdigest()}))
