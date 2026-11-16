#!/usr/bin/env python3
"""Count both Lean diagnostic forms in every preserved development check."""
import json
from pathlib import Path
import re
root = Path('evidence/subagents/b')
error = re.compile(r'^\S+\.lean:\d+:\d+: error[:(]', re.M)
fixture = 'first.lean:1:2: error: deliberate\nsecond.lean:3:4: error(lean.unknownIdentifier): deliberate\n'
(root / 'error-counter-fixture.log').write_text(fixture)
assert len(error.findall(fixture)) == 2
rows = []
for pattern in ['runwithhost-*.log', 'decryption-*.log', 'firsttagged-*.log',
                'evalgate-*.log', 'garbledrun-*.log', 'bobtables-*.log']:
    for path in sorted(root.glob(pattern)):
        text = path.read_text()
        rss = re.search(r'^\s*(\d+)\s+maximum resident set size', text, re.M)
        rows.append(dict(log=str(path), exit=1 if 'FAIL(' in text else 0,
                         errors=len(error.findall(text)),
                         warnings=len(re.findall(r'^\S+\.lean:\d+:\d+: warning:', text, re.M)),
                         max_rss_bytes=int(rss[1]) if rss else None))
(root / 'development-results.json').write_text(json.dumps(rows, indent=2) + '\n')
(root / 'error-counter-check.txt').write_text('both forms counted: 2/2\n')
print(json.dumps(rows, indent=2))
