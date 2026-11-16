#!/usr/bin/env python3
"""Close the reviewed report draft only after exact-source proof checks have completed."""
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess

stage = Path('/private/tmp/sc-yao-final-stage')
ref = subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip()
assert ref == '6e7ef601ad9a05d5e26d09f32eadb9c17a4a6cbc'
sweep = json.loads(Path('evidence/final-publication-sweep-summary.json').read_text())
matrix = json.loads(Path('evidence/final-current-helper-seal-summary.json').read_text())
axioms = json.loads(Path('evidence/final-publication-security-audit-summary.json').read_text())
assert sweep['modules'] == 261 and sweep['current_sorry_declarations'] == 30
assert matrix['checks'] == 272 and matrix['all_pass']
assert axioms['stored_constants'] == 1490 and axioms['helper_stored_constants'] == 1110
commits = (stage / 'patches/COMMITS.tsv').read_text().splitlines()
assert len(commits) == 9 and all(s.endswith('\tnone') for s in commits[1:])
repro = (stage / 'evidence/patch-reproduction.log').read_text()
assert sum(s.startswith('REPRODUCED ') for s in repro.splitlines()) == 8
assert Path('evidence/interfaces/full-stored-signatures.md').is_file()
for name in ['source-inventory.json', 'source-signatures.md']:
    src = stage / 'evidence/interfaces' / name
    dst = Path('evidence/interfaces') / name
    if dst.exists():
        assert dst.read_bytes() == src.read_bytes()
    else:
        shutil.copyfile(src, dst)
text = Path('evidence/subagents/final-report-draft/REPORT.md').read_text()
text = re.sub(r'\*\*DRAFT — PENDING.*?delivered as final\.\n\n', '', text, count=1, flags=re.S)
a = text.index('The completed pre-documentation final sweep')
b = text.index('## Source, exports and frozen scope', a)
text = text[:a] + '''The final exact-source sweep passed all261modules, including the last documentation
revision. The admission comparison is32→30: exactly the two target admissions disappear.
All272current-source helper seals pass; four documentation reruns replace the four
superseded Garbling rows, with all276raw runs preserved. The final1490constant trace
confirms the table above. No proof code or declaration changed in the English sketch edit.

''' + text[b:]
text = text.replace('No sc-garble, #318 or sc-compose proof declaration is imported or consumed.',
    'No declaration added by the unmerged sc-garble, #318 or sc-compose deliveries is imported or consumed.')
text = text.replace('(`PENDING_CURRENT_SIGNATURE_EXPORT`)',
    '(`source-inventory.json`, `source-signatures.md`, `full-stored-signatures.md`)')
text = text.replace('The post-documentation trace refresh is `PENDING_GARBLING_POSTDOC_CHECKS`.',
    'The exact-source refresh passes in `evidence/final-publication-security-audit-summary.json`;\n'
    'its complete elaborated types are also exported in `evidence/interfaces/full-stored-signatures.md`.')
a = text.index('`PENDING_CURRENT_HELPER_MATRIX`:')
b = text.index('All24SY-3necessity controls', a)
text = text[:a] + '''The current-source matrix is272/272PASS:268unchanged-file rows plus the four exact-current
Garbling reruns. All68files have A/B×strict/coe coverage, zero errors in both forms and
fresh outputs, and reconstruct their current unsealed source byte-for-byte. All276raw runs
remain delivered, including the four superseded rows. The primary parallel batch verified
that all261imported artifacts stayed unchanged and every initial probe hash matched.
An observed exclusive-writer lock attempt was rejected while the shared readers were live.
Current normal checks and the full stored-constant trace pass after the documentation edit.

''' + text[b:]
text = text.replace('Its four-line English proof sketch', 'Its short English proof sketch')
text = text.replace('the exact-source postdoc checks remain explicitly pending above.',
                    'the exact-source post-documentation checks pass as recorded above.')
text = text.replace('current-source export hashes are `PENDING_CURRENT_SIGNATURE_EXPORT`.',
                    'current-source export hashes are in `evidence/interfaces/source-inventory.json`.')
text = text.replace('`PENDING_EXACT_MANIFESTS` includes',
                    'The top-level and evidence SHA256 manifest verification includes')
# Registry consumers distinguish real use from prospective reuse.
text = text.replace('Alice garbling; output decoding; garbled evaluator; simulator/reduction reconstruction.',
    'GarblingProgram.gatesWord_poly and BobProgram.output_poly consume readCircuit_poly; '
    'FakeProgram uses the same description recoder. decodeDescription_host packages that computation with the output word.')
text = text.replace('Bob evaluator; fake-garbling simulator; reduction reconstruction.',
    'GarbledRun.garbledRunWith_poly via BobProgram.output_poly and yaoHybrid_polyTime. '
    'The fake-view simulator and B1 slot-substitution reduction do not execute this evaluator.')
reuse = Path('evidence/subagents/final-reuse-locations/REPORT.md').read_text()
reuse = reuse[:reuse.index('No Lean command, package command')].strip()
reuse = reuse.replace('# Exact merged reuse locations', '### Exact pinned locations of compared and reused interfaces', 1)
where = text.index('## Hosts, promotion and reader requests (SY-4)')
text = text[:where] + reuse + '\n\n' + text[where:]
auth = Path('evidence/scope-request/execution-authorization.md').read_text()
auth = auth.replace('# Execution authorization (historical session record)',
                    '### Shared-wrapper execution authorization', 1)
where = text.index('## Dependency trace and axioms')
text = text[:where] + auth + '\n\n' + text[where:]
where = text.index('## Delivery, reproducibility and final closure')
text = text[:where] + '''## Delivery and reproducibility

The prepared payload contains all eight unsigned format-patches from the fixed issue base.
COMMITS.tsv records every hash, author/committer identity and date, and signing=none.
All eight hashes reproduced exactly with git am in a fresh own shared scratch clone using
those recorded values; see evidence/patch-reproduction.log. The final71source hashes and
width/line inventories are exported beside the full1490elaborated stored signatures.

Before publication, the exporter verifies top-level and evidence SHA256 manifests against
the exact actual file sets, with no leading ./, omission or extra file. Delivery uses only
inbox/fills/sc-yao in the dedicated worktree, commit.gpgsign=false, a pull with rebase
immediately before the non-force push, and a staged/committed path-scope check. A refused
push is kept and reported rather than forced or silently retried. The push result and
delivery commit are recorded in the chat receipt, outside this self-hashed payload.

The returned ZIP contains this identical payload under exactly sc-yao/. Its archive paths
and every file hash are compared against the staged payload before delivery; the ZIP digest
is recorded in the external receipt. The source branch remains local. The maintainer reviews
and rebases the material for a PR after sc-garble lands; Seyoon approves that PR.

Previously pushed checkpoint commits remain in exchange history:

| Checkpoint | Delivery commit |
|---|---|
| 1 | `f0a9a6163c5c91599147eb550fd5bb929cc68aa0` |
| 2 | `816971fc6922646f056a47efd41b1407f762320d` |
| 3 | `acc868271367d525350da2c1043e7f470f1c0a98` |
| 4 | `171a341ab208261d7a29865a32260c1640617158` |
'''
assert 'PENDING_' not in text and '**DRAFT' not in text
# Improve prose spacing without changing code, hashes, formulas, or verbatim records.
units = ('children|helper|files|lines|public|private|variants|errors|constants|rows|'
    'target|source|reader|patches|commits|inputs|words|cases|modules|negative|unsealed|'
    'sealed|stored|fresh|final|imports|bits|bytes|slots|baseline|candidates|controls|'
    'changed|explicit|full|fully|inherited|new|frozen|unchanged|FAIL|WARN')
parts = re.split(r'(```[\s\S]*?```|`[^`\n]*`)', text)
for i in range(0, len(parts), 2):
    parts[i] = re.sub(r'(\d)(?=(?:' + units + r')\b)', r'\1 ', parts[i], flags=re.I)
text = ''.join(parts)
normalized = ' '.join(re.sub(r'^>\s?', '', text, flags=re.M).split())
for path in Path('evidence/scope-request').glob('*.md'):
    s = path.read_text()
    if 'Question sent via request_user_input_async:' not in s:
        continue
    question = s.split('Question sent via request_user_input_async:\n', 1)[1].split(
        '\n\nUser answer', 1)[0]
    assert ' '.join(question.split()) in normalized, path
out = Path('evidence/reports/final.md')
assert not out.exists()
out.write_text(text)
print('FINAL REPORT', len(text.splitlines()), 'lines;', len(text.split()), 'words;',
      hashlib.sha256(out.read_bytes()).hexdigest())
