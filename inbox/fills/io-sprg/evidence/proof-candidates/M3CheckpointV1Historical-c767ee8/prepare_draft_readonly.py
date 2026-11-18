"""Pure temporary report preparation: no Lean, Git, source edits or gate execution."""
from pathlib import Path
import csv
import datetime
import hashlib
import io
import json
import re

W = Path('/Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange')
B = Path('/private/tmp/io-sprg-proof-notes/tmpM3CheckpointDraft')
PREFIX = 'TCSlib.Cryptography.Obfuscation.StructuredSeed.'
AREA = 'TCSlib/Cryptography/Obfuscation/StructuredSeed/'
M2 = W / 'evidence/checkpoints/M2/REPORT.md'
M0 = W / 'evidence/checkpoints/M0/REPORT.md'
OLD_ANCHORS = Path('/private/tmp/io-sprg-proof-notes/M2CheckpointDraft/current-declaration-anchors-M2.tsv')

sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()

def tsv(path, rows, fields):
    stream = io.StringIO()
    writer = csv.DictWriter(stream, fieldnames=fields, delimiter='\t', lineterminator='\n')
    writer.writeheader()
    writer.writerows(rows)
    (B / path).write_text(stream.getvalue())

m2 = M2.read_text()
frozen = m2.split('## Frozen fidelity, Rule15 and non-vacuity tables', 1)[1].split(
    '## Current M2 declaration anchors for the archived tables', 1)[0]
archived_tables = re.findall(r'(?:^\|[^\n]*\n){2,}', frozen, re.M)
assert len(archived_tables) == 4
for table in archived_tables:
    assert table in M0.read_text(), 'Archived mathematical table differs from M0'
(B / 'archived-M0-tables.BYTE-EXACT.md').write_text(
    '## Frozen fidelity, Rule15 and non-vacuity tables\n\n'
    'All four mathematical tables below are byte-exact M0 snapshots. Their line numbers\n'
    'are **historical M0 anchors**; current draft anchors are indexed separately.\n\n' +
    frozen[frozen.index('### Archived M0 fidelity table'):])

# These are planning inputs only. Final owner authority must be the root's committed
# dynamic inventory. Existing M2 files plus the three explicitly approved new splits.
old_inventory = json.loads((W / 'evidence/checkpoints/M2/owner-inventory.json').read_text())
changed = [AREA + 'Claim42.lean', *(AREA + 'Claim42/' + n + '.lean'
    for n in ['Load', 'Defs', 'Bounds', 'Conditions'])]
files = sorted(set(old_inventory['files']) | set(changed))
source_rows = [{'file': rel, 'sha256': sha(W / rel),
    'lines': len((W / rel).read_text().splitlines()),
    'max_width': max(map(len, (W / rel).read_text().splitlines()), default=0)} for rel in files]
anchors = [row for row in csv.DictReader(OLD_ANCHORS.open(), delimiter='\t')
           if row['file'] not in changed]
for rel in changed:
    stack = []
    for number, line in enumerate((W / rel).read_text().splitlines(), 1):
        match = re.match(r'^namespace (\S+)', line)
        if match:
            stack.append(match[1])
        elif re.match(r'^end(?: |$)', line):
            assert stack, (rel, number)
            stack.pop()
        else:
            match = re.match(r'^(?:noncomputable )?(def|theorem|lemma) (\S+)', line)
            if match:
                anchors.append({'name': '.'.join(stack + [match[2]]), 'kind': match[1],
                                'file': rel, 'line': str(number)})
    assert not stack, rel
anchors.sort(key=lambda r: r['name'])
assert len(anchors) == len({r['name'] for r in anchors})
byname = {r['name']: r for r in anchors}
tsv('current-declaration-anchors.WORKTREE.tsv', anchors, ['name','kind','file','line'])

originals = [row for row in csv.DictReader(
    (W / 'evidence/review/m0-report-sp-w2/proof-obligations.tsv').open(), delimiter='\t')
    if row['milestone'] == 'M3']
assert len(originals) == 10
original_rows = []
for row in originals:
    a = byname[row['Lean_name']]
    original_rows.append({'name': row['Lean_name'], 'file': a['file'], 'line': a['line'],
                          'status': 'FINAL_M3_CHECKS_PENDING'})
tsv('M3-originals.WORKTREE.tsv', original_rows, ['name','file','line','status'])
helper_specs = json.loads((W / 'evidence/checkpoints/M3/helper-specs.json').read_text())
assert len(helper_specs) == 13
helper_rows = []
for spec in helper_specs:
    full = PREFIX + ('Params.' if spec['name'] == 'jointLaw_prob_eq_uprob' else 'Internal.') + spec['name']
    a = byname.get(full)
    helper_rows.append({'name': full, 'file': spec['file'],
        'line': a['line'] if a else 'PENDING_INSERTION', 'probe': spec['probe'],
        'status': 'FINAL_M3_CHECKS_PENDING',
        'role': ' '.join(spec['doc'].split('**Proof sketch.**',1)[0].split())})
tsv('M3-helpers.WORKTREE.tsv', helper_rows, ['name','file','line','probe','status','role'])

original_table = '| Frozen M3 obligation (area prefix omitted) | Worktree anchor | Final evidence |\n| --- | --- | --- |\n'
for row in original_rows:
    original_table += f"| `{row['name'].removeprefix(PREFIX)}` | `{row['file'].removeprefix(AREA)}:{row['line']}` | Pending committed-M3 refresh |\n"
helper_table = '| Proposed/inserted theorem-only helper (area prefix omitted) | Worktree anchor | Role |\n| --- | --- | --- |\n'
for row in helper_rows:
    helper_table += f"| `{row['name'].removeprefix(PREFIX)}` | `{row['file'].removeprefix(AREA)}:{row['line']}` | {row['role']} |\n"

# Retain all previous selected declaration identities, then include current M3 scope.
selected = set(PREFIX + name for name in re.findall(r'^\| `([^`]+)` \| `[^`]+` \|$',
    m2.split('## Current M2 declaration anchors for the archived tables',1)[1].split(
        '## Phase B target statements',1)[0], re.M))
selected |= {r['name'] for r in original_rows + helper_rows if r['name'] in byname}
appendix = '## Current worktree declaration anchors\n\n'
appendix += ('These anchors are a hash-bound temporary worktree snapshot, **not final committed-M3\n'
             'references**. Refresh after root supplies the final M3 source and check records.\n'
             'The complete TSV also retains explicit structure-field anchors from unchanged M2 files.\n'
             'Generated constructors/recursors/inherited fields remain represented by their structure;\n'
             'this lexical appendix is not a typed kernel census or a proof-status table.\n\n'
             '| Declaration (area prefix omitted) | Worktree source anchor |\n| --- | --- |\n')
for name in sorted(selected):
    assert name in byname, name
    a = byname[name]
    appendix += f"| `{name.removeprefix(PREFIX)}` | `{a['file'].removeprefix(AREA)}:{a['line']}` |\n"
(B / 'current-anchor-appendix.WORKTREE.md').write_text(appendix)
(B / 'M3-originals.WORKTREE.md').write_text(original_table)
(B / 'M3-helpers.WORKTREE.md').write_text(helper_table)

# This snapshot intentionally contains no final evidence claim or inferred final hash.
progress = json.loads((W / 'evidence/checkpoints/M3/progress.json').read_text())
delivery_m2 = json.loads((W / 'evidence/delivery/M2.json').read_text())
snapshot = {'status':'DRAFT_FINAL_M3_HEAD_AND_CHECKS_PENDING',
    'captured_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'root_provided_prefix_heads':['e966956e25caf9512050ddf5d480a5dec7f4d3de',
                                  'bc5d5227a52571ad5e1e9b86219cfcb4987b7771'],
    'final_M3_source_head':None,
    'expected_NOT_VERIFIED':{'owners':26,'headers':689,'cumulative_helpers':19,
        'M3_new_helpers':13,'approved_moves':14,'checked_steps':133,
        'completed_original_bodies':114,'remaining_original_holes':32},
    'source_scope':'M2 inventory plus approved three Claim42 split modules; final dynamic committed inventory still required',
    'source_files':source_rows,'draft_anchor_count':len(anchors),
    'archived_M0_report_sha256':sha(M0),'archived_M2_report_sha256':sha(M2),
    'archived_exact_table_sha256':[hashlib.sha256(t.encode()).hexdigest() for t in archived_tables],
    'root_progress_snapshot':progress,'M2_delivery':delivery_m2,
    'final_static_build_axiom_slot_checks':'PENDING_ROOT_RECORDS',
    'full_kernel_census_and_seals':'HISTORICAL_M0_UNTIL_FINAL_FRESH_GATES',
    'source_mutation':False,'Lean_Git_cache_agent_invocations':False}
(B / 'snapshot.PENDING.json').write_text(json.dumps(snapshot,indent=2,ensure_ascii=False)+'\n')
print('Prepared worktree anchors and four byte-exact M0 tables; final M3 evidence PENDING')
