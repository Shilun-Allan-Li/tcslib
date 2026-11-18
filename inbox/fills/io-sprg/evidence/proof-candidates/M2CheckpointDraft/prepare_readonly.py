from pathlib import Path
import csv, datetime, hashlib, io, json, re

W = Path('/Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange')
B = Path('/private/tmp/io-sprg-proof-notes/M2CheckpointDraft')
M1 = Path('/private/tmp/io-sprg-proof-notes/M1CheckpointDraft')
HEAD = '4ecc40c04a001bc87349b7ec368ece309774c28a'
PREFIX = 'TCSlib.Cryptography.Obfuscation.StructuredSeed.'
STRETCH = 'TCSlib/Cryptography/Obfuscation/StructuredSeed/Stretch.lean'

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def dump(name, value):
    (B / name).write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n')

def tsv(name, rows, keys):
    stream = io.StringIO()
    writer = csv.DictWriter(stream, fieldnames=keys, delimiter='\t', lineterminator='\n')
    writer.writeheader()
    writer.writerows(rows)
    (B / name).write_text(stream.getvalue())

inv = json.loads((W / 'evidence/checkpoints/M2/owner-inventory.json').read_text())
progress = json.loads((W / 'evidence/checkpoints/M2/progress.json').read_text())
assert inv['head'] == progress['source_head'] == HEAD
source = (W / STRETCH).read_text()
summary = json.loads((W / 'evidence/checks/M2-Stretch/summary.json').read_text())
assert digest(W / STRETCH) == summary['source_sha256']
assert summary['all_standard_axioms'] and summary['public_theorems'] == 9
assert summary['frozen_statements_unchanged']
old = json.loads((M1 / 'snapshot.json').read_text())
old_hashes = {r['file']: r['sha256'] for r in old['files']}
files = [{'file': rel, 'sha256': digest(W / rel),
          'lines': len((W / rel).read_text().splitlines()),
          'max_width': max(map(len, (W / rel).read_text().splitlines()), default=0)}
         for rel in inv['files']]
changed = [r['file'] for r in files if old_hashes.get(r['file']) != r['sha256']]
assert changed == [STRETCH], changed
assert len(files) == 23 and sum(r['lines'] for r in files) == 7694

namespace = []
anchors = []
for line, text in enumerate(source.splitlines(), 1):
    ns = re.match(r'^namespace (\S+)', text)
    if ns:
        namespace.append(ns.group(1))
    elif re.match(r'^end(?: |$)', text):
        namespace.pop()
    else:
        decl = re.match(r'^(?:noncomputable )?(def|theorem|lemma) (\S+)', text)
        if decl:
            name = '.'.join(namespace + [decl.group(2)])
            anchors.append({'name': name, 'kind': decl.group(1), 'file': STRETCH,
                            'line': str(line)})
assert len(anchors) == 11
assert {r['name'] for r in anchors if r['kind'] == 'theorem'} == set(summary['axioms'])
tsv('current-Stretch-anchors.tsv', anchors, ['name', 'kind', 'file', 'line'])

old_anchors = list(csv.DictReader((M1 / 'current-declaration-anchors.tsv').open(), delimiter='\t'))
all_anchors = [r for r in old_anchors if r['file'] != STRETCH] + anchors
all_anchors.sort(key=lambda r: r['name'])
assert len(all_anchors) == 785
tsv('current-declaration-anchors-M2.tsv', all_anchors, ['name', 'kind', 'file', 'line'])
anchor_map = {r['name']: r for r in all_anchors}

old_appendix = (M1 / 'current-anchor-appendix.md').read_text()
selected = []
for text in old_appendix.splitlines():
    match = re.match(r'^\| `([^`]+)` \| `[^`]+` \|$', text)
    if match:
        selected.append(PREFIX + match.group(1))
selected = sorted(set(selected) | set(summary['added_helpers']))
appendix = '''## Current M2 declaration anchors for the archived tables

The fidelity, Rule15, target-selection and non-vacuity tables in
`evidence/checkpoints/M1/REPORT.md` are exact frozen M0 tables. Their original
line references remain historical M0 anchors. This appendix updates declaration
locations to M2 source `4ecc40c04a001bc87349b7ec368ece309774c28a`.
Only Stretch changed from the published M1 source; hashes of the other 22 owned
files match the saved M1 snapshot. The accompanying complete TSV has 785 explicit
named declarations and structure-field anchors. Generated constructors, recursors
and inherited fields remain represented by their owning structure. This source
index is not a new typed kernel census or a proof-status table.

| Current full name (area prefix omitted) | M2 source anchor |
| --- | --- |
'''
for name in selected:
    a = anchor_map[name]
    display = a['file'].removeprefix('TCSlib/Cryptography/Obfuscation/StructuredSeed/')
    appendix += f"| `{name.removeprefix(PREFIX)}` | `{display}:{a['line']}` |\n"
(B / 'current-anchor-appendix-M2.md').write_text(appendix)

stretch_table = '| Declaration (area prefix omitted) | Current source anchor | Role |\n| --- | --- | --- |\n'
original = {'Params.seedBitsAt_le': '104', 'jls_seedBits_eq': '105',
            'jls_seedBits_le': '106', 'jls_hasPolyStretch': '110'}
helpers = {'Internal.w_lower': '107', 'Internal.stretch_gaps': '108',
           'Internal.eventually_seed_relative_gap': '109'}
for a in anchors:
    short = a['name'].removeprefix(PREFIX)
    role = ('Original M2 obligation; CHECKED_PASS step ' + original[short]
            if short in original else
            'New theorem-only helper; CHECKED_PASS step ' + helpers[short]
            if short in helpers else 'Unchanged definition/reader')
    stretch_table += f"| `{short}` | `Stretch.lean:{a['line']}` | {role} |\n"
(B / 'current-Stretch-anchors.md').write_text('# Current M2 Stretch anchors\n\n' + stretch_table)

frozen = W / 'evidence/statements/proof-obligations-current.tsv'
frozen_rows = list(csv.DictReader(frozen.open(), delimiter='\t'))
m3 = [r for r in frozen_rows if r['milestone'] == 'M3']
assert len(m3) == 10
m3_out = []
for r in m3:
    a = anchor_map[r['Lean_name']]
    m3_out.append(dict(r, current_file_line=a['file'] + ':' + a['line']))
tsv('M3-next-obligations.tsv', m3_out,
    ['Lean_name', 'file_line', 'milestone', 'owner_proof_sketch', 'current_file_line'])
m3_md = '''# M3 next scope: all ten original obligations

Authority: the frozen `evidence/statements/proof-obligations-current.tsv`, filtered
by exact milestone `M3`; current anchors agree with the unchanged M1 files.
The next milestone includes both owners: five load lemmas and five Claim42 lemmas.
None of these ten is counted as completed by M2.

| Original full name (area prefix omitted) | Current source anchor |
| --- | --- |
'''
for r in m3_out:
    m3_md += f"| `{r['Lean_name'].removeprefix(PREFIX)}` | `{r['current_file_line'].removeprefix('TCSlib/Cryptography/Obfuscation/StructuredSeed/')}` |\n"
m3_md += '''
The final Claim42 cutoff must be independent of the public prime parameter.
Complete the existing probability and bucket-load obligations, not only the final
`claim42` body. Additional specialized theorem-only helpers, if needed, require
explicit inventories and later seal coverage; they do not reduce this original
obligation count by renaming it.
'''
(B / 'M3-next-obligations.md').write_text(m3_md)

steps = [json.loads(p.read_text()) for p in sorted((W / 'evidence/steps').glob('*/step.json'))]
assert len(steps) == 110 and all(r['status'] == 'CHECKED_PASS' for r in steps)
build_path = W / 'evidence/build/M2/all-owners/results.jsonl'
build = [json.loads(l) for l in build_path.read_text().splitlines() if l.strip()]
assert len(build) == 23
assert {r['module'] for r in build} == set(inv['modules'])
build_mismatches = []
for r in build:
    module = r['module']
    log = build_path.parent / 'mods' / (module.replace('/', '_') + '.log')
    obj = W / '.lake/io-sprg-oleans' / (module + '.olean')
    checks = {'source': (W / (module + '.lean'), r['source_sha256']),
              'log': (log, r['log_sha256']), 'object': (obj, r['object_sha256'])}
    for label, (path, expected) in checks.items():
        if not path.exists() or digest(path) != expected:
            build_mismatches.append({'module': module, 'kind': label})
assert not build_mismatches, build_mismatches
assert all(r['head_at_start'] == HEAD and r['rc'] == r['errors'] == r['error_forms'] == 0
           for r in build)

bindings = {}
for rel in ['evidence/checkpoints/M2/progress.json',
            'evidence/checkpoints/M2/owner-inventory.json',
            'evidence/checkpoints/M2/source-head.txt',
            'evidence/checkpoints/M2/helper-plan.md',
            'evidence/checks/M2-Stretch/summary.json',
            'evidence/checks/M2-Stretch/expected.json',
            'evidence/build/M2/all-owners/results.jsonl',
            'evidence/statements/proof-obligations-current.tsv',
            'evidence/checkpoints/M1/REPORT.md', 'evidence/delivery/M1.json']:
    bindings[rel] = digest(W / rel)

snapshot = {
 'status': 'READ_ONLY_REPORT_PREPARATION_NOT_A_NEW_LEAN_RUN',
 'captured_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'source_head_authority': 'evidence/checkpoints/M2/source-head.txt',
 'source_head': HEAD,
 'M1_source_head': '19dde91afc384656e7e47cb018057e088d4ded0a',
 'M1_published_exchange': '10da7fdefd9a44023cc117a672f19e8a3617b81d',
 'M2_delivery': 'PENDING',
 'source_files': 23, 'source_lines': sum(r['lines'] for r in files),
 'max_lines': max(r['lines'] for r in files),
 'max_width': max(r['max_width'] for r in files),
 'changed_owned_files_vs_saved_M1_snapshot': changed,
 'Stretch_lines': len(source.splitlines()), 'Stretch_public_theorems': 9,
 'Stretch_all_standard_axioms': True,
 'M2_original_completed': 4, 'M2_new_helpers': 3,
 'original_completed_cumulative': 104, 'new_helpers_cumulative': 6,
 'checked_steps_cumulative': 110, 'original_remaining': 42,
 'frozen_original_total': 146, 'M3_next_original_obligations': 10,
 'full_owner_build_records': len(build),
 'full_owner_build_all_rc0_zero_errors_both_forms': True,
 'full_owner_build_source_log_object_hash_mismatches': build_mismatches,
 'full_owner_build_first_start': build[0]['start'],
 'full_owner_build_last_end': build[-1]['end'],
 'new_full_kernel_census_or_canonical_seals': 'NOT_CLAIMED; historical M0/final pending',
 'current_named_source_anchor_rows': len(all_anchors),
 'evidence_sha256': bindings, 'source_files_detail': files,
 'M2_step_records': steps[-7:]
}
dump('snapshot.json', snapshot)

addendum = '''# io-sprg Phase A — M2 checkpoint addendum

M2 stretch proofs and local checks are complete at source
`4ecc40c04a001bc87349b7ec368ece309774c28a`; M2 packaging and publication remain
pending. This addendum updates the published M1 report rather than replacing its
historical evidence. M1 was published at exchange commit
`10da7fdefd9a44023cc117a672f19e8a3617b81d`, from source
`19dde91afc384656e7e47cb018057e088d4ded0a`.

All four original M2 bodies are filled, with three new theorem-only helpers.
The cumulative record is **110 CHECKED_PASS steps: 104 original bodies and six
new helpers**, leaving **42 original direct proof holes**. M3–M6 remain unfinished,
T1–T6 remain unproved Phase B targets, and the complete end-to-end proof gate is open.

## Scope and proof route

| M2 original obligation | Saved checked step | Current source anchor |
| --- | --- | --- |
| `Params.seedBitsAt_le` | 104, repaired | `Stretch.lean:82` |
| `jls_seedBits_eq` | 105 | `Stretch.lean:390` |
| `jls_seedBits_le` | 106 | `Stretch.lean:404` |
| `jls_hasPolyStretch` | 110, repaired | `Stretch.lean:428` |

The new owned `Internal` helpers are `w_lower` (step107, line204),
`stretch_gaps` (step108, line223), and `eventually_seed_relative_gap`
(step109, repaired, line254). Failed attempts and their repaired check records
remain under `evidence/steps/` and `evidence/build/M2/`; only the final recorded
CHECKED_PASS states are counted above.

The seed bound uses the explicit witness `C = 2*(2^P.D)+12`, including zero and
rounding cases, for
`seedBitsAt κ ≤ C*(κ+1)^5*(n κ + m κ / w κ + 1)`.
The width helper proves `κ^(E*δ/2)/2 ≤ w κ` for `κ≥1`.
The sufficient E0 threshold supplies positive public/noise exponent gaps; the
relative-gap helper then proves `seedBitsAt κ ≤ m κ * κ^(-ε)` eventually.
Rational δ remains construction data and is coerced to real values for analysis,
as required by SP-W1. These payload bounds do not depend on the public prime.

The final proof retains the actual coefficient from the public
`Complexity.PolyExpr.eval_le` output-polynomial bound. It uses
`D = max 1 ((C:ℝ)*2^c)` and `η = ε/(2*(c+1))`, and absorbs the fixed
`D^η` factor using the existing real-power growth API. The discarded generic
monic-normalization route (`StretchFinal` candidates02/06) is not the implemented
proof route and must not be described as approved reuse or completed source.
No new algorithm, machine, sampler, efficiency claim, or frozen statement is
introduced by these three helpers. The helper plan is
`evidence/checkpoints/M2/helper-plan.md`.

SP-W3's seed-growth conjunct is proved together with the power bound. The raw
construction has `κ+1 ≤ seedBits κ` at every κ, since its public length is positive
and residue width is κ+1. This supplies `κ ≤ seedBits κ` beyond the common cutoff;
the final HasPolyStretch proof includes both conjuncts. No positive-κ premise is
added to the frozen theorem.

## Completed local checks and their limits

| Check | Result and authority |
| --- | --- |
| Fresh owner build | All23 exact owners, including both facades: rc0 and zero errors in both forms. `evidence/build/M2/all-owners/results.jsonl`; all23 source/log/object SHA-256 bindings match the current files, and all records name source4ecc40c. The final recorded owner ended at 2026-11-18T17:38:59.934902+00:00. |
| Stretch theorem axioms | All9 public theorem prints use only propext, Classical.choice and Quot.sound. `evidence/checks/M2-Stretch/summary.json`; its source hash matches the current576-line Stretch module. This scope includes both unchanged reader theorems, four original obligations and three helpers. |
| Stretch frozen statements | Existing frozen statements unchanged; exactly the three listed theorem-only helpers added, as recorded in the same summary. |
| Cumulative steps | All110 saved `step.json` records say CHECKED_PASS. M2 is steps104–110; the prior103 records belong to the completed M1 scope. |
| Source size | 23 owned files,7694 lines; maximum file801 lines, maximum width100. Stretch itself is576 lines, maximum width90. |
| Changed source from M1 | Stretch is the only changed owned file; the other22 source hashes match the saved M1 snapshot. The read-only preparation snapshot binds every current owner and referenced metadata file. |

The M1 **297 standard-only public theorem prints in11 affected owners** remain
M1 evidence with their original scope. They are not relabelled as a fresh M2
whole-area axiom census. M2 adds the fresh9-theorem Stretch result above. This
addendum does not infer a new stored-constant count, typed StmtDump count, or
transitive sorryAx-dependent count from source line counts or subtraction.

The canonical full stored-constant census, typed statement dump, dependency graph,
four-variant seals and paired controls remain **historical M0 evidence, with the
final fresh gates pending**. The M0 results were88 seals plus96 controls (184 passes)
for the then22 owners; they are not M2 proof passes. The final dynamic inventory
must include Basic and any later owned helper/split modules. Current M2 full-area
static boundary/campaign/freeze summaries and packaging verification are not
asserted by this read-only addendum; the checkpoint owner must attach their fresh
records before claiming those gates.

## Preserved fidelity and current anchors

Keep the exact fidelity, Rule15, target-selection and non-vacuity tables preserved
in `evidence/checkpoints/M1/REPORT.md`, with their original explicit label as
**historical M0 line anchors**. The full deviations remain in the archived M0
report. These contracts/formulas are unchanged by M2; proof status is the status
above, not the historical table's prose or locations.

Use `current-anchor-appendix-M2.md` for the current declaration-identity appendix.
`current-declaration-anchors-M2.tsv` has785 explicit named declaration/field
anchors, and `current-Stretch-anchors.tsv` gives all11 Stretch declarations.
These are source indexes, not kernel-generated declaration or typed census counts.
The other22 files are hash-identical to M1, so their M1 source anchors remain valid.

## Next milestone and retained disclosures

**M3 next means all ten original obligations**, not only the final Claim42 theorem:
five in `Claim42/Load.lean` and five in `Claim42.lean`. The exact frozen names,
current locations and original proof sketches are in `M3-next-obligations.tsv`;
the readable ten-row table is `M3-next-obligations.md`. The final probability bound
must keep its sufficiently-large cutoff independent of the public prime parameter.

Retain the published M1 overlap/reuse and process-limit disclosures without changing
their scope. This includes per-log classification of bounded search results,
harness-error/supersession records, the recorded two-Lean-wrapper overlap and its
correction, and the earlier whole-job subagent-limit breach. This preparation
performs only static reads and temporary report generation; it does not run Lean,
Git, cache tooling, source mutations or agents. No new claim of whole-history
seriality, global host auditing or theorem-search completeness is made.

M2 packaging/publication remains pending. M1's delivery record is
`evidence/delivery/M1.json`; a future M2 delivery hash must come from its actual
published delivery record, not from this source commit or a proposed packaging
commit. The project remains an intermediate Phase A checkpoint.
'''
(B / 'ADDENDUM-M2.md').write_text(addendum)
(B / 'README.md').write_text('''# M2 checkpoint report preparation

Read-only repository inspection; outputs are staged only under this temporary path.
Use ADDENDUM-M2.md as prose for the M2 update. Active evidence/REPORT.md was not edited.
The snapshot binds the current M2 source, all23 completed owner build records and
metadata. It verifies saved source/log/object hashes; it does not invoke Lean.

Files:
- ADDENDUM-M2.md: complete report addendum with completed proof/build scope and pending gates.
- current-Stretch-anchors.md/.tsv: all11 current Stretch declarations.
- current-anchor-appendix-M2.md: current selected declaration-identity appendix for archived M0 tables.
- current-declaration-anchors-M2.tsv: full785-row source anchor index (676 named commands plus109 fields).
- M3-next-obligations.md/.tsv: exact10 frozen M3 obligations, including original sketches in TSV.
- snapshot.json: current metadata/source hashes, completed owner build hash checks and step bindings.
- prepare_readonly.py: static renderer; only reads repository and writes this temporary directory.

Do not relabel historical M0 census/seals, M1 axiom counts or the archived table locations as
fresh M2 whole-area kernel evidence. Do not report M2 delivery complete until the root supplies
its actual package/push record. Do not revive the rejected monic-normalization candidates02/06.
''')
print(json.dumps({k: snapshot[k] for k in [
    'source_head', 'source_files', 'source_lines', 'checked_steps_cumulative',
    'original_remaining', 'M3_next_original_obligations', 'full_owner_build_records',
    'full_owner_build_source_log_object_hash_mismatches', 'current_named_source_anchor_rows']}, indent=2))
print('WROTE', B)
