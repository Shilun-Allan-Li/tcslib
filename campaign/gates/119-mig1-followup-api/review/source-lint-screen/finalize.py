"""Read-only Git/source/output QA, source-level candidate review, then local freeze."""
from pathlib import Path
import base64, collections, datetime, hashlib, io, json, re, subprocess, tarfile

OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[4]
BASE = '1160c18f03fd318f0dec25738790935fa61379d4'
CAPTURED = 'aa37da7fa8d5dc53823ccf99db8747e55cabb04b'
CURRENT = 'f1ca767a10551960faf36ad9c8ff17bea3a2d88c'
MERGED_API = '3023dc1408c3d216fc07a7cbba9ae30135b861ed'

def sha(b): return hashlib.sha256(b).hexdigest()
def git(*args):
    return subprocess.run(['git', '-C', str(ROOT), *args], check=True,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE).stdout
def write_json(name, value):
    (OUT/name).write_text(json.dumps(value, indent=2, ensure_ascii=False)+'\n')

capture = json.loads((OUT/'capture.json').read_text())
assert capture['base'] == BASE and capture['head'] == CAPTURED
population = list(capture['population'])
assert len(population) == 16 and len(set(population)) == 16
assert population == (OUT/'population.txt').read_text().splitlines()
for commit in [BASE, CAPTURED, CURRENT, MERGED_API]:
    assert git('rev-parse', commit).decode().strip() == commit
    assert git('cat-file', '-t', commit).decode().strip() == 'commit'
source_links = []
for side, commit in [('base', BASE), ('head', CAPTURED)]:
    archive = base64.b64decode((OUT/(side+'.tar.base64.txt')).read_bytes(), validate=False)
    assert len(archive) == capture['sides'][side]['archive_bytes']
    assert sha(archive) == capture['sides'][side]['archive_sha256']
    with tarfile.open(fileobj=io.BytesIO(archive)) as tar:
        selected = {p:tar.extractfile(p).read() for p in population}
    for row in capture['sides'][side]['files']:
        path = row['path']
        inert = (OUT/'inputs'/side/(path+'.txt')).read_bytes()
        assert inert == selected[path] == git('show', commit+':'+path)
        assert len(inert) == row['bytes'] and sha(inert) == row['sha256']
        blob = git('rev-parse', commit+':'+path).decode().strip()
        assert blob == row['blob']
        assert hashlib.sha1(b'blob '+str(len(inert)).encode()+b'\0'+inert).hexdigest() == blob
        other = MERGED_API if side == 'base' else CURRENT
        assert git('show', other+':'+path) == inert
        source_links.append(dict(side=side, path=path, captured_commit=commit,
                                 equivalent_commit=other, blob=blob, sha256=sha(inert)))
api_diff = git('diff', '--name-only', BASE, MERGED_API, '--', '*.lean')
head_diff = git('diff', '--name-only', CAPTURED, CURRENT, '--', '*.lean')
assert api_diff == head_diff == b''
write_json('final-source-linkage.json', dict(
    base=BASE, merged_prerequisite=MERGED_API, captured_head=CAPTURED, current_pr234_head=CURRENT,
    all_lean_diff_base_to_merged_empty=True, all_lean_diff_capture_to_current_empty=True,
    exact_population_blobs=source_links,
    scope='Read-only object and source equality. Original screen commands/pins are retained; no retiling or replay claim.'))

for tool, digest in capture['tools'].items():
    actual = (ROOT/tool).read_bytes()
    assert sha(actual) == digest
    assert (OUT/'tools'/(tool.replace('/', '__')+'.txt')).read_bytes() == actual
    assert git('show', BASE+':'+tool) == git('show', CAPTURED+':'+tool) == actual

delta = json.loads((OUT/'pair-delta.json').read_text())
assert (delta['base']['candidates'], delta['head']['candidates']) == (2222,2228)
assert (delta['base']['reproduced_chars'],delta['head']['reproduced_chars']) == (738885,740747)
assert len(delta['new']) == 6 and not delta['gone'] and not delta['changed_measurements']
indexes = {}
for side, count in [('base',2005),('head',2006)]:
    rows = json.loads((OUT/(side+'-index.json')).read_text())
    indexes[side] = {r['label']:r for r in rows}
    assert len(rows) == len(indexes[side]) == count
    receipt = json.loads((OUT/(side+'-run.json')).read_text())
    raw = (OUT/(side+'.out')).read_bytes()
    assert receipt['exit'] == 0 and receipt['bytes'] == len(raw) and receipt['output_sha256'] == sha(raw)
    assert receipt['script_sha256'] == capture['tools']['scripts/copy-text-screen-v3.py']
    assert receipt['command'][:4] == ['nice','-n','10','python3'] and receipt['command'][4] == '-I'
    assert receipt['command'][7:] == population and receipt['full_population'] == 16
    candidates = json.loads((OUT/(side+'-candidates.json')).read_text())
    assert len(candidates) == delta[side]['candidates']
    assert len({(r['a'],r['b']) for r in candidates}) == len(candidates)
    assert sum(r['shared'] for r in candidates) == delta[side]['reproduced_chars']
    for r in candidates:
        assert r['denominator'] == indexes[side][r['b']]['body_chars']
        assert r['kind'] == indexes[side][r['a']]['kind'] == indexes[side][r['b']]['kind']
    scheduling = json.loads((OUT/('scheduling-check-'+side+'.json')).read_text())
    assert int(scheduling['actual_process_snapshot'].split()[1]) == 10

events = [json.loads(s) for s in (OUT/'lock-events.jsonl').read_text().splitlines()]
assert [e['event'] for e in events] == ['waiting','acquired','released']
br=json.loads((OUT/'base-run.json').read_text()); hr=json.loads((OUT/'head-run.json').read_text())
assert events[1]['utc'] <= br['start_utc'] <= br['end_utc'] <= hr['start_utc'] <= hr['end_utc'] <= events[2]['utc']
parser_delta=json.loads((OUT/'parser-delta.json').read_text())
assert not parser_delta['changed_surviving_normalized_bodies'] and not parser_delta['kind_changes']
assert set(parser_delta['new_eligible_labels']) == {'Finite.lean::exists_first_entry_of_fixed','Wrappers.lean::redirectTM_spaceUsedByTape'}
assert parser_delta['gone_eligible_labels'] == ['Catalog.lean::redirectTM_spaceUsedByTape']
assert not any('redirectTM_spaceUsedByTape' in r[k] for r in json.loads((OUT/'head-candidates.json').read_text()) for k in ['a','b'])

new_name='Finite.lean::exists_first_entry_of_fixed'
predicate_names={'Loop.lean::emCall_first_entry','Primitives.lean::emitter_first_entry'}
singleton_names={'Catalog.lean::f2_catalogFirstEntry','Primitives.lean::catalogFirstEntry'}
classifications=[]
for r in delta['new']:
    assert r['kind']=='proof' and r['cross_file']
    other = r['b'] if r['a']==new_name else r['a']
    assert new_name in [r['a'],r['b']]
    if other in predicate_names:
        group='P: predicate first-entry harvest'
        assessment=('Material common proof, not a syntax-only false positive: least stop time, strict cut, '
                    'fixed continuation, and final endpoint. New public theorem generalizes the old Bool/DecidablePred '
                    'private contracts; new fixed-continuation proof uses public run equations and explicit induction. '
                    'The two old private proofs remain unchanged, including their Function.iterate_fixed step. '
                    'This approved prerequisite publication stages downstream MIG re-points; it does not establish '
                    'that the legacy copies are removed or approve permanent duplication.')
    else:
        assert r['a']==new_name and other in singleton_names
        group='S: singleton-stop specialization'
        assessment=('Material shared least-entry/endpoint argument. Existing private theorem concerns one live state '
                    'and is a source-level specialization of the new stop-predicate theorem. The old singleton proofs '
                    'are identical to each other and unchanged. Their direct consumer conversion has not been '
                    'elaborated in this no-Lean task; publication is not downstream cleanup or a debt waiver.')
    classifications.append(dict(**r, group=group, assessment=assessment))
assert len(classifications)==6 and len({(r['a'],r['b']) for r in classifications})==6
write_json('new-candidate-classification.json', classifications)

snippets=[]
for label in sorted({new_name}|predicate_names|singleton_names):
    row=indexes['head'][label]
    lines=(OUT/'inputs/head'/(row['path']+'.txt')).read_text().splitlines()
    start=next(i for i,s in enumerate(lines) if re.match(r'(?:private )?(?:theorem|lemma) '+re.escape(row['name'])+r'\b',s))
    end=next(j+1 for j in range(start,len(lines)) if lines[j].strip()=='exact he.symm')
    snippets.append('## '+label+'\n\nExact captured head lines '+str(start+1)+'–'+str(end)+':\n\n```lean\n'+'\n'.join(lines[start:end])+'\n```\n')
(OUT/'family-source-snippets.md').write_text('# Reviewed candidate endpoints\n\n'+'\n'.join(snippets))

lint=json.loads((OUT/'lint-results.json').read_text())
assert not lint['style_normalized_new'] and not lint['style_normalized_gone']
assert len(lint['sides']['base']['style']['findings'])==len(lint['sides']['head']['style']['findings'])==77
for side in ['base','head']:
    assert lint['sides'][side]['campaign']['counts']=={'FAIL':0,'WARN':7,'INFO':7}
whole=json.loads((OUT/'whole-source-delta.json').read_text())
assert len(whole)==5 and collections.Counter(r['delta']['tag'] for r in whole)=={'insert':4,'delete':1}
assert not list(OUT.rglob('*.lean')) and not list(OUT.rglob('*.pyc'))

source_review=(OUT/'SOURCE-REVIEW.md').read_text()
source_review=source_review.replace('Copy-screen disposition remains separate until both raw16-file runs finish. In particular,',
    'Both full16-file screens have finished; the complete delta and all six added rows are\nreviewed in README.md and new-candidate-classification.json. In particular,')
(OUT/'SOURCE-REVIEW.md').write_text(source_review)

table='\n'.join('| `'+r['a']+'` | `'+r['b']+'` | '+str(r['shared'])+'/'+str(r['denominator'])+' = '+str(r['printed_percent'])+'% | '+r['group'].split(':')[0]+' |' for r in classifications)
readme='''# Gate119 exact-source lint and copy-screen review

Both unmodified, full16-file v3 screens completed with exit0, serially under the shared
screen lock and actual niceness10. All six new directed candidates are material
first-entry proof similarities with unchanged private harvest targets. They are explicitly
disclosed staged reuse; this report does not approve permanent copies or close the gate.

## Pins and source fidelity

- Screen base: `1160c18f03fd318f0dec25738790935fa61379d4` (API230 source).
- Screen head: `aa37da7fa8d5dc53823ccf99db8747e55cabb04b` (PR234 authored source).
- Current records-merged PR234 head: `f1ca767a10551960faf36ad9c8ff17bea3a2d88c`.
- Merged prerequisite campaign: `3023dc1408c3d216fc07a7cbba9ae30135b861ed`.

Read-only Git object checks verify full commit/blob identities, all32 inert source inputs,
both reversible archives, and exact16-file source equality to the two successor commits.
Entire `*.lean` diffs are also empty base→merged prerequisite and captured→current head.
These are source-equivalence links, not new screen or replay runs. Full receipts are in
`capture.json`, `final-source-linkage.json`, and `final-verification.json`.

The exact five-file source delta is four insertions and one deletion; every surviving line
is identical. The three authored exports are `pairDiagTM_spaceUsed`,
`FinTM.incFixedTM_spaceUsed`, and `MultiTapeTM.exists_first_entry_of_fixed`.
`FinTM.redirectTM_spaceUsedByTape` is an approved public-home relocation, not a fourth
new authored contract. Its old doc/name/header is preserved; its inserted body is the
approved CURRENT-MIG public-reader proof, whereas the removed API1160 body used legacy
foreign unfolds/private Catalog helper. The separate compiled census, not this source
screen, accounts for compiler auxiliaries. No definition/table/import/attribute/old
private helper or unrelated proof changes occur in this source delta.

## Population and executions

`population.txt` lists the same16 complete files on each side (60,675→60,716 newline
lines). `POPULATION.md` justifies every owner, prerequisite, model/control home and explicit
comparison source. Hardness, ExhaustiveReplay and NTimeDiagonalizer are inspected reuse
comparisons, not newly claimed dependencies/callers; StateRenaming is conservative model
context. Loop and CodeSimulator are full explicit harvest-comparison coverage. No literal
generic first-entry twin is asserted to occur in CodeSimulator. No population or raw
candidate cap was applied; this is the full named union, not recursive library closure.

| Measure | Base | Head |
|---|---:|---:|
| Eligible declarations | 2,005 | 2,006 |
| Directed candidates | 2,222 | 2,228 |
| Reproduced normalized characters (sum of directed scores) | 738,885 | 740,747 |
| Proof / cross-file | 913 | 919 |
| Proof / same-file | 961 | 961 |
| Term / cross-file | 163 | 163 |
| Term / same-file | 185 | 185 |
| Wall seconds | 1,247.757 | 1,264.189 |

BASE ran21:16:51–21:37:39UTC and HEAD21:37:39–21:58:43UTC on2026-11-07.
`base/head-request.json`, `base/head-run.json`, raw `.out`, and actual scheduling snapshots
retain commands, timestamps, exit status, hash, CPU and process data. `child_maxrss` is the
raw cumulative child high-water value in platform units, not a measured per-head peak.
`lock-events.jsonl` records acquisition and release. The screen tool SHA256 is
`f4feac91d3a1ec036f3bbcaafde83e6855a1bf1a62d31dac31a40a40d878f181`;
all three canonical tools equal their base/head Git objects and retained inert copies.

## Every added candidate

Raw tool direction is **a reproduces b**; the denominator is the complete normalized
**b** body, not an independent theorem count. Six new rows, zero gone rows, zero changed
retained scores. All2,222 old directed rows and their measurements survive unchanged.

| a reproduces | b | Shared / full b | Group |
|---|---|---:|---|
'''+table+'''

P: The new general live-stop theorem and the two old Bool/DecidablePred private
predicate variants share least-time selection, strict cut and fixed-run endpoint logic.
The old twins are also100% of one another (403/403 in both directions), already in BASE.
The new theorem replaces the old implicit `Function.iterate_fixed` conversion with public
run equations and explicit induction. These are material proof similarities, not a
short syntax coincidence. Publication is the approved common prerequisite; the old
consumers are deliberately not re-pointed in this API PR. Their cleanup remains a
separate downstream MIG task; no debt acknowledgement is inferred.

S: The two unchanged singleton-stop variants are identical375-character proofs. Their
least-time/fixed-endpoint argument is the singleton source-level case of the new predicate
contract. This task did not elaborate those consumer conversions. Their two new66% rows
are retained honestly, with the same downstream-cleanup limitation.

`new-candidate-classification.json` dispositions each row exactly once;
`family-source-snippets.md` retains the full reviewed headers and bodies for all five
endpoints. `pair-delta.json/out` and both candidate JSON/raw lists are complete. No new
same-file, executable term/data, or redirect relocation candidate appears. Removing the
old redirect theorem retires no baseline candidate, so no textual debt reduction is claimed.

The index independently shows only new eligible first-entry and moved-Wrappers labels,
one gone Catalog label, no surviving normalized body/kind change. The two new zero-space
proofs normalize to the same52-character application of the already-public generic
zero-tapes fact, below v3's60-character declaration threshold; both are explicitly
covered by manual source/reuse inspection, not counted as screened declarations. No
executable definition or transition table was copied by these insertions.

## Lints, limits and provenance

Unmodified canonical lint functions ran against exact inert archives on the same five
changed files, with campaign check8b enabled. Style77→77 inherited diagnostics and no
normalized new diagnostic; campaign0FAIL/7WARN/7INFO→same. The recorded lint `exit` values
follow the canonical CLI rule; these were function invocations, not separate CLI processes.
Long-file/module-heading/old proof-sketch findings remain visible and are not waived.
New docs are natural operational statements and the first-entry proof has a specific
sketch. The old moved redirect doc's frozen design labels/reader wording are disclosed
legacy prose, retained under the exact approved move. See `SOURCE-REVIEW.md` and raw lints.

The parser-only indexing attempt emitted a sandbox `nice: setpriority` warning but
completed. It performed no tiling and is not claimed as nice10 execution; its raw warning
is retained. Both actual screens separately ran escalated with observed nice10. No screen
failed or was truncated. No Lean, replay, source/API/Git mutation, cache/snapshot write,
commit/push, dispatch or gate closure was performed by this task. Source equivalence,
lint and bounded semantic review are not proof of global absence of duplication, nor
approval of the2,222 inherited candidates. Parent owns gate/replay/ledger disposition.

The folder is frozen after final QA; `SHA256SUMS` covers every other retained file.
'''
(OUT/'README.md').write_text(readme)
write_json('final-verification.json', dict(
    utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    exact_source_inputs=32, exact_archives=2, population_each_side=16,
    tools_exact=3, all_lean_source_equivalence=True,
    screens_exit=[br['exit'],hr['exit']], screens_serial=True, lock_released=True,
    actual_screen_niceness=[10,10], raw_pair_counts=[2222,2228], all_raw_rows_reconciled=True,
    new_rows_classified=6, gone_rows=0, changed_retained_measurements=0,
    unfiltered_candidate_lists=True, source_delta_insertions=4, source_delta_deletions=1,
    no_new_normalized_style_diagnostics=True, no_lean_or_git_mutation=True,
    scope='Bounded source/lint/copy-text review; no elaboration, replay, debt waiver, dispatch readiness or gate closure.'))
manifest=[]
for path in sorted(OUT.rglob('*')):
    if path.is_file() and path.name != 'SHA256SUMS':
        manifest.append(sha(path.read_bytes())+'  '+str(path.relative_to(OUT)))
(OUT/'SHA256SUMS').write_text('\n'.join(manifest)+'\n')
for line in manifest:
    digest,path=line.split('  ',1)
    assert sha((OUT/path).read_bytes())==digest
print(json.dumps(dict(frozen_files=len(manifest), manifest_sha256=sha((OUT/'SHA256SUMS').read_bytes()),
                      readme_sha256=sha((OUT/'README.md').read_bytes()),
                      new_rows=len(classifications), current_head=CURRENT), indent=2))
