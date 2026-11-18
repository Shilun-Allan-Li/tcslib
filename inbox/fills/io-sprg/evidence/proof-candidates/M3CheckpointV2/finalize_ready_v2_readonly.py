"""Temp-only M3 v2 report/anchor verification and rendering; no subprocesses."""
from pathlib import Path
import collections
import csv
import datetime
import difflib
import hashlib
import io
import json
import re

W=Path('/Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange')
B=Path('/private/tmp/io-sprg-proof-notes/M3CheckpointV2')
V1=Path('/private/tmp/io-sprg-proof-notes/M3CheckpointV1Historical-c767ee8')
BASES=Path('/private/tmp/io-sprg-proof-notes/WarningCleanupC767/base-source')
HEAD='04249b85e80a007dc5845077a18a365d5150e14b'
OLD='c767ee867e76c0b1248cee46d4af5296ffa078d5'
PREFIX='TCSlib.Cryptography.Obfuscation.StructuredSeed.'
AREA='TCSlib/Cryptography/Obfuscation/StructuredSeed/'
STANDARD={'propext','Classical.choice','Quot.sound'}
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
rj=lambda rel:json.loads((W/rel).read_text())
inputs=['evidence/checkpoints/M3/owner-inventory.json','evidence/checkpoints/M3/source-head.txt',
 'evidence/checks/m3-final-v2/summary.json','evidence/checks/m3-final-v2/freeze-summary.json',
 'evidence/checks/m3-final-v2/global-freeze/summary.json','evidence/checks/m3-final-v2/global-freeze/current-global-map.json',
 'evidence/checks/m3-final-v2/sizes-widths.json','evidence/checks/m3-final-v2/boundary.json',
 'evidence/checks/m3-final-v2/lean-warning-summary.json','evidence/checkpoints/M3/axiom-summary-v2.json',
 'evidence/checkpoints/M3/noise-opacity-repair/focused-v3-binding.json',
 'evidence/build/M3/all-owners-v2/results.jsonl','evidence/meta/M3-final-v2/results.jsonl',
 'evidence/host/M3-final-v2/slot-summary.json','evidence/host/M3-final-v2/slots-io-sprg.log']
inv=rj(inputs[0]);static=rj(inputs[2]);freeze=rj(inputs[3]);glob=rj(inputs[4]);names=rj(inputs[5])
sizes=rj(inputs[6]);boundary=rj(inputs[7]);warnings=rj(inputs[8]);axioms=rj(inputs[9]);slots=rj(inputs[13])
assert (W/inputs[1]).read_text().strip()==HEAD
for record in [inv,static,sizes,boundary,warnings,axioms]:assert record['head']==HEAD
assert freeze['current_head']==HEAD and freeze['changed']==freeze['removed']==0
assert freeze['statement_prose_unchanged'] and len(freeze['added_helpers'])==20
assert len(freeze['approved_moves'])==14
assert glob['status']=='FROZEN_GLOBAL_HEADERS_AND_STATEMENT_PROSE_PASS'
assert glob['current_headers']==690 and glob['frozen_headers']==670
assert not glob['globally_removed'] and not glob['globally_changed_headers']
assert len(glob['moves'])==14 and len(glob['new_theorems_reported'])==20
assert len(inv['files'])==static['owners']==26 and static['decls']=={'ADDED':690}
assert static['lines']==8672 and static['all_widths_pass'] and not static['new_campaign_fail_warn']
for name,row in static['checks'].items():
 assert sha(W/f'evidence/checks/m3-final-v2/{name}.log')==row['log_sha256']
 assert row['rc']==(1 if name=='campaign' else 0)
assert not boundary['forbidden_imports'] and not boundary['new_realization_variants'] and not boundary['new_contract_variants'] and not boundary['pdf_paths']
assert set(boundary['changed'])==set(inv['files'])|{'TCSlib.lean'}
assert warnings['total_warnings']==warnings['expected_remaining_sorry_warnings']==32 and warnings['other_warnings']==[]
filemap={r['file']:r for r in sizes['files']};assert set(filemap)==set(inv['files'])
assert sum(r['lines'] for r in filemap.values())==8672
assert max(r['lines'] for r in filemap.values())==801 and max(r['max_width'] for r in filemap.values())==100
build=W/'evidence/build/M3/all-owners-v2'
rows=[json.loads(l) for l in (build/'results.jsonl').read_text().splitlines()]
assert len(rows)==26 and len({r['module'] for r in rows})==26
assert {r['module']+'.lean' for r in rows}==set(inv['files'])
sorry_count=0
for row in rows:
 rel=row['module']+'.lean';log=build/'mods'/(row['module'].replace('/','_')+'.log');text=log.read_text()
 assert row['head_at_start']==HEAD and row['rc']==row['errors']==row['error_forms']==0
 assert sha(W/rel)==row['source_sha256']==filemap[rel]['sha256']==glob['current_source_sha256'][rel]
 assert sha(log)==row['log_sha256'] and not re.search(r'error[:(]',text)
 assert sha(W/'.lake/io-sprg-oleans'/(row['module']+'.olean'))==row['object_sha256']
 assert not [l for l in text.splitlines() if 'warning:' in l and 'sorry' not in l]
 sorry_count+=text.count("declaration uses 'sorry'")
assert sorry_count==32
steps=[rj(f'evidence/steps/{i:03}/step.json') for i in range(1,135)]
assert all(row['status']=='CHECKED_PASS' for row in steps)

assert axioms['public_theorem_prints']==335 and axioms['affected_owners']==17 and axioms['all_standard_only']
assert axioms['headlines']==19 and axioms['standard_only_headlines']==6
meta=[json.loads(l) for l in (W/'evidence/meta/M3-final-v2/results.jsonl').read_text().splitlines()]
meta={r['module']:r for r in meta if 'module' in r}
for mod,probe in axioms['probes'].items():
 assert sha(W/probe['log'])==probe['log_sha256']==meta[mod]['log_sha256']
 assert sha(W/(mod+'.lean'))==meta[mod]['source_sha256'] and meta[mod]['rc']==meta[mod]['errors']==0
 text=(W/probe['log']).read_text();assert not re.search(r'error[:(]',text)
 got={}
 for m in re.finditer(r"^'(.+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",text,re.M):
  assert m[1] not in got
  got[m[1]]=set(x.strip() for x in (m[2] or '').split(',') if x.strip())
 assert got=={n:set(a) for n,a in probe['axioms'].items()} and len(got)==probe['theorems']
completed=axioms['probes']['evidence/probes/M3V2_AllCompletedAxioms']['axioms']
headline=axioms['probes']['evidence/probes/M3V2_HeadlineAxioms']['axioms']
assert all(set(a)<=STANDARD for a in completed.values())
assert sum(set(a)<=STANDARD for a in headline.values())==6 and sum('sorryAx' in a for a in headline.values())==13
assert all(name in completed and set(completed[name])<=STANDARD for name in freeze['added_helpers'])
focus=axioms['focused_noise_opacity'];run=focus['run'];focusbind=rj(inputs[10])
assert meta[run['module']]==run and run['rc']==run['errors']==run['warnings']==0
assert sha(W/focus['log'])==run['log_sha256'] and sha(W/(run['module']+'.lean'))==run['source_sha256']
assert sha(W/focusbind['source'])==focusbind['source_sha256']
assert sha(W/focusbind['probe'])==focusbind['probe_sha256']==run['source_sha256']
assert run['module']=='evidence/probes/M3_FocusedNoiseOpacityV3'
assert 'attribute [local irreducible]' in (W/focusbind['probe']).read_text()
oldmeta=[json.loads(l) for l in (W/'evidence/meta/M3-focused-noise-opacity/results.jsonl').read_text().splitlines()]
oldrun=next(r for r in oldmeta if 'module' in r)
oldlog=W/'evidence/meta/M3-focused-noise-opacity/mods/evidence_probes_M3_FocusedNoiseOpacity.log'
assert oldrun['rc']!=0 and oldrun['errors']>0 and sha(oldlog)==oldrun['log_sha256']

cleanup=[]
for i in range(1,9):
 rel=f'evidence/warning-cleanup/W{i:02}/edit.json';row=rj(rel)
 assert row['status']=='COMBINED_FINAL_OWNER_CHECKED_PASS'
 assert filemap[row['file']]['sha256']==row['final_owner_source_sha256']
 assert sha(W/f'evidence/warning-cleanup/W{i:02}/before.lean.txt')==row['before_sha256']
 assert sha(W/f'evidence/warning-cleanup/W{i:02}/after.lean.txt')==row['after_sha256']
 cleanup.append(row);inputs.append(rel)
assert len({r['file'] for r in cleanup})==4
assert slots['status']=='PASS_WITH_EXACT_RECORDED_HISTORICAL_VIOLATION'
assert slots['acquisitions']==1273 and slots['max_concurrent_job_wrappers']==2 and not slots['active']
assert slots['all_tagged_wrapper_acquisitions_serial'] is False and slots['post_correction_serial'] is True
assert slots['post_correction']['acquisitions']==504 and slots['post_correction']['max_concurrent_job_wrappers']==1
assert sha(W/'evidence/host/M3-final-v2/slots-io-sprg.log')==slots['extracted_log_sha256']

public_probes=sorted((W/'evidence/overlap/probes').glob('M3Load_*/search.json'))
assert len(public_probes)==24
search_status=collections.Counter()
for path in public_probes+[W/'evidence/overlap/probes/M3NoiseActual_lpnNoise_law_cast/search.json']:
 record=json.loads(path.read_text());assert {r['mode'] for r in record['searches']}=={'exact','apply'}
 for search in record['searches']:
  mode=search['mode'];source=path.parent/(mode+'.lean.txt');log=path.parent/(mode+'.log')
  assert sha(source)==search['run']['source_sha256'] and sha(log)==search['run']['log_sha256']
  if path in public_probes:
   assert not re.search(r'^import .*StructuredSeed',source.read_text(),re.M)
   assert search['elaboration_errors']==[]
  search_status[search['status']]+=1
actual=rj('evidence/overlap/probes/M3NoiseActual_lpnNoise_law_cast/search.json')
assert actual['target_absent_before_all_searches'] is True
assert sha(BASES/'LPN.lean.txt')==actual['owner_before_sha256']
assert 'theorem Internal.lpnNoise_law_cast' not in (BASES/'LPN.lean.txt').read_text()

# Refresh all explicit anchors from the root's complete current global map. Preserve
# separately indexed structure fields by exact old→new equal-line mapping in LPN.
oldanchors=list(csv.DictReader((V1/'current-declaration-anchors-M3.tsv').open(),delimiter='\t'))
anchors={name:{'name':name,'kind':row['kind'],'file':row['file'],'line':str(row['line'])}
         for name,row in names.items()}
lpnold=(BASES/'LPN.lean.txt').read_text().splitlines();lpnnew=(W/(AREA+'LPN.lean')).read_text().splitlines()
linemap={}
for block in difflib.SequenceMatcher(None,lpnold,lpnnew,autojunk=False).get_matching_blocks():
 for offset in range(block.size):linemap[block.a+offset+1]=block.b+offset+1
for row in oldanchors:
 if row['name'] in anchors:continue
 assert row['kind'] in {'field','structure-field'},(row['name'],row['kind'])
 fresh=dict(row)
 if row['file']==AREA+'LPN.lean':
  oldline=int(row['line']);assert oldline in linemap
  fresh['line']=str(linemap[oldline]);assert lpnold[oldline-1]==lpnnew[int(fresh['line'])-1]
 else:
  # The other three cleanup owners have no structures; every old field owner
  # remains byte-identical to c767 source, as its v1 snapshot establishes.
  oldhash=next(r['sha256'] for r in json.loads((V1/'snapshot.SOURCE-CONFIRMED-GATES-PENDING.json').read_text())['source_files'] if r['file']==row['file'])
  assert filemap[row['file']]['sha256']==oldhash
 anchors[row['name']]=fresh
anchorrows=sorted(anchors.values(),key=lambda r:r['name'])
def tsv(name,rows,fields):
 buf=io.StringIO();wr=csv.DictWriter(buf,fieldnames=fields,delimiter='\t',lineterminator='\n');wr.writeheader();wr.writerows(rows);(B/name).write_text(buf.getvalue())
tsv('current-declaration-anchors-M3-v2.tsv',anchorrows,['name','kind','file','line'])
selection=set(PREFIX+n for n in re.findall(r'^\| `([^`]+)` \| `[^`]+` \|$',(V1/'current-anchor-appendix-M3.md').read_text(),re.M))
selection.add(PREFIX+'Internal.lpnNoise_law_cast')
appendix='''## Current M3 v2 source declaration anchors

These locations refer to root-confirmed repaired source
`04249b85e80a007dc5845077a18a365d5150e14b`. Every source/log/object hash was
checked against the fresh26-owner build and committed-source static inventory.
The complete TSV includes explicit structure fields; LPN field locations were
remapped through exact equal source lines after the new cast reader was inserted.
Generated constructors/recursors/inherited fields remain represented by their
owning structure. This lexical index is not a full typed kernel census.

| Declaration (area prefix omitted) | M3 v2 source anchor |
| --- | --- |
'''
for name in sorted(selection):
 row=anchors[name];appendix+=f"| `{name.removeprefix(PREFIX)}` | `{row['file'].removeprefix(AREA)}:{row['line']}` |\n"
(B/'current-anchor-appendix-M3-v2.md').write_text(appendix)
archived=(V1/'archived-M0-tables.BYTE-EXACT.md').read_text();(B/'archived-M0-tables.BYTE-EXACT.md').write_text(archived)
tables=re.findall(r'(?:^\|[^\n]*\n){2,}',archived,re.M);assert len(tables)==4

s=(V1/'REPORT-M3.READY.md').read_text()
for i,table in enumerate(tables):s=s.replace(table,f'FROZEN_TABLE_{i}_EXACT',1)
s=s.replace('# io-sprg Phase A — checkpoint 3 (M3)','# io-sprg Phase A — checkpoint 3 (M3), repaired v2',1)
s=s.replace(OLD,HEAD).replace('c767ee8','04249b8')
s=s.replace('| Proof-complete M3 source head | `'+HEAD+'` |',
 '| Third M3 source checkpoint (pre-opacity repair) | `'+OLD+'` |\n| Fourth M3 source commit, repaired v2 | `'+HEAD+'` |')
for before,after in {
 'all 133':'all 134','All 133':'All 134','All133':'All 134','133 CHECKED_PASS':'134 CHECKED_PASS',
 '001–133':'001–134','all334':'all335','all 334':'all 335','All334':'All335','All 334':'All 335',
 'fresh334':'fresh335','fresh 334':'fresh 335','335-theorem':'335-theorem',
 'thirteen new theorem-only helpers':'fourteen new theorem-only helpers',
 'thirteen\ntheorem-only helpers':'fourteen\ntheorem-only helpers',
 'All thirteen helper bodies':'All fourteen helper bodies',
 'nineteen cumulative helpers':'twenty cumulative helpers',
 'all nineteen':'all twenty','All nineteen':'All twenty',
 'six numerical bounds, six conditional probability bounds,\nand one shared semantic joint-law reader':'six numerical bounds, six conditional probability bounds,\nand two specialized semantic readers (joint-law transport and cast-indexed noise law)',
 '19 (M1 3 + M2 3 + M3 13)':'20 (M1 3 + M2 3 + M3 14)',
 'and19 new helpers':'and20 new helpers','and 19 new helpers':'and 20 new helpers',
 '689 ADDED':'690 ADDED','689 OK':'690 OK','| 689 |':'| 690 |',
 '14 ledgered moves,19':'14 ledgered moves,20','moves, 19 added helpers':'moves, 20 added helpers',
 'nineteen added helpers':'twenty added helpers','19 new helpers.':'20 new helpers.',
 '8,657':'8,672','8,657':'8,672','8657':'8672','207 above':'222 above',
 'M3 adds 963':'M3 adds 978','thirteen specialized theorem-only helpers':'fourteen specialized theorem-only helpers',
 '1,231':'1,273','462 post-correction':'504 post-correction','Its 462':'Its 504',
 '18:56:43':'19:21:31','fresh335-theorem':'fresh335-theorem'
}.items():s=s.replace(before,after)
# The old warning row is historical; the repaired current build has no such warning.
s=re.sub(r'^\| Lean linter diagnostics \|.*\n',
 '| Lean warnings | Exactly32 expected warnings for the remaining frozen later-stage sorry bodies; zero other warnings. All twelve previous linter warnings were removed by eight proof-only edits in four prior owners. `evidence/checks/m3-final-v2/lean-warning-summary.json`. |\n',s,flags=re.M)
s=s.replace('`evidence/build/M3/all-owners/`','`evidence/build/M3/all-owners-v2/`')
s=s.replace('`evidence/checks/m3-final/`','`evidence/checks/m3-final-v2/`')
s=s.replace('`evidence/checks/m3-final/sizes-widths.json`','`evidence/checks/m3-final-v2/sizes-widths.json`')
s=s.replace('`evidence/checks/m3-final/boundary.json`','`evidence/checks/m3-final-v2/boundary.json`')
s=s.replace('`evidence/checkpoints/M3/axiom-summary.json`','`evidence/checkpoints/M3/axiom-summary-v2.json`')
s=s.replace('`evidence/host/M3-final/`','`evidence/host/M3-final-v2/`')
s=s.replace('`evidence/host/M3-final/slot-summary.json`','`evidence/host/M3-final-v2/slot-summary.json`')
s=s.replace('The older progress.json still describes an earlier prefix and is not used as final\ncompletion evidence.', 'Intermediate progress snapshots retain their earlier scope; the repaired source\ninventory and fresh v2 evidence below determine this checkpoint status.')
s=s.replace('`evidence/checks/M3-proof-complete-global-freeze/`','`evidence/checks/m3-final-v2/global-freeze/`')
s=s.replace('The proof-complete global freeze is a source-bound WORKTREE_CANDIDATE audit whose\ncapture preceded the final commit. This preparation checked every captured source\nhash against the current files, and root confirmed their committed head as above.\nIt does not mislabel that guard as an independent Git HEAD or kernel-type audit.',
 'The global freeze remains explicitly a source-bound WORKTREE_CANDIDATE audit.\nThis preparation checked every captured source hash against the repaired current\nfiles and fresh committed-source static inventory. Root supplied the source head;\nthis preparation invoked no Git. Source header/prose preservation is separate\nfrom the later complete generated kernel-type audit.')
# Regenerate source tables from the current complete map, rather than arithmetic offsets.
step_last={(r['file'],r['name'].split('.')[-1]):i for i,r in enumerate(steps,1)}
orig=[r for r in csv.DictReader((W/'evidence/review/m0-report-sp-w2/proof-obligations.tsv').open(),delimiter='\t') if r['milestone']=='M3']
helpernames=[r['name'] for r in csv.DictReader((V1/'M3-helpers.WORKTREE.tsv').open(),delimiter='\t')]
helpernames.append(PREFIX+'Internal.lpnNoise_law_cast');assert len(helpernames)==14

def current_table(targets):
 text='| Declaration (area prefix omitted) | M3 v2 source anchor | Saved step |\n| --- | --- | --- |\n'
 for name in targets:
  row=anchors[name];step=step_last[row['file'],name.split('.')[-1]]
  text+=f"| `{name.removeprefix(PREFIX)}` | `{row['file'].removeprefix(AREA)}:{row['line']}` | {step}: CHECKED_PASS |\n"
 return text
orig_table=current_table([r['Lean_name'] for r in orig]);helper_table=current_table(helpernames)
(B/'M3-originals-v2.md').write_text(orig_table);(B/'M3-helpers-v2.md').write_text(helper_table)
a=s.index('## Original M3 declarations');b=s.index('## Module organization and frozen interface preservation',a)
s=s[:a]+'''## Original M3 declarations

These current anchors and saved checked steps refer to the repaired M3 v2 source.
The fresh full-owner build and completed-owner axiom probes pass.

'''+orig_table+'''
## New M3 theorem-only helpers

All fourteen helper bodies have saved CHECKED_PASS records and standard-only
axioms in the fresh selected probe. The fourteenth is the cast-indexed scalar
noise-law reader, step134, owned beside lpnNoise in LPN.lean. It is not a new
algorithm or assumption. Per-helper public reuse and search scopes are recorded
below; search suggestions themselves are not proof evidence.

'''+helper_table+'\n'+s[b:]
a=s.index('## Current M3 source declaration anchors');b=s.index('## Source and host disclosures',a)
s=s[:a]+appendix+'\n'+s[b:]
a=s.index('## Overlap and public API reuse');b=s.index('## Unchanged quantifiers, targets and earlier judgments',a)
s=s[:a]+'''## Opacity repair and proof-only cleanup

The c767ee8 report and checks were held before publication after the focused
single-definition diagnostic failed: making the foreign `lpnNoise` opaque exposed
an implicit cast normalization in `Params.badSet_expect_le`. The old proof used
`cast_eq` on a stored coin-type equality whose reduction depended on that foreign
definition. The failure is retained in `evidence/meta/M3-focused-noise-opacity/`
and its old source/probe hashes. The pre-repair c767ee8 checkpoint artifacts remain
historical under `evidence/checkpoints/M3/pre-opacity-repair-c767ee8/`.

The fourth M3 commit adds only the theorem
`Internal.lpnNoise_law_cast` in LPN.lean. Its literal statement includes the cast
from the explicit selector/residue product into the noise's stored coin type.
The noise owner composes the already proved `lpnNoise_law` with public Core.cast_eq;
foreign consumers now use the published cast-indexed law rather than normalize
that foreign definition. No frozen theorem statement, encoding, algorithm,
parameter, import or assumption was changed. The updated consumer and affected
owners passed, then all26 repaired owners were freshly rebuilt.

After that full build, the final focused probe
`evidence/probes/M3_FocusedNoiseOpacityV3.lean` copied the current Claim42/Defs
body under a **local irreducible lpnNoise only**. It passed rc0, zero errors and
warnings at the exact current consumer source hash. `focused-v3-binding.json` and
the third run in `evidence/meta/M3-final-v2/results.jsonl` bind its source/log.
This is a focused single-definition diagnostic, **not** a canonical full-closure
Rule10 seal. The historical v1 failure is not counted as a pass or erased.

The same commit applies eight proof-only warning cleanups in LPN, Degree,
Correctness and Stretch. The stored W01–W08 JSON records and before/after snapshots
under `evidence/warning-cleanup/` retain the exact hunks. Unused simp arguments and
a lambda binder were removed/renamed, redundant case equation labels removed,
two unnecessary focused-sequence operators replaced by ordinary sequencing, and
two dead ring suffixes deleted. Each proof-body edit was applied in a separate
tool invocation; combined final owner checks are recorded, not invented individual
compile claims. These four prior owners are therefore **changed from M2**.
Their frozen headers and pre-sketch prose remain byte-equivalent under the global
guard. No linter option or attribute was changed/disabled. The fresh v2 full build
has exactly32 remaining-sorry warnings and zero other warnings.

## Overlap and public API reuse

The name/shape logs remain under `evidence/overlap/M3-Load-name-shape/`,
`M3-Claim42-name-shape/` and the joint-law/noise-reader search records. Twenty-four
public-only full/core goal pairs now have48 exact?/apply? runs under
`evidence/overlap/probes/M3Load_*/`; their archived imports exclude StructuredSeed.
The added cast-normalization **control** closes by the existing Core.cast_eq.
This motivates composing that API in the noise owner; it is not evidence that
the actual opaque-noise reader statement was already available publicly.

A separate actual-reader exact/apply pair under
`evidence/overlap/probes/M3NoiseActual_lpnNoise_law_cast/` imports the preexisting
owned noise algorithm/law with lpnNoise opaque. The target reader was absent from
the bound source before both searches, so it cannot match itself. Both outcomes
are recorded INCONCLUSIVE_FINITE_SEARCH; they establish no global absence claim.
This is distinct from the public-only normalization control. In total50 current
search source/log hashes were checked across those25 pairs.

The original errProb_nonneg core closes by public
`Games.ProbComp.prob_nonneg`; its frozen named wrapper composes that fact with the
published reader. Other partial/diagnostic outputs are not theorem proofs. The
original invalid prefactor harness attempt remains retained and superseded by its
fresh namespace-correct v2 pair. Specialized sampler/record goals are explicitly
mathematical cores, not claims that a complete source statement was searched under
all its own definitions. Actual saved source bodies, fresh26-owner compilation
and335 standard-only selected theorem prints supply the proof evidence.

The specialized helpers compose public finite expectation/product, Markov,
binomial/factorial, power-order and polynomial/exponential growth APIs. The two
new semantic readers centralize their concrete joint-law/cast transports; no
copied generic identity, local contract variant, machine, fair-coin sampler or
algorithm construction is introduced. Complete conservative Rule10 closures,
all controls and runtime masks/EOF coverage remain final fresh gates.

'''+s[b:]
# Replace the overlap evidence row and add the bounded focused diagnostic explicitly.
s=re.sub(r'^\| Overlap/reuse \|.*\n', '| Overlap/reuse |24 public-only full/core exact/apply pairs plus one separate actual-reader pair with target absent from the pre-search owner; all50 source/log bindings retained. Closed normalization controls are public reuse, partial/inconclusive outputs are not proofs. |\n| Focused noise opacity | V3 passes after the full repaired build with only lpnNoise locally opaque; zero errors/warnings. Old v1 failure is retained. This is a single-definition diagnostic, not a canonical seal. |\n',s,flags=re.M)
# Current headline values are re-rendered from the fresh exact log map.
a=s.index('## Current M3 headline axiom prints');b=s.index('## Size re-estimate',a)
htext='''## Current M3 v2 headline axiom prints

Fresh19-headline probe at source04249b8. Names have the prefix
`TCSlib.Cryptography.Obfuscation.StructuredSeed.`. Exact logs and hashes are in
`evidence/checkpoints/M3/axiom-summary-v2.json`.

| Headline | Current printed axioms |
| --- | --- |
'''
for name,deps in headline.items():htext+=f"| `{name.removeprefix(PREFIX)}` | `{', '.join(deps)}` |\n"
s=s[:a]+htext+'\n'+s[b:]
# Remaining original declarations keep their frozen identities, with current locations.
a=s.index('| Frozen milestone | Remaining declaration');b=s.index('## Delivery verification',a)
remaining=[r for r in csv.DictReader((W/'evidence/review/m0-report-sp-w2/proof-obligations.tsv').open(),delimiter='\t') if r['milestone'] in ['M4','M4 / M6','M5','M6']]
assert len(remaining)==32
remain='| Frozen milestone | Remaining declaration (area prefix omitted) | M3 v2 source anchor |\n| --- | --- | --- |\n'
for row in remaining:
 ar=anchors[row['Lean_name']];remain+=f"| {row['milestone']} | `{row['Lean_name'].removeprefix(PREFIX)}` | `{ar['file'].removeprefix(AREA)}:{ar['line']}` |\n"
s=s[:a]+remain+'\n'+s[b:]
s=s.replace('and two specialized semantic readers (joint-law transport and cast-indexed noise law). The reader avoids duplicating the same\nsampler transport', 'and two specialized semantic readers (joint-law transport and cast-indexed noise law).\nThe joint-law reader avoids duplicating the same sampler transport')
s=s.replace('Core.cast_eq','`cast_eq` from Lean core')
for before,after in {'Exactly32':'Exactly 32','exactly32':'exactly 32','step134':'step 134',
 'all26':'all 26','fresh26':'fresh 26','and335':'and 335','All335':'All 335',
 'all50':'all 50','with48':'with 48','have48':'have 48','total50':'total 50',
 'Fresh19-headline':'Fresh 19-headline','source04249':'source 04249','scan:690':'scan: 690',
 '|24 public-only':'| 24 public-only'}.items():s=s.replace(before,after)
# Ensure the final table/rendering did not erase the protected M0 snapshots.
for i,table in enumerate(tables):s=s.replace(f'FROZEN_TABLE_{i}_EXACT',table)
assert all(table in s for table in tables)
assert not re.search(r'PENDING_[A-Z_]+|FROZEN_TABLE_\d|PLACEHOLDER',s)
assert 'Twelve non-sorry linter warnings remain' not in s
report=B/'REPORT-M3.READYv2.md';report.write_text(s)
provenance={'status':'READY_M3_REPAIRED_V2_PROOFS_LOCAL_GATES_COMPLETE_DELIVERY_PENDING',
 'source_head':HEAD,'source_head_authority':'Root + source-head/inventory/static/build records; no Git by preparer',
 'report_sha256':sha(report),'report_lines':len(s.splitlines()),'captured_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'owners':26,'headers':690,'frozen_headers':670,'moves':14,'helpers_cumulative':20,'M3_helpers':14,
 'M3_originals':10,'checked_pass_steps':134,'completed_original_bodies':114,'remaining_original_holes':32,
 'lines':8672,'max_file':801,'max_width':100,'expected_remaining_sorry_warnings':32,'other_Lean_warnings':0,
 'fresh_selected_theorems':335,'fresh_selected_owners':17,'fresh_headlines':19,'fresh_standard_headlines':6,'fresh_sorry_headlines':13,
 'focused_opacity_V3':{'status':'PASS','scope':'Only local-irreducible lpnNoise; NOT canonical full-closure seal','source_sha256':focusbind['source_sha256'],'probe_sha256':run['source_sha256'],'log_sha256':run['log_sha256']},
 'historical_opacity_V1':'FAIL retained; c767 report held before publication','warning_cleanup_edits':8,'warning_cleanup_owners':4,
 'slot_acquisitions':1273,'slot_max_wrappers':2,'slot_historical_serial':False,'slot_post_correction_acquisitions':504,'slot_post_correction_serial':True,'slot_active':0,
 'public_core_probe_pairs':24,'separate_actual_reader_pairs':1,'tactic_runs':50,'search_statuses':dict(search_status),
 'full_M0_kernel_census_and_Rule10':'HISTORICAL ONLY; fresh complete final gates remain required',
 'candidate_V2_adapters':'UNRUN; syntax only (standalone source freeze root-tested)',
 'archived_exact_table_sha256':[hashlib.sha256(t.encode()).hexdigest() for t in tables],
 'current_anchor_rows_including_fields':len(anchorrows),
 'source_files':sizes['files'],'evidence_sha256':{rel:sha(W/rel) for rel in inputs},
 'M3_package_publication':'PENDING','report_self_hash':'External provenance only; no circular embedded self-hash',
 'active_REPORT_modified':False,'preparer_Lean_Lake_Git_cache_source_edits_agents':False}
(B/'report-provenance.READYv2.json').write_text(json.dumps(provenance,indent=2,ensure_ascii=False)+'\n')
(B/'README.md').write_text('''# M3 repaired READYv2 packet

REPORT-M3.READYv2.md is the current report for source04249b8. All M3 proofs and
fresh local gates pass; packaging/publication and the complete final gates remain
pending. This is separate from the byte-preserved c767 historical v1 packet.

Verified by static reads/hash comparison here:26 exact source/log/object build
records;690 ADDED source headers and670 frozen headers/prose with14 moves/20 helpers;
all134 saved CHECKED_PASS steps;335 selected public theorem prints in17 completed
owners and19 headlines; final focused lpnNoise-opacity V3 pass;8 cleanup edit
records;50 current overlap-run source/log bindings; and fresh slot snapshot.
Exactly32 remaining-sorry warnings, zero other warnings. No proof/opacity success
is inferred from the historical c767 v1 failure or from a partial search suggestion.

Current anchors are fully refreshed, including all shifted LPN structure fields.
Four mathematical M0 tables are byte-exact. Full M0 stored/kernel/seal gates remain
historical; the V2 final-audit adapter candidates remain unrun. The focused V3 pass
is single-definition only, not canonical Rule10 coverage.

Artifacts:REPORT-M3.READYv2.md, report-provenance.READYv2.json,
current-anchor-appendix-M3-v2.md, current-declaration-anchors-M3-v2.tsv,
M3-originals-v2.md, M3-helpers-v2.md, archived-M0-tables.BYTE-EXACT.md,
finalize_ready_v2_readonly.py, SHA256SUMS.

The pure temp producer was executed only to verify existing root evidence and
render this packet. No Lean/Lake/Git/cache/gate/source edit/agent invocation occurred.
Active evidence/REPORT.md and all historical v1 artifacts remain untouched.
''')
files=sorted(p for p in B.iterdir() if p.is_file() and p.name!='SHA256SUMS')
(B/'SHA256SUMS').write_text(''.join(sha(p)+'  '+p.name+'\n' for p in files))
print('M3_READY_V2',len(s.splitlines()),'lines',sha(report),'26builds/335+19prints/focusV3PASS; delivery pending')
