"""Read-only evidence verification and temp M3 report rendering. No subprocesses."""
from pathlib import Path
import collections
import csv
import datetime
import hashlib
import json
import re

W = Path('/Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange')
B = Path('/private/tmp/io-sprg-proof-notes/tmpM3CheckpointDraft')
HEAD = 'c767ee867e76c0b1248cee46d4af5296ffa078d5'
PREFIX = 'TCSlib.Cryptography.Obfuscation.StructuredSeed.'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
sha = lambda path: hashlib.sha256(Path(path).read_bytes()).hexdigest()
readj = lambda rel: json.loads((W / rel).read_text())

inv=readj('evidence/checkpoints/M3/owner-inventory.json')
static=readj('evidence/checks/m3-final/summary.json')
freeze=readj('evidence/checks/m3-final/freeze-summary.json')
global_freeze=readj('evidence/checks/m3-final/global-freeze/summary.json')
boundary=readj('evidence/checks/m3-final/boundary.json')
sizes=readj('evidence/checks/m3-final/sizes-widths.json')
axioms=readj('evidence/checkpoints/M3/axiom-summary.json')
slots=readj('evidence/host/M3-final/slot-summary.json')
for record in [inv,static,boundary,sizes,axioms]:assert record['head']==HEAD
assert freeze['current_head']==HEAD and freeze['changed']==freeze['removed']==0
assert freeze['statement_prose_unchanged'] and len(freeze['added_helpers'])==19
assert len(freeze['approved_moves'])==14
assert global_freeze['status']=='FROZEN_GLOBAL_HEADERS_AND_STATEMENT_PROSE_PASS'
assert global_freeze['current_headers']==689 and global_freeze['frozen_headers']==670
assert not global_freeze['globally_changed_headers'] and not global_freeze['globally_removed']
assert len(global_freeze['moves'])==14 and len(global_freeze['new_theorems_reported'])==19
assert static['owners']==len(inv['files'])==26 and static['decls']=={'ADDED':689}
assert static['lines']==8657 and static['all_widths_pass'] and not static['new_campaign_fail_warn']
for name,row in static['checks'].items():
    assert sha(W/f'evidence/checks/m3-final/{name}.log')==row['log_sha256']
    assert row['rc']==(1 if name=='campaign' else 0)
assert not boundary['forbidden_imports'] and not boundary['new_realization_variants']
assert not boundary['new_contract_variants'] and not boundary['pdf_paths']
assert set(boundary['changed'])==set(inv['files'])|{'TCSlib.lean'}

size_by_file={r['file']:r for r in sizes['files']}
assert set(size_by_file)==set(inv['files'])
assert sum(r['lines'] for r in size_by_file.values())==8657
assert max(r['lines'] for r in size_by_file.values())==801
assert max(r['max_width'] for r in size_by_file.values())==100
build=W/'evidence/build/M3/all-owners'
rows=[json.loads(l) for l in (build/'results.jsonl').read_text().splitlines()]
assert len(rows)==26 and len({r['module'] for r in rows})==26
assert {r['module']+'.lean' for r in rows}==set(inv['files'])
compiler_warnings=[]
for row in rows:
    rel=row['module']+'.lean';log=build/'mods'/(row['module'].replace('/','_')+'.log')
    assert row['head_at_start']==HEAD and row['rc']==row['errors']==row['error_forms']==0
    assert sha(W/rel)==row['source_sha256']==size_by_file[rel]['sha256']==global_freeze['current_source_sha256'][rel]
    assert sha(log)==row['log_sha256']
    assert sha(W/'.lake/io-sprg-oleans'/(row['module']+'.olean'))==row['object_sha256']
    assert not re.search(r'error[:(]',log.read_text())
    compiler_warnings.extend({'file':rel,'warning':line} for line in log.read_text().splitlines()
        if 'warning:' in line and 'sorry' not in line)
assert len(compiler_warnings)==12
m2sizes={r['file']:r for r in readj('evidence/checks/m2-final/sizes-widths.json')['files']}
assert all(size_by_file[r['file']]['sha256']==m2sizes[r['file']]['sha256'] for r in compiler_warnings)
steps=[readj(f'evidence/steps/{i:03}/step.json') for i in range(1,134)]
assert all(r['status']=='CHECKED_PASS' for r in steps)

assert axioms['public_theorem_prints']==334 and axioms['affected_owners']==17
assert axioms['all_standard_only'] and axioms['headlines']==19 and axioms['standard_only_headlines']==6
meta=[json.loads(l) for l in (W/'evidence/meta/M3-final/results.jsonl').read_text().splitlines()]
meta={r['module']:r for r in meta if 'module' in r}
for mod,probe in axioms['probes'].items():
    assert sha(W/probe['log'])==probe['log_sha256']==meta[mod]['log_sha256']
    assert sha(W/(mod+'.lean'))==meta[mod]['source_sha256']
    assert meta[mod]['rc']==meta[mod]['errors']==0
    log=(W/probe['log']).read_text()
    assert not re.search(r'error[:(]',log)
    got={}
    for m in re.finditer(r"^'(.+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log,re.M):
        assert m[1] not in got
        got[m[1]]=set(x.strip() for x in (m[2] or '').split(',') if x.strip())
    assert got=={n:set(a) for n,a in probe['axioms'].items()}
    assert len(got)==probe['theorems']
completed=axioms['probes']['evidence/probes/M3_AllCompletedAxioms']['axioms']
headline=axioms['probes']['evidence/probes/M3_HeadlineAxioms']['axioms']
assert all(set(a)<=STANDARD for a in completed.values())
assert sum(set(a)<=STANDARD for a in headline.values())==6
assert sum('sorryAx' in a for a in headline.values())==13
assert PREFIX+'Params.claim42' in headline and set(headline[PREFIX+'Params.claim42'])<=STANDARD
assert all(name in completed and set(completed[name])<=STANDARD for name in freeze['added_helpers'])

assert slots['status']=='PASS_WITH_EXACT_RECORDED_HISTORICAL_VIOLATION'
assert slots['acquisitions']==1231 and slots['max_concurrent_job_wrappers']==2
assert not slots['active'] and slots['all_tagged_wrapper_acquisitions_serial'] is False
assert slots['post_correction_serial'] is True
assert slots['post_correction']['acquisitions']==462 and slots['post_correction']['max_concurrent_job_wrappers']==1
assert sha(W/'evidence/host/M3-final/slots-io-sprg.log')==slots['extracted_log_sha256']

# Read each isolated M3 full/core search pair without executing tactics or materializers.
probes=sorted((W/'evidence/overlap/probes').glob('M3Load_*/search.json'))
assert len(probes)==23
search_status=collections.Counter()
for path in probes:
    record=json.loads(path.read_text())
    assert {r['mode'] for r in record['searches']}=={'exact','apply'}
    for search in record['searches']:
        mode=search['mode'];source=path.parent/(mode+'.lean.txt');log=path.parent/(mode+'.log')
        assert sha(source)==search['run']['source_sha256'] and sha(log)==search['run']['log_sha256']
        assert not re.search(r'^import .*StructuredSeed',source.read_text(),re.M)
        assert search['elaboration_errors']==[]
        search_status[search['status']]+=1

s=(B/'REPORT-M3.SOURCE-CONFIRMED-GATES-PENDING.md').read_text()
s=s.replace('# io-sprg Phase A — checkpoint 3 (M3), local gates pending', '# io-sprg Phase A — checkpoint 3 (M3)')
a=s.index("M3's ten original proof bodies");b=s.index('M0 was frozen',a)
s=s[:a]+'''M3 Claim 4.2 and all ten original M3 obligations are proved and locally checked at
`c767ee867e76c0b1248cee46d4af5296ffa078d5`. All26 owned modules pass the fresh
build, all133 saved proof steps are CHECKED_PASS, and all334 selected public
theorems in17 completed owners print only standard axioms. Six of19 current
headlines are standard-only, now including `Params.claim42`; thirteen later
headlines still retain sorryAx.

This is an intermediate proof checkpoint. **M3 packaging and publication remain
pending.** M4–M6 and the full final proof gates remain unfinished, with32 original
direct proof holes. T1–T6 remain the named, unproved Phase B efficiency hypotheses.
The complete end-to-end goal is not yet finished.

'''+s[b:]
s=s.replace('Fresh all-owner build/axiom gates remain pending.', 'The fresh all-owner build and completed-owner axiom probes pass at this source.')
s=s.replace('All thirteen helper bodies have saved CHECKED_PASS records. Fresh selected-owner\naxiom checks and final overlap/admission evidence are distinct gates.', 'All thirteen helper bodies have saved CHECKED_PASS records and are standard-only\nin the fresh completed-owner axiom probe. Their isolated name/shape and exact/apply\nsearch records are retained separately from the actual source proofs.')
s=s.replace('| Owned source modules, including both facades | 26 | Current M3 owner inventory; full build pending |', '| Owned source modules, including both facades | 26 | Exact current inventory; fresh full build pass |')
s=s.replace('| Explicit source headers | 689 | Proof-complete global map; independent final static refresh pending |', '| Explicit source headers | 689 | Fresh base→HEAD decls2:689 ADDED, zero CHANGED/REMOVED |')
s=s.replace('| Cumulative new theorem-only helpers | 19 (M1 3 + M2 3 + M3 13) | Global map and source inventories; fresh axiom scope pending |', '| Cumulative new theorem-only helpers | 19 (M1 3 + M2 3 + M3 13) | Global map; all nineteen are standard-only in fresh selected prints |')
s=s.replace('Source/build/static/axiom/slot gates remain separate.', 'Fresh source/build/static/selected-axiom/slot evidence is recorded below; the\ncomplete stored-root/kernel-type/canonical seal suite remains a later final gate.')
s=s.replace('The full exact import\nclosure/static refresh remains pending. No file exceeds1,000 lines.', 'The full static refresh passes. No file exceeds1,000 lines; the split adds only\nowned imports and no new external Mathlib root.')
s=s.replace('preserved, fourteen moves are exact and nineteen added helpers are separately\nreported. Kernel types/helper axioms remain separate gates.', 'preserved, fourteen moves are exact and nineteen added helpers are separately\nreported. The fresh static pass rebinds current source bytes to committed HEAD in\n`evidence/checks/m3-final/sizes-widths.json`. All nineteen helper axioms are\nstandard-only in the fresh selected probe; full generated kernel types remain a\nseparate final gate.')
a=s.index('## Current local checks and final-gate limits');b=s.index("M0's full stored-constant census",a)
s=s[:a]+'''## Current local checks and final-gate limits

| Check | Current M3 result and evidence |
| --- | --- |
| Exact-owner compilation | All26 expected owners, including both facades, pass with rc0 and zero errors in both forms. Every current source/log/object SHA matches; every record identifies c767ee8. `evidence/build/M3/all-owners/`. |
| Lean linter diagnostics | Twelve non-sorry linter warnings remain in unchanged M1/M2 files (LPN1, Degree1, Correctness4, Stretch6): unused simp/variable, unnecessary sequence syntax and dead/no-op ring tactics. They do not change rc0/zero-error outcomes. This is not a warning-free-build claim; the warnings and exact source lines are retained in the logs. |
| Saved proof steps | All133 `evidence/steps/001–133/step.json` records are CHECKED_PASS:114 original bodies and19 new helpers. Failed attempts/repairs remain archived; they are not counted as additional passes. |
| Selected theorem axioms | All334 selected source public theorems in17 completed owners use only propext, Classical.choice, Quot.sound (or subsets). This includes all ten M3 originals and all nineteen cumulative helpers. Fresh `evidence/checkpoints/M3/axiom-summary.json` binds both probe logs. |
| Headline axioms | Fresh19 prints: six standard-only (`Params.claim42`, `Params.G4_eval_eq`, `jls_hasComplexity`, `jls_hasPolyStretch`, `lpnNoise_law`, `PrimeSchedule.nonempty`); thirteen later headlines retain sorryAx. Exact sets are listed below. |
| Source declarations and frozen interface | Base→HEAD689 ADDED only, no CHANGED/REMOVED;670 frozen global headers/prose prefixes unchanged,14 exact ledgered moves,19 added helpers. `evidence/checks/m3-final/` retains per-file relocation rows and the global guard. |
| Style/campaign | Style, sk15 and widths pass; zero new individual campaign FAIL/WARN against the pinned base. Campaign rc1 is baseline-only. The unchanged15-line hasComplexityEff_iff lexical sk15 false positive and prior triage remain retained. |
| Sizes/names | 26 files,8,657 lines; largest801, maximum width100. Clash scan:689 OK, zero CLASH/DUP-NEW/MODIFIED. |
| Phase A/PDF boundary | Current scan has no forbidden import, new realization/contract variant, forbidden enumeration or PDF path; only the designated sampler-contract imports. `evidence/checks/m3-final/boundary.json`. Full all-intermediate-commit PDF verification remains a packaging check. |
| Overlap/reuse |23 isolated M3 full/core goals each have exact?/apply? records, with owned imports excluded and source/log hashes retained. The nonnegativity core closes directly by public prob_nonneg; partial/diagnostic outputs are not proofs. Details below. |
| Tagged wrapper history | Fresh18:56:43UTC audit:1,231 acquisitions, maximum two because the exact historical violation remains recorded;462 post-correction acquisitions have maximum one, seriality true, zero active wrappers. `evidence/host/M3-final/`. |

The current build, static, probe and slot records were read and hash-checked during
report preparation. Probe stdout's raw substring count is not a diagnostic count:
the completed probe has one occurrence in an identifier, but zero actual error
forms and rc0. No full-graph or canonical seal completion is inferred from these
selected source public-theorem probes.

'''+s[b:]
a=s.index('## Unchanged quantifiers, targets and earlier judgments')
overlap='''## Overlap and public API reuse

`evidence/overlap/M3-Load-name-shape/`,
`evidence/overlap/M3-Claim42-name-shape/`, and
`evidence/overlap/M3-joint-law-reader-name-shape/` retain the name/shape searches.
All23 current M3 mathematical goals have two source/log-bound isolated searches
in `evidence/overlap/probes/M3Load_*/`:46 tactic invocations total. Their imports
exclude StructuredSeed, so no existing owned sorried theorem can close its own
goal. Some are full generic statements; specialized sampler/record transports use
explicitly labelled mathematical cores, not claims of complete source elaboration.

The errProb_nonneg core closes under both exact? and apply? by the existing
`Games.ProbComp.prob_nonneg`; the actual frozen named wrapper composes that API
with its published reader. Other search outcomes are NO_CLOSING_PROOF,
PARTIAL_NOT_PROOF or DIAGNOSTIC_FAILURE with no pre-search elaboration errors.
None is treated as a theorem proof. The actual saved source bodies, full-owner
build and fresh334-theorem axioms are the proof evidence.

The original prefactor template's unused namespace opening failed the harness;
that invalid attempt remains under `evidence/overlap/invalid-single/` and was
superseded by a fresh namespace-correct v2 exact/apply pair. It is not counted
among the23 current goal pairs. Earlier M1/M2 immutable overlap audits retain their
published historical scopes.

The specialized new helper bodies compose the public finite expectation/product,
Markov, binomial/factorial, power-order and polynomial/exponential growth APIs.
`Params.jointLaw_prob_eq_uprob` factors the same concrete raw-draw transport once
for its three consumers; no copied generic probability identity or local contract
variant is introduced. No machine, fair-coin sampler or new algorithm is defined.

'''
s=s[:a]+overlap+s[a:]
s=s.replace('are **historical M0 anchors**; current draft anchors are indexed separately.', 'are **historical M0 anchors**; current committed-source anchors are indexed separately.')
a=s.index('The exact-exception slot checker preserves every tagged line');b=s.index('## Delivery and continuation',a)
s=s[:a]+'''The fresh exact-exception slot audit at18:56:43UTC preserves every tagged line
and REAP provenance. It records1,231 acquisitions, whole-history seriality false,
and maximum two tagged wrappers because the known three-second violation is not
erased. Its462 post-correction acquisitions have maximum one wrapper, seriality
true and no active wrappers. Every other overlap would fail the checker. These
are snapshot-qualified tagged wrapper facts, not a global host process cap,
actual simultaneous Lean-process census or complete child-process history proof.
`evidence/host/M3-final/slot-summary.json` gives the exact qualification and hashes.

'''+s[b:]
a=s.index('## Delivery and continuation')
s=s[:a]+'''## Current M3 headline axiom prints

Fresh19-headline probe at sourcec767ee8. All names below have the prefix
`TCSlib.Cryptography.Obfuscation.StructuredSeed.`. The exact logs and SHA-256
bindings are in `evidence/checkpoints/M3/axiom-summary.json`.

| Headline | Current printed axioms |
| --- | --- |
'''
for name,deps in headline.items():s+=f"| `{name.removeprefix(PREFIX)}` | `{', '.join(deps)}` |\n"
s+='''
## Remaining original obligations and continuation

The32 remaining direct original bodies comprise M4's eight hybrid/security
statements, eight shared M4/M6 reduction/encoding obligations, M5's seven raw
security/existence statements, and M6's nine target links/assemblies. Supporting
encoding proofs completed in M1 do not by themselves complete M6. No transitive
sorryAx-dependent count is inferred from this direct-hole count.

'''
anchors={r['name']:r for r in csv.DictReader((B/'current-declaration-anchors-M3.tsv').open(),delimiter='\t')}
frozen_obligations=list(csv.DictReader((W/'evidence/review/m0-report-sp-w2/proof-obligations.tsv').open(),delimiter='\t'))
remaining=[r for r in frozen_obligations if r['milestone'] in ['M4','M4 / M6','M5','M6']]
assert len(remaining)==32
s+='| Frozen milestone | Remaining declaration (area prefix omitted) | M3 source anchor |\n| --- | --- | --- |\n'
for row in remaining:
    a=anchors[row['Lean_name']]
    s+=f"| {row['milestone']} | `{row['Lean_name'].removeprefix(PREFIX)}` | `{a['file'].removeprefix('TCSlib/Cryptography/Obfuscation/StructuredSeed/')}:{a['line']}` |\n"
s+='''
## Delivery verification

M3 source proofs and local milestone gates are complete at
`c767ee867e76c0b1248cee46d4af5296ffa078d5`. **M3 packaging and publication
remain pending.** This READY report is ready for root's packager, not a claim that
an M3 payload has already been replayed, bundled, committed or pushed.

The packager must copy committed source; replay every patch at the pinned base
with exact commit hashes, including M0's empty marker; verify the bundle; check
every intermediate commit tree for PDFs; and verify exact source/evidence manifest
path sets and hashes. The future M3 `evidence/replay.json`, `bundle-verify.txt`,
`pdf-commit-trees.json`, `payload-source-binding.json`, COMMITS.tsv and exchange
publication record will be the delivery authority. No M3 delivery hash, successful
push or final ZIP is invented. Report SHA-256 is recorded externally in this
preparation's provenance, so no circular self-hash is embedded in REPORT.md.

Continue M4–M6 and then the full fresh stored-constant/kernel-type/canonical
four-variant seal/control gates. The candidate V2 tools remain unrun adaptations;
AST syntax checks are not gate passes. The four M0 mathematical tables are retained
byte-for-byte and their historical counts/anchors stay explicitly attributed.

No user question is pending. SP-W1 is resolved; SP-W2/SP-W3 and the disclosed
organization/process judgments remain available for downstream review. Report
preparation performed static reads and temporary writes only. It did not invoke
Lean, Lake, Git, cache tooling, source edits, final gates or agents. The pure temp
producer was executed only to verify existing root-produced records and render
this report/anchor/provenance packet; active evidence/REPORT.md is untouched.
'''
# Normalize only current prose; retain the four historical mathematical tables verbatim.
archived_text=(B/'archived-M0-tables.BYTE-EXACT.md').read_text()
protected=re.findall(r'(?:^\|[^\n]*\n){2,}',archived_text,re.M)
for i,tab in enumerate(protected):s=s.replace(tab,f'ARCHIVED_TABLE_{i}_BYTE_EXACT',1)
for before,after in {
 'All26':'All 26','all26':'all 26','All133':'All 133','all133':'all 133',
 'all334':'all 334','All334':'All 334','in17':'in 17','of19':'of 19','with32':'with 32',
 'exact5,270':'exact 5,270','Load5 and Claim425':'five Load and five Claim42 obligations',
 'decls2:689':'decls2: 689','files;8,657':'files; 8,657','largest801':'largest 801',
 'file801':'file 801','measure102':'measure 102',',307':', 307',',236':', 236',
 ',368':', 368','exceeds1,000':'exceeds 1,000','files,8,657':'files, 8,657',
 'width100':'width 100','width≤100':'width ≤ 100','width≤96':'width ≤ 96',
 'records;670':'records; 670','files;670':'files; 670','report;670':'report; 670',
 'Base→HEAD689':'Base→HEAD 689','689 ADDED, zero':'689 ADDED, zero',
 'REMOVED;670':'REMOVED; 670','unchanged,14':'unchanged, 14','moves,19':'moves, 19',
 'CHECKED_PASS:114':'CHECKED_PASS: 114','bodies and19':'bodies and 19','Fresh19':'Fresh 19',
 'unchanged15-line':'unchanged 15-line','logs. |\n| Overlap/reuse |23':'logs. |\n| Overlap/reuse | 23',
 '| Overlap/reuse |23':'| Overlap/reuse | 23','Fresh18:56':'Fresh 18:56','audit:1,231':'audit: 1,231',
 'recorded;462':'recorded; 462','were22':'were 22',',88':', 88','plus96':'plus 96',
 ',1036':', 1036','and511':'and 511','All23':'All 23','`:46':'`: 46',
 'fresh334':'fresh 334','sourcec767':'source c767','Fresh19-headline':'Fresh 19-headline',
 'at18:56':'at 18:56','records1,231':'records 1,231','Its462':'Its 462',
 'The32':'The 32','this draft makes':'this report makes','LPN1, Degree1, Correctness4, Stretch6':'LPN 1, Degree 1, Correctness 4, Stretch 6'
}.items():s=s.replace(before,after)
for i,tab in enumerate(protected):s=s.replace(f'ARCHIVED_TABLE_{i}_BYTE_EXACT',tab)
s=s.replace('## Source commits and confirmed proof scope', '''## Milestones

Cumulative source line counts refer to each named historical source checkpoint.

| Milestone | Status | Source commit | Cumulative source lines |
| --- | --- | --- | --- |
| M0 statements | Frozen and published | `d10a560b34d58919bc1a5206ce66a444613f94c7` | 5,911 (22 owners) |
| M1 algebraic correctness | Complete and published | `19dde91afc384656e7e47cb018057e088d4ded0a` | 7,244 (23 owners) |
| M2 stretch | Complete and published | `4ecc40c04a001bc87349b7ec368ece309774c28a` | 7,694 (23 owners) |
| M3 Claim 4.2 | Proofs/local gates complete; packaging/publication pending | `c767ee867e76c0b1248cee46d4af5296ffa078d5` | 8,657 (26 owners) |
| M4 hybrids/reductions | Unfinished | No completion commit | Not measured as complete |
| M5 raw security/existence | Unfinished | No completion commit | Not measured as complete |
| M6 target links/assemblies | Unfinished; target truth stays Phase B | No completion commit | Not measured as complete |

## Source commits and confirmed proof scope''')
s=s.replace('## Remaining original obligations and continuation', '''## Size re-estimate

Current source is 8,657 lines, 207 above the original expected upper estimate of
8,450, while every file remains below the hard 1,000-line limit. M3 adds 963 lines
to M2's 7,694: the five load proofs, the thirteen specialized theorem-only helpers,
the five original Claim42 proofs and the three new module headers. This reflects
proof size and modular organization within the requested scope.

A provisional final estimate is 9,500–12,500 lines while the remaining 32 reduction,
security and target-link proofs are completed. This is a planning range, not a
completion claim or permission to add scope; M4's explicit realiser/averaging
transports dominate its uncertainty. Additional splits must preserve FQNs/frozen
headers/prose, exact move ledgers and complete final owner coverage. The final
measured source inventory will supersede this estimate.

## Remaining original obligations and continuation''')
report=B/'REPORT-M3.READY.md';report.write_text(s)
archived=(B/'archived-M0-tables.BYTE-EXACT.md').read_text()
tables=re.findall(r'(?:^\|[^\n]*\n){2,}',archived,re.M)
assert len(tables)==4 and all(t in s for t in tables)
assert not re.search(r'PENDING_[A-Z_]+|PLACEHOLDER|FILL_ME',s)
assert 'local gates pending' not in s and 'Fresh all-owner build/axiom gates remain pending' not in s
inputs=['evidence/checkpoints/M3/owner-inventory.json','evidence/checkpoints/M3/source-head.txt',
'evidence/checks/m3-final/summary.json','evidence/checks/m3-final/freeze-summary.json',
'evidence/checks/m3-final/global-freeze/summary.json','evidence/checks/m3-final/sizes-widths.json',
'evidence/checks/m3-final/boundary.json','evidence/checkpoints/M3/axiom-summary.json',
'evidence/build/M3/all-owners/results.jsonl','evidence/meta/M3-final/results.jsonl',
'evidence/host/M3-final/slot-summary.json','evidence/host/M3-final/slots-io-sprg.log']
provenance={'status':'READY_M3_PROOFS_AND_LOCAL_GATES_COMPLETE_DELIVERY_PENDING',
'source_head':HEAD,'report_sha256':sha(report),'report_lines':len(s.splitlines()),
'captured_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
'owners':26,'headers':689,'frozen_headers':670,'moves':14,'cumulative_helpers':19,
'M3_originals':10,'M3_helpers':13,'checked_pass_steps':133,'completed_originals':114,
'remaining_original_holes':32,'lines':8657,'max_file':801,'max_width':100,
'fresh_selected_theorems':334,'fresh_selected_owners':17,'fresh_headlines':19,
'fresh_standard_headlines':6,'fresh_sorry_headlines':13,
'existing_non_sorry_Lean_linter_warnings':compiler_warnings,
'fresh_slot_acquisitions':1231,'fresh_slot_max_wrappers':2,
'fresh_slot_post_correction_acquisitions':462,'fresh_slot_post_correction_serial':True,
'overlap_current_goals':23,'overlap_current_tactic_runs':46,'overlap_statuses':dict(search_status),
'archived_exact_table_sha256':[hashlib.sha256(t.encode()).hexdigest() for t in tables],
'evidence_sha256':{rel:sha(W/rel) for rel in inputs},
'full_stored_kernel_census_and_seals':'HISTORICAL_M0_FINAL_FRESH_GATES_PENDING',
'candidate_V2_tools':'UNRUN; syntax only; standalone global freeze root-reported pass',
'M3_packaging_publication':'PENDING; report self-hash external only',
'active_REPORT_modified':False,'preparer_Lean_Git_cache_source_agents':False}
(B/'report-provenance.READY.json').write_text(json.dumps(provenance,indent=2,ensure_ascii=False)+'\n')
(B/'README.md').write_text('''# M3 READY report packet

REPORT-M3.READY.md is the current complete report: source c767ee8 proofs and local
milestone gates pass; M3 packaging/publication and full final gates remain pending.
report-provenance.READY.json and SHA256SUMS bind all inputs/report/table bytes.

Validation performed here:static reads/hash comparisons of root-produced26-owner
source/log/object build results, static/global source freeze,334 selected theorem
prints in17 completed owners plus19 headlines, all133 saved CHECKED_PASS records,
23 isolated M3 exact/apply goal pairs, and the fresh tagged-wrapper snapshot.
No Lean, Lake, Git, cache, source edits, final gate executions or agents were run.
Pure temp producers were executed only for evidence verification/report rendering.

The four archived M0 mathematical tables are byte-exact. Full M0 kernel/Rule10
results stay historical; the V2 candidate adapters remain unrun. Twelve existing
Lean linter warnings in unchanged M1/M2 files are disclosed; rc0/zero-error passes
are not described as warning-free. Active evidence/REPORT.md is untouched.

Current artifacts:
- REPORT-M3.READY.md and report-provenance.READY.json.
- current-anchor-appendix-M3.md/current-declaration-anchors-M3.tsv.
- M3-originals.SOURCE-CONFIRMED.md/M3-helpers.SOURCE-CONFIRMED.md.
- archived-M0-tables.BYTE-EXACT.md.
- finalize_ready_readonly.py:current pure temp evidence/render producer.

Earlier DRAFT/PENDING/SOURCE-CONFIRMED artifacts are retained historical preparation
snapshots, superseded by READY; their status text must not replace the current one.
''')
files=sorted(p for p in B.iterdir() if p.is_file() and p.name!='SHA256SUMS')
(B/'SHA256SUMS').write_text(''.join(sha(p)+'  '+p.name+'\n' for p in files))
print('M3_READY',len(s.splitlines()),'lines',sha(report),'334+19freshprints; package/publication pending')
