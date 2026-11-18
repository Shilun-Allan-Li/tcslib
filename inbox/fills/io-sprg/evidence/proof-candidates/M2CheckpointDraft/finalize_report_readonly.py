from pathlib import Path
import hashlib, json, re, runpy

B = Path('/private/tmp/io-sprg-proof-notes/M2CheckpointDraft')
W = Path('/Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange')
runpy.run_path(str(B / 'prepare_readonly.py'))
HEAD = '4ecc40c04a001bc87349b7ec368ece309774c28a'
PREFIX = 'TCSlib.Cryptography.Obfuscation.StructuredSeed.'

def read(rel):
    return (W / rel).read_text()

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

static = json.loads(read('evidence/checks/m2-final/summary.json'))
freeze = json.loads(read('evidence/checks/m2-final/freeze-summary.json'))
boundary = json.loads(read('evidence/checks/m2-final/boundary.json'))
axioms = json.loads(read('evidence/checkpoints/M2/axiom-summary.json'))
slots = json.loads(read('evidence/host/M2-final/slot-summary.json'))
assert all(d['head'] == HEAD for d in [static, boundary, axioms])
assert freeze['current_head'] == HEAD
assert static['decls'] == {'ADDED': 676} and static['lines'] == 7694
assert static['new_campaign_fail_warn'] == [] and static['all_widths_pass']
assert freeze['changed'] == freeze['removed'] == 0 and len(freeze['added_helpers']) == 6
assert not boundary['forbidden_imports'] and not boundary['new_realization_variants']
assert not boundary['new_contract_variants'] and not boundary['pdf_paths']
assert axioms['public_theorem_prints'] == 306 and axioms['affected_owners'] == 12
assert axioms['all_standard_only'] and axioms['headlines'] == 19
assert axioms['standard_only_headlines'] == 5
assert slots['acquisitions'] == 1118 and slots['max_concurrent_job_wrappers'] == 2
assert slots['active'] == {} and slots['post_correction_serial']
assert slots['status'] == 'PASS_WITH_EXACT_RECORDED_HISTORICAL_VIOLATION'
for probe in axioms['probes'].values():
    assert sha(W / probe['log']) == probe['log_sha256']
for name, check in static['checks'].items():
    assert sha(W / f'evidence/checks/m2-final/{name}.log') == check['log_sha256']

snap = json.loads((B / 'snapshot.json').read_text())
for rel in ['evidence/checks/m2-final/summary.json',
            'evidence/checks/m2-final/freeze-summary.json',
            'evidence/checks/m2-final/boundary.json',
            'evidence/checks/m2-final/campaign-diff.json',
            'evidence/checkpoints/M2/axiom-summary.json',
            'evidence/host/M2-final/slot-summary.json']:
    snap['evidence_sha256'][rel] = sha(W / rel)
snap['fresh_M2_completed_theorem_prints'] = 306
snap['fresh_M2_completed_axiom_owners'] = 12
snap['fresh_M2_all_completed_theorems_standard_only'] = True
snap['fresh_M2_headlines'] = 19
snap['fresh_M2_standard_only_headlines'] = 5
snap['fresh_M2_sorry_headlines'] = 14
snap['current_source_named_commands_base_to_head_added_only'] = 676
snap['frozen_M0_headers_changed'] = snap['frozen_M0_headers_removed'] = 0
snap['current_new_helpers_cumulative'] = freeze['added_helpers']
snap['fresh_slot_audit'] = {k: slots[k] for k in [
    'as_of', 'acquisitions', 'max_concurrent_job_wrappers', 'active',
    'post_correction_serial', 'post_correction', 'status', 'qualification']}
(B / 'snapshot.json').write_text(json.dumps(snap, indent=2, ensure_ascii=False) + '\n')

addendum = (B / 'ADDENDUM-M2.md').read_text()
a = addendum.index('The M1 **297 standard-only')
b = addendum.index('## Preserved fidelity', a)
addendum = addendum[:a] + '''Fresh M2 probes print **all306 public theorems in12 completed owners**, and all
are standard-only. The19 current headline prints have exactly five standard-only
results (`G4_eval_eq`, `jls_hasComplexity`, `jls_hasPolyStretch`, `lpnNoise_law`,
`PrimeSchedule.nonempty`) and14 retaining sorryAx.
`evidence/checkpoints/M2/axiom-summary.json` binds both fresh logs. This supersedes
the M1-only297-theorem scope without turning either selected probe into a full
stored-constant census.

Fresh `evidence/checks/m2-final/` reports676 ADDED source declarations only,
zero frozen M0 headers changed/removed, exactly six cumulative new helpers,
zero clashes, passing style/sk15/width checks, and no new individual campaign
FAIL/WARN against the base (the campaign command itself retains baseline rc1).
The Phase A boundary scan records no forbidden import or new realization/contract
variant. These are current M2 static results.

The fresh tagged-wrapper audit at `evidence/host/M2-final/slot-summary.json` records
1118 acquisitions, maximum two wrappers because it preserves the known historical
violation,349 post-correction acquisitions with maximum one, post-correction
seriality true, and zero active wrappers. Its qualification excludes global host
or complete child-process-history claims. The two historical instruction breaches
remain disclosed in the full report.

The canonical full stored-constant census, typed statement dump, dependency graph,
four-variant seals and paired controls remain **historical M0 evidence, with the
final fresh gates pending**. The M0 results were88 seals plus96 controls (184 passes)
for the then22 owners; they are not M2 proof passes. The final dynamic inventory
must include Basic and any later owned helper/split modules. No transitive
sorryAx-dependent count is inferred from the42 remaining direct holes.

''' + addendum[b:]
(B / 'ADDENDUM-M2.md').write_text(addendum)

m1 = read('evidence/checkpoints/M1/REPORT.md')
def section(start, end):
    return start + m1.split(start, 1)[1].split(end, 1)[0]

prefix = '''# io-sprg Phase A — checkpoint 2 (M2)

M2 polynomial stretch is proved and locally checked at
`4ecc40c04a001bc87349b7ec368ece309774c28a`. M1 was published at exchange commit
`10da7fdefd9a44023cc117a672f19e8a3617b81d`, from source
`19dde91afc384656e7e47cb018057e088d4ded0a`. M0 remains frozen at
`d10a560b34d58919bc1a5206ce66a444613f94c7`, delivered at
`15946b52d0615fda8afad9ed3c57cfaf5beaaa8d`.

This is an intermediate proof checkpoint. M2 proof work and local gates are
complete; its packaging and publication remain pending. M3–M6 remain unfinished,
with **42 original direct proof holes**. T1–T6 remain unproved Phase B targets.
The whole end-to-end goal and final proof gates remain open.

## Bases, heads and milestone scope

The source branch is local `fill/io-sprg`, based on
`5ed465f62e4ae0f93ded1a1ba49e807591b589eb` (`iO/phase-a-base`), without rebasing.
The delivery branch writes only `inbox/fills/io-sprg/` on
`exchange/pass-shelat-ch5-8`.

| Milestone | Status | Source commit |
| --- | --- | --- |
| M0 | Frozen and published | `d10a560b34d58919bc1a5206ce66a444613f94c7` |
| M1 | Complete and published at exchange10da7fdefd9a44023cc117a672f19e8a3617b81d | `19dde91afc384656e7e47cb018057e088d4ded0a` |
| M2 | All four original bodies, three new helpers and local gates complete; delivery pending | `4ecc40c04a001bc87349b7ec368ece309774c28a` |
| M3 | Claim4.2/load bounds: all ten original obligations next | Pending |
| M4 | Hybrids/reductions, including shared M4/M6 support | Pending |
| M5 | Raw security and existence | Pending |
| M6 | Target links/conditional assemblies | Pending |

M1 filled100 original bodies (83 foundational/M1 plus17 encoding support obligations)
and added three theorem-only helpers. Its103 checked steps cover Degree24,
Params14, Encoding17, LPN3, Buckets7, SparseFactor5, Polys10, Correctness18,
the Defs efficiency-forgetting bridge, the Samplers prime-width bridge, Basic2,
and the G4 seed-support helper. Supporting encodings done early do not complete M6.

M2 fills four more original bodies and adds three theorem-only helpers. The
cumulative record is **104 original bodies + six helpers =110 CHECKED_PASS steps**.
Failed attempts and their repaired records remain in evidence; only final checked
states are counted. No transitive sorryAx-dependent count is inferred from the
42 remaining direct holes.

## M2 stretch proof route

''' + (B / 'current-Stretch-anchors.md').read_text().split('\n\n', 1)[1] + '''
The four original M2 obligations are Params.seedBitsAt_le, jls_seedBits_eq,
jls_seedBits_le and jls_hasPolyStretch (steps104,105,106,110). The new Internal
helpers w_lower, stretch_gaps and eventually_seed_relative_gap are steps107–109.
All nine public Stretch theorem prints, including the two existing readers,
are standard-only at the current source hash.

The seed estimate uses `C = 2*(2^P.D)+12`, covers integral rounding and κ=0,
and is independent of the prime schedule. The noise-width lower bound and E0
threshold supply positive exponent gaps. The relative-gap helper yields
`seedBitsAt κ ≤ m κ * κ^(-ε)` eventually.

The final proof keeps the actual coefficient from public
`Complexity.PolyExpr.eval_le`, sets `D = max 1 ((C:ℝ)*2^c)` and
`η = ε/(2*(c+1))`, then absorbs `D^η` through the existing real-power growth API.
The old generic monic-normalization candidates02/06 were rejected and are not the
implemented proof route. The public API is composed rather than rederived as a
new generic monic-normalization theorem. No new algorithm, machine, sampler,
efficiency claim, or frozen statement is introduced by these helpers.
`evidence/checkpoints/M2/helper-plan.md` records the route.

SP-W1 keeps δ rational in construction data, coerced to real for these analytic
bounds. SP-W3's growth conjunct is proved as well as the power bound: the actual
construction has `κ+1 ≤ seedBits κ` for every κ, hence `κ ≤ seedBits κ` beyond the
common cutoff. No positive-κ premise is added to the frozen stretch theorem.

## Current local checks and their limits

| Check | Current M2 result and evidence |
| --- | --- |
| Owner compilation | Exact set of23 owners, including both facades: rc0, zero errors in both forms. `evidence/build/M2/all-owners/results.jsonl`; all23 actual source/log/object hashes match, and every record names source4ecc40c. |
| Completed theorem axioms | All306 public theorem prints in12 completed owners use only propext, Classical.choice, Quot.sound (or subsets). Fresh `evidence/checkpoints/M2/axiom-summary.json`. |
| Headline axioms | Fresh19 prints: exactly five standard-only (G4_eval_eq, jls_hasComplexity, jls_hasPolyStretch, lpnNoise_law, PrimeSchedule.nonempty);14 later headlines retain sorryAx, listed below. |
| Source declarations | Base-to-head676 ADDED, zero CHANGED/REMOVED; zero clashes. All670 frozen M0 headers unchanged, exactly six cumulative new helpers. `evidence/checks/m2-final/`. |
| Style/campaign | Style, sk15 and widths pass. No new individual campaign FAIL/WARN against the pinned base; campaign rc1 is baseline-only. The unchanged15-line hasComplexityEff_iff lexical statement flag and triage remain retained. |
| Size/width | 23 owned files,7694 lines; maximum file801 lines, maximum width100. Stretch576 lines, maximum width90. |
| Phase A boundary | No forbidden new import, realization/contract variant, forbidden enumeration, machine or sampler construction. Only the existing target-conditioned primitive assemblies. `evidence/checks/m2-final/boundary.json`. |
| Saved proof steps | All110 `evidence/steps/*/step.json` records are CHECKED_PASS. Original completed104, new helpers6, original holes42. |
| Focused opacity history | The M1 Correctness foreign-jlsSPRG_raw opacity diagnostic passed in `evidence/meta/M1-focused-raw-opacity/`. It remains historical M1 evidence, not a fresh M2 canonical seal. |

The full stored-constant census, typed StmtDump, sorryAx dependency graph, full
four-variant canonical seals and paired controls **have not been rerun at M2**.
Their delivered M0 artifacts are historical evidence for M0 only:22 owners,
88 seals plus96 controls, all184 passed;1036 stored constants,948 public kernel
types and511 theorem prints were checked there. They are not current M2 counts
or proof passes. The final gate must regenerate an exact dynamic owner inventory
(including Basic and any later split modules), all stored roots, controls,
request masks/environment bindings and all four variants. The detailed tooling
coverage audit remains in `evidence/proof-candidates/tmpFinalAuditTools/`.

This checkpoint carries partial final-gate evidence, as allowed for intermediate
milestones. Neither306 selected theorem prints nor676 explicit source commands
are a full kernel census; actual final transitive counts must come from the
fresh kernel graph, not subtraction from M0.

'''

judgment = section('## Statement changes and judgment calls', '## Overlap and reuse')
judgment = judgment.replace('The three new helpers are:', 'The six cumulative theorem-only helpers are:')
needle = '| Params.G4_seed_allOutputs | Retains the literal G4 polynomial witness on the exact seed law for both complexity links. |'
judgment = judgment.replace(needle, needle + '''
| Internal.w_lower | Lower-bounds rounded noise width by half its real-power schedule at κ≥1. |
| Internal.stretch_gaps | Extracts positive public/noise exponent gaps from the explicit E0 threshold. |
| Internal.eventually_seed_relative_gap | Combines the rounded payload estimate and exponent gaps into a prime-independent relative seed bound. |''')
judgment = judgment.replace('It adds no external module or Mathlib cache root; the refreshed closure has128\nmodules and the same83 direct Mathlib roots.', 'At M1 it added no external module or Mathlib cache root; the refreshed M1 closure\nhad128 modules and the same83 direct Mathlib roots. M2 adds no import root.')
judgment = judgment.replace('Current size is7244 lines.', 'Current size is7694 lines.')

overlap = section('## Overlap and reuse', '## Source and host provenance; process-limit disclosures')
overlap = overlap.replace('The current immutable-log review covers218', 'The archived M1 immutable-log review covers218')
overlap += '''The M2 stretch route uses public PolyExpr coefficient bounds, floor bounds and
real-power growth/composition APIs. Retaining the actual output coefficient avoids
the discarded generic monic-normalization overlap. Current M2 source uses the three
owned theorem-only helpers inventoried above; source status and fresh check logs
are the authority, rather than untested preparation packets.

'''

host = section('## Source and host provenance; process-limit disclosures', '## Frozen fidelity, Rule15 and non-vacuity tables')
host = host.replace("The checker in `evidence/host/M1-final/` preserves the exact incident and REAP\nprovenance:1068 tagged acquisitions, maximum two wrappers, historical seriality false,\npost-correction tagged seriality true, zero active wrappers at its snapshot.", "The fresh checker in `evidence/host/M2-final/` preserves the exact incident and REAP\nprovenance:1118 tagged acquisitions, maximum two wrappers, historical seriality false,\n349 post-correction acquisitions with maximum one wrapper, post-correction tagged\nseriality true, and zero active wrappers at its 17:45:27UTC snapshot.")

fidelity = section('## Frozen fidelity, Rule15 and non-vacuity tables', '## Current declaration anchors for the archived tables')
fidelity = fidelity.replace('The current M1 anchor', 'The current M2 anchor')
anchors = (B / 'current-anchor-appendix-M2.md').read_text() + '\n'
targets = section('## Phase B target statements (unproved)', '## Current headline axiom prints')

headlines = '''## Current M2 headline axiom prints

Fresh19-headline probe at source4ecc40c; exactly five standard-only and14 retaining
sorryAx. All names below have the area prefix
`TCSlib.Cryptography.Obfuscation.StructuredSeed.`. Exact printed dependencies and
log hashes are recorded in `evidence/checkpoints/M2/axiom-summary.json`.

| Headline | Current printed axioms |
| --- | --- |
'''
for name, dependencies in axioms['probes']['evidence/probes/M2_HeadlineAxioms']['axioms'].items():
    headlines += f"| `{name.removeprefix(PREFIX)}` | `{', '.join(dependencies)}` |\n"
headlines += '\n'

commits = section('## Source commits', '## Delivery verification and continuation')
commits = commits.replace('Every source commit from the pinned base is listed below. Exact author/committer metadata and signing status are in `patches/COMMITS.tsv`.', 'The table below preserves the M0/M1 source-commit history from the published M1\nreport. M2 adds source checkpoint `4ecc40c04a001bc87349b7ec368ece309774c28a`. Exact\nfinal source-commit subjects, author/committer metadata and signing status must be\nbound by the M2 package\'s `patches/COMMITS.tsv`; no delivery hash is inferred from a\nsource hash.')

delivery = '''## Delivery verification and continuation

M1 is published at exchange commit
`10da7fdefd9a44023cc117a672f19e8a3617b81d`; the source head is
`19dde91afc384656e7e47cb018057e088d4ded0a`.
`evidence/delivery/M1.json` records5040 payload files, exact committed path-set
verification, zero committed SHA-256 mismatches and successful non-force push.
The Unicode-path verifier correction is retained in that record.

M2 source is committed at `4ecc40c04a001bc87349b7ec368ece309774c28a`, with proof and
local gates complete. **M2 packaging and publication are pending.** The packager
must stage only this unit's payload, replay every patch at the pinned base with
exact hash equality (including the empty M0 marker), verify the bundle, check all
intermediate commit trees for PDFs, and check exact manifest path sets and hashes.
It must copy committed source, not unstaged files. M2's fresh `evidence/replay.json`,
`bundle-verify.txt`, `pdf-commit-trees.json` and `payload-source-binding.json` will be
the packaging authority. No M2 delivery hash, successful push or final ZIP is
claimed before those records exist.

Continue with **all ten original M3 obligations**, listed in the table below from
the frozen proof-obligation TSV, then M4–M6 and the full final gates. The M3 final
Claim42 cutoff must be independent of the public prime parameter.

'''
delivery += (B / 'M3-next-obligations.md').read_text().split('| Original full name', 1)[1]
delivery = delivery.replace('\n (area prefix omitted)', '\n (area prefix omitted)')
# Restore the first table header omitted by the split, without duplicating the prose.
delivery = delivery.replace('\n (area prefix omitted) | Current source anchor |', '\n| Original full name (area prefix omitted) | Current source anchor |')
if '\n| Original full name' not in delivery:
    delivery = delivery.replace('(area prefix omitted) | Current source anchor |', '| Original full name (area prefix omitted) | Current source anchor |', 1)
delivery += '''
No user question is pending. SP-W1 is resolved; SP-W2/SP-W3 and the disclosed
organization/process decisions remain recorded for downstream review. The report
preparation itself performed static reads and temporary writes only; it did not
run Lean, Git, cache tooling, source edits or agents.
'''

report = prefix + judgment + overlap + host + fidelity + anchors + targets + headlines + commits + delivery
# Four archived mathematical tables must remain byte-for-byte equal to M1.
def tables(text):
    return re.findall(r'(?:^\|[^\n]*\n){2,}', text, re.MULTILINE)
old_tables = tables(fidelity)
assert len(old_tables) == 4, len(old_tables)
for table in old_tables:
    assert table in report
assert 'M2–M6 remain unfinished' not in report
assert 'Current size is7244' not in report
assert 'Continue with all four M2' not in report
assert 'M2 | Stretch: four original obligations remain' not in report
assert 'FILL' not in report and 'PLACEHOLDER' not in report
(B / 'REPORT-M2.READY.md').write_text(report)

provenance = {
 'status': 'COMPLETE_READ_ONLY_READY_REPORT_M2_DELIVERY_PENDING',
 'source_head': HEAD,
 'M1_report_sha256': sha(W / 'evidence/checkpoints/M1/REPORT.md'),
 'ready_report_sha256': sha(B / 'REPORT-M2.READY.md'),
 'ready_report_lines': len(report.splitlines()),
 'archived_exact_table_sha256': [hashlib.sha256(t.encode()).hexdigest() for t in old_tables],
 'fresh_completed_prints': 306, 'fresh_headlines': 19,
 'fresh_standard_headlines': 5, 'fresh_sorry_headlines': 14,
 'full_kernel_census_and_canonical_seals': 'HISTORICAL_M0_FINAL_PENDING',
 'active_REPORT_modified': False,
 'note': 'M2 source/build/static/axiom/slot evidence read; no Lean/Git/cache/agents invoked.'
}
(B / 'report-provenance.json').write_text(json.dumps(provenance, indent=2) + '\n')
(B / 'README.md').write_text((B / 'README.md').read_text() + '''
Finalized full report:
- REPORT-M2.READY.md: complete current M2 report assembled from the M1 archive,
  all four frozen mathematical tables byte-exact and explicitly historical,
  current M2 anchors, fresh306/19 axiom scope, fresh static gates and slot audit.
- report-provenance.json: source/archive/report hashes and exact table digests.
- finalize_report_readonly.py: static finalizer; reads fresh root-produced records only.

No placeholders remain. M2 delivery remains pending by design; the root must replace
that publication status only after its actual package/push record exists.
''')
manifest = ''.join(sha(p) + '  ' + p.name + '\n' for p in sorted(B.iterdir()) if p.is_file() and p.name != 'SHA256SUMS')
(B / 'SHA256SUMS').write_text(manifest)
print(json.dumps(provenance, indent=2))
