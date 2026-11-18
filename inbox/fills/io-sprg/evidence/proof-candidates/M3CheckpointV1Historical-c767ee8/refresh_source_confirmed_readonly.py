"""Temp-only report refresh from root-confirmed source/evidence; no subprocesses."""
from pathlib import Path
import csv
import datetime
import hashlib
import json
import re

W = Path('/Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange')
B = Path('/private/tmp/io-sprg-proof-notes/tmpM3CheckpointDraft')
HEAD = 'c767ee867e76c0b1248cee46d4af5296ffa078d5'
AREA = 'TCSlib/Cryptography/Obfuscation/StructuredSeed/'
PREFIX = 'TCSlib.Cryptography.Obfuscation.StructuredSeed.'
sha = lambda path: hashlib.sha256(Path(path).read_bytes()).hexdigest()
invpath = W / 'evidence/checkpoints/M3/owner-inventory.json'
freeze_path = W / 'evidence/checks/M3-proof-complete-global-freeze/summary.json'
inv, freeze = json.loads(invpath.read_text()), json.loads(freeze_path.read_text())
assert inv['head'] == (W / 'evidence/checkpoints/M3/source-head.txt').read_text().strip() == HEAD
assert freeze['status'] == 'FROZEN_GLOBAL_HEADERS_AND_STATEMENT_PROSE_PASS'
assert freeze['current_owners'] == len(inv['files']) == 26
assert freeze['current_headers'] == 689 and freeze['frozen_headers'] == 670
assert len(freeze['moves']) == 14 and len(freeze['new_theorems_reported']) == 19
assert not freeze['globally_removed'] and not freeze['globally_changed_headers']
assert not freeze['approved_prose_updates']
files=[]
for rel in inv['files']:
    path=W/rel
    assert sha(path)==freeze['current_source_sha256'][rel]
    lines=path.read_text().splitlines()
    files.append({'file':rel,'sha256':sha(path),'lines':len(lines),
                  'max_width':max(map(len,lines),default=0)})
steps=[json.loads((W/f'evidence/steps/{i:03}/step.json').read_text()) for i in range(1,134)]
assert all(s['status']=='CHECKED_PASS' for s in steps)
assert sum(f['lines'] for f in files)==8657
assert max(f['lines'] for f in files)==801 and max(f['max_width'] for f in files)==100
originals=list(csv.DictReader((B/'M3-originals.WORKTREE.tsv').open(),delimiter='\t'))
helpers=list(csv.DictReader((B/'M3-helpers.WORKTREE.tsv').open(),delimiter='\t'))
assert len(originals)==10 and len(helpers)==13 and all(h['line']!='PENDING_INSERTION' for h in helpers)
step_map={(s['file'],s['name']):i for i,s in enumerate(steps,1)}

def rowname(row):
    return row['name'].removeprefix(PREFIX)

def table(rows,helper=False):
    result='| Declaration (area prefix omitted) | M3 source anchor | Saved step |\n| --- | --- | --- |\n'
    for row in rows:
        number=step_map[(row['file'],row['name'].split('.')[-1])]
        result+=f"| `{rowname(row)}` | `{row['file'].removeprefix(AREA)}:{row['line']}` | {number}: CHECKED_PASS |\n"
    return result

original_table=table(originals)
helper_table=table(helpers,True)
(B/'M3-originals.SOURCE-CONFIRMED.md').write_text(original_table)
(B/'M3-helpers.SOURCE-CONFIRMED.md').write_text(helper_table)
appendix=(B/'current-anchor-appendix.WORKTREE.md').read_text()
a=appendix.index('| Declaration (area prefix omitted)')
appendix='''## Current M3 source declaration anchors

These locations refer to root-confirmed source
`c767ee867e76c0b1248cee46d4af5296ffa078d5`. Every captured source hash matches
the root's proof-complete global freeze snapshot; the source-head file and owner
inventory identify the same commit. This preparation did not independently run Git.
The complete TSV retains explicit structure-field anchors from unchanged M2 files.
Generated constructors/recursors/inherited fields remain represented by their structure.
This lexical appendix is not a typed kernel census or proof-status table.

'''+appendix[a:]
(B/'current-anchor-appendix-M3.md').write_text(appendix)
(B/'current-declaration-anchors-M3.tsv').write_bytes((B/'current-declaration-anchors.WORKTREE.tsv').read_bytes())

s=(B/'REPORT-M3.DRAFT-PENDING.md').read_text()
start=s.index('## Claim 4.2 proof route')
newprefix='''# io-sprg Phase A — checkpoint 3 (M3), local gates pending

M3's ten original proof bodies and thirteen new theorem-only helpers are completed
in root-confirmed source `c767ee867e76c0b1248cee46d4af5296ffa078d5`.
All133 saved proof-step records are CHECKED_PASS. The final26-owner build and fresh
selected/headline axiom probes are still running/pending; **this report does not
claim all local gates or publication are complete**. M4–M6 and the full final proof
gates remain unfinished. T1–T6 remain the named Phase B efficiency hypotheses.

M0 was frozen at `d10a560b34d58919bc1a5206ce66a444613f94c7` and delivered at
exchange `15946b52d0615fda8afad9ed3c57cfaf5beaaa8d`. M1 source
`19dde91afc384656e7e47cb018057e088d4ded0a` was published at exchange
`10da7fdefd9a44023cc117a672f19e8a3617b81d`. M2 source
`4ecc40c04a001bc87349b7ec368ece309774c28a` was published at exchange
`c1d4f422f071f4a8e346d71a0f00ea3525941eee`. `evidence/delivery/M2.json`
records its successful non-force push, exact5,270-file payload path set and zero
committed SHA-256 mismatches. These remain historical M2 delivery results.

The source branch is `fill/io-sprg` on base
`5ed465f62e4ae0f93ded1a1ba49e807591b589eb`, without rebasing. Delivery writes
only `inbox/fills/io-sprg/` on `exchange/pass-shelat-ch5-8`.

## Source commits and confirmed proof scope

| M3 source checkpoint | Commit |
| --- | --- |
| First M3 source commit | `e966956e25caf9512050ddf5d480a5dec7f4d3de` |
| Second M3 source commit | `bc5d5227a52571ad5e1e9b86219cfcb4987b7771` |
| Proof-complete M3 source head | `c767ee867e76c0b1248cee46d4af5296ffa078d5` |

The final package's COMMITS.tsv must supply exact source-commit subjects and
metadata; no exchange delivery hash is inferred from these source hashes.

M3 fills all ten frozen original obligations (Load5 and Claim425) and adds thirteen
theorem-only helpers: six numerical bounds, six conditional probability bounds,
and one shared semantic joint-law reader. The reader avoids duplicating the same
sampler transport in the decomposition and Cond2 proof; Cond3 also reuses it.
It adds no algorithm or sampler. The decomposition consumer received a fresh root
check after this refactor. Cond2's repaired local index projection closes by rfl;
no projection equality or transport premise was added to a frozen statement.

| Confirmed source/proof quantity | Value | Evidence and limit |
| --- | --- | --- |
| Owned source modules, including both facades | 26 | Current M3 owner inventory; full build pending |
| Explicit source headers | 689 | Proof-complete global map; independent final static refresh pending |
| Frozen M0 headers and statement-prose prefixes | 670 unchanged | Global freeze PASS, no approved prose change |
| Cumulative new theorem-only helpers | 19 (M1 3 + M2 3 + M3 13) | Global map and source inventories; fresh axiom scope pending |
| Existing declarations relocated | 14 | Exact move ledger and retained per-file decls2 rows |
| Saved checked proof steps | 133 CHECKED_PASS | Read all evidence/steps/001–133/step.json records |
| Completed original bodies | 114 (M1 100 + M2 4 + M3 10) | Root-confirmed original/helper classification |
| Remaining original direct holes | 32 | Root-confirmed; no transitive sorryAx-dependent count inferred |
| Source size and width | 26 files;8,657 lines; largest801; width≤100 | Direct byte/line measurement, source hashes match freeze snapshot |

The proof-complete global freeze is a source-bound WORKTREE_CANDIDATE audit whose
capture preceded the final commit. This preparation checked every captured source
hash against the current files, and root confirmed their committed head as above.
It does not mislabel that guard as an independent Git HEAD or kernel-type audit.
The older progress.json still describes an earlier prefix and is not used as final
completion evidence. Source/build/static/axiom/slot gates remain separate.

'''
s=newprefix+s[start:]
a=s.index('## Original M3 declarations');b=s.index('## Module organization and frozen interface preservation',a)
s=s[:a]+'''## Original M3 declarations

These anchors and saved checked steps refer to the proof-complete M3 source.
Fresh all-owner build/axiom gates remain pending.

'''+original_table+'''
## New M3 theorem-only helpers

All thirteen helper bodies have saved CHECKED_PASS records. Fresh selected-owner
axiom checks and final overlap/admission evidence are distinct gates.

'''+helper_table+'\n'+s[b:]
s=s.replace('Final source line counts and exact import closure remain\npending the fresh dynamic inventory/static report.', 'The five Claim42 files measure102 facade,307 Defs,236 Bounds,368 Conditions and\n212 Load lines, respectively; every line has width≤96. The full exact import\nclosure/static refresh remains pending. No file exceeds1,000 lines.')
s=s.replace("Root ran the global guard successfully at an earlier M3 prefix. That source-bound\npass is archived in `evidence/checks/M3-prefix-global-freeze/` and subsequent prefix\ncaptures. It does not certify final source bytes, helper axioms or proof completion.", "Root's proof-complete global guard PASS is archived in\n`evidence/checks/M3-proof-complete-global-freeze/`. All26 captured source hashes\nmatch the current proof-complete files;670 frozen headers/prose prefixes are\npreserved, fourteen moves are exact and nineteen added helpers are separately\nreported. Kernel types/helper axioms remain separate gates.")
s=s.replace('| Final source head and exact 26-owner inventory | PENDING_ROOT_RECORDS |', '| Final source head and exact26-owner inventory | Root-confirmed c767ee867e76c0b1248cee46d4af5296ffa078d5; captured source hashes match proof-complete freeze |')
s=s.replace('| All 133 expected saved proof-step records CHECKED_PASS | PENDING_ROOT_RECORDS |', '| All133 saved proof-step records | Confirmed CHECKED_PASS by direct reading of all saved records |')
s=s.replace('| All ten original M3 bodies and thirteen new helpers, standard-only axioms | PENDING_ROOT_RECORDS |', '| Ten original bodies and thirteen helpers | Bodies have saved CHECKED_PASS; fresh standard-only axiom gate PENDING_ROOT_RECORDS |')
s=s.replace('| Global 670-header/prose freeze, exact fourteen moves, helper census | PENDING_ROOT_RECORDS |', '| Global670-header/prose freeze, exact fourteen moves, helper census | Proof-complete source-bound PASS;689 current headers,19 new helpers |')
a=s.index('## Current worktree declaration anchors');b=s.index('## Source and host disclosures',a)
s=s[:a]+appendix+'\n'+s[b:]
s=s.replace('M3 source proof completion, local gates, packaging and publication are **pending\nthis report\'s final refresh**. After root supplies the final records, bind every\nnew source anchor/hash and replace only evidence-backed pending entries.', 'M3 proof bodies and source anchors are now confirmed. Local gates, packaging and\npublication remain pending. After root supplies the final records, replace only\nevidence-backed pending entries; keep the current committed-source/hash binding.')
s=s.replace("The separate current appendix follows declaration identity and handles moved\nClaim42 declarations explicitly.", "The separate source-c767ee8 appendix follows declaration identity and handles moved\nClaim42 declarations explicitly.")
report=B/'REPORT-M3.SOURCE-CONFIRMED-GATES-PENDING.md';report.write_text(s)
# Preserve all four frozen mathematical tables exactly after all textual updates.
arch=(B/'archived-M0-tables.BYTE-EXACT.md').read_text()
tables=re.findall(r'(?:^\|[^\n]*\n){2,}',arch,re.M)
assert len(tables)==4 and all(t in s for t in tables)
assert 'PENDING_FINAL_M3_HEAD' not in s and 'PENDING_INSERTION' not in s
snapshot={'status':'SOURCE_AND_PROOF_STEPS_CONFIRMED_FRESH_LOCAL_GATES_PENDING',
 'source_head':HEAD,'source_head_authority':'Root message + source-head.txt + owner-inventory.json; no Git run by preparer',
 'captured_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'owners':26,'headers':689,'frozen_headers':670,'cumulative_helpers':19,'M3_helpers':13,
 'moves':14,'checked_pass_steps':133,'completed_originals':114,'remaining_original_holes':32,
 'lines':8657,'max_file_lines':801,'max_width':100,'source_files':files,
 'global_freeze_mode':freeze['mode'],'global_freeze_head_at_capture':freeze['HEAD_at_capture'],
 'global_freeze_all_current_source_hashes_match':True,
 'report_sha256':sha(report),'report_lines':len(s.splitlines()),
 'archived_exact_table_sha256':[hashlib.sha256(t.encode()).hexdigest() for t in tables],
 'evidence_sha256':{'evidence/checkpoints/M3/owner-inventory.json':sha(invpath),
 'evidence/checkpoints/M3/source-head.txt':sha(W/'evidence/checkpoints/M3/source-head.txt'),
 'evidence/checks/M3-proof-complete-global-freeze/summary.json':sha(freeze_path)},
 'gates_pending':['full26_owner_build','fresh_selected_334_theorems17owners','fresh19_headlines_expected6standard',
                  'final_static_refresh','slot_history','package_replay_bundle_manifests','publication'],
 'full_stored_census_and_rule10':'Historical M0 until final fresh gates',
 'active_REPORT_modified':False,'Lean_Git_cache_agents_source_mutation':False}
(B/'snapshot.SOURCE-CONFIRMED-GATES-PENDING.json').write_text(json.dumps(snapshot,indent=2,ensure_ascii=False)+'\n')
(B/'README.md').write_text((B/'README.md').read_text()+'''

Source-confirmed refresh:
- REPORT-M3.SOURCE-CONFIRMED-GATES-PENDING.md:root-confirmed c767ee8 source,
  all133 saved CHECKED_PASS records, actual8,657-line26-owner sizes, final anchors.
- current-anchor-appendix-M3.md/current-declaration-anchors-M3.tsv:new locations.
- snapshot.SOURCE-CONFIRMED-GATES-PENDING.json:source/evidence/report/table hashes.
- refresh_source_confirmed_readonly.py:pure temp producer executed for this update.

Full owner build, fresh334-selected/19-headline axioms, final static/slot and
publication remain pending. Do not use the older draft as the current version.
''')
allfiles=sorted(p for p in B.iterdir() if p.is_file() and p.name!='SHA256SUMS')
(B/'SHA256SUMS').write_text(''.join(sha(p)+'  '+p.name+'\n' for p in allfiles))
print('SOURCE_CONFIRMED_GATES_PENDING',HEAD,len(s.splitlines()),'report lines;26 owners/8657 lines')
