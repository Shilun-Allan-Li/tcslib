# io-sprg report finalizer, Mac host 2026-11-18. No Lean or Git mutation.
# Invoke only after all current M0 gates pass and the exact M0 marker is committed.
from pathlib import Path
import collections,hashlib,json,re,runpy,subprocess
root=Path.cwd();r=root/'evidence/rule10/m0_final';head=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();base='5ed465f62e4ae0f93ded1a1ba49e807591b589eb'
assert hashlib.sha256(Path('/private/tmp/io-sprg-tools/lean-slot.sh').read_bytes()).hexdigest()=='ff64d8d5b6baf4e7b1c15172a7faeb70246f22c6acf76134bbdb70c017f41f1a'
subject=subprocess.check_output(['git','show','-s','--format=%s','HEAD'],text=True).strip();assert subject=='io-sprg: M0 statements (all proofs sorry)'
gate=json.loads((r/'complete-runtime-check.json').read_text());assert gate['complete'] and gate['records_all_ok'] and gate['canonical_pass'] and gate['completed']==gate['planned']==184
bind=runpy.run_path(str(root/'evidence/tools/io-sprg-rule10/environment_binding.py'));assert bind['snapshot'](root/'.lake/io-sprg-oleans',r)==gate['environment_sha256']
for v in ['coe-A','coe-B','strict-A','strict-B']:assert json.loads((r/('ctlcheck-'+v+'.json')).read_text())['all_ok']
scan=json.loads((r/'explicit-classified.json').read_text())['summary'];assert scan['foreign_items']==0
ax=json.loads((root/'evidence/axioms/m0-sp-w3/summary.json').read_text());assert not ax['root_nonstandard'] and len(ax['direct_sorry_constants'])==146
prints=json.loads((root/'evidence/axioms/m0-sp-w3/print-comparison.json').read_text());assert prints['all_match_current_graph'] and prints['printed_public_theorems']==511
subprocess.run(['python3','-I',str(root/'evidence/tools/source_inventory.py')],check=True)
subprocess.run(['python3','-I',str(root/'evidence/tools/slot_history.py'),'--require-closed'],check=True)
subprocess.run(['python3','-I',str(root/'evidence/tools/report_current.py')],check=True)
p=root/'evidence/REPORT.md';text=p.read_text();body=text[text.index('## Source and host'):]
body=body.replace('## Statement changes and judgment calls','## Statement changes').replace('## Quantifier audit and pre-M0 refinements','## Deviations from the design note').replace('## Helper plan, overlap, and reuse','## Helper plan\n\nThe following table records proof steps and their library searches.\n\n## Overlap and reuse')
body=body.replace('There is no post-M0 statement change because no freeze exists yet.','All listed statement refinements were completed before the M0 freeze; no post-M0 statement change is reported.').replace('The statements are not yet frozen. These are disclosed design choices and the','These pre-M0 refinements are now frozen. They are disclosed design choices and the')
assert (root/'evidence/build/summary.txt').read_text().startswith('HEAD '+head+'\n'),'Rebind the unchanged checked sources to the empty marker HEAD before finalizing'
counts=json.loads((r/'request-counts.json').read_text());totals=collections.Counter()
for x in counts:totals[x['variant']]+=x['requested']
strict=[x for x in gate['probes'] if x['kind']=='seal' and x['variant'].startswith('strict-') and(x.get('rc') or x.get('errors'))]
commits=subprocess.check_output(['git','log','--reverse','--format=%H%x09%s',base+'..'+head],text=True).splitlines()
commit_table='\n'.join('| `'+row.split('\t',1)[0]+'` | '+row.split('\t',1)[1]+' |' for row in commits)
header=f'''# io-sprg Phase A — checkpoint 0, M0 statements

M0 is complete and frozen at `{head}`. This is a statements checkpoint:
146 named Phase A theorem proofs remain. Readers and PrimeSchedule.nonempty are proved;
T1–T6 remain named Phase B obligations. M1–M6 are pending. No final proof-completion
claim is made. Work continues after this checkpoint without waiting for the statements gate.

## Bases, heads, and milestones

- Lean base: `{base}`; local branch `fill/io-sprg` remains on that base.
- M0 head: `{head}`.
- Records: `dbea2807532392781304e004715f3b0190025f5e`.
- Host inputs: `bc9d982b83cb35ea351e2fb373752e8688945b1c`.
- Rule 10 tool provenance: `2467bc3befdad8472b1f359337bf3a203e3651e1`.
- Gate source revision: `d286bafc4b1754e26ecae89c7f7f9c2a7cb7d7d3`.
  The empty M0 marker changes no source or imported olean; every source hash is rebound to HEAD.
- New source: 22 files, 5,911 lines. Existing edit: TCSlib.lean, one export import.

| Milestone | Status | Commit / scope |
| --- | --- | --- |
| M0 statements | Complete, frozen | `{head}`; all 22 owners and required M0 gates pass. |
| M1 algebraic correctness | Pending | No proof milestone claimed. |
| M2 stretch | Pending | Includes SP-W3 seed growth. |
| M3 Claim 4.2 | Pending | Common cutoff before every public prime. |
| M4 reductions / prop41 | Pending | Every-realiser inequalities. |
| M5 raw Theorem 4.1 | Pending | Conditional security and existence. |
| M6 links / assembly | Pending | Targets remain hypotheses. |

## Current checks

| Check | Result and evidence |
| --- | --- |
| Owned modules | 22 current-byte passes, rc0 and zero errors in both diagnostic forms; only declared sorry warnings. evidence/build/summary.txt binds every source to HEAD. |
| decls2 | 670 ADDED, zero CHANGED/REMOVED against the base; evidence/checks/m0-sp-w3/decls2.log. |
| Statements | {ax['stored_constants']} stored constants, {ax['public_types']} public full kernel-expression types; evidence/axioms/m0-sp-w3/StmtDump.jsonl. |
| Axioms | 511 public theorem prints match the full graph. Zero nonstandard axioms; 146 direct holes and {len(ax['transitive_sorry_constants'])} transitive sorry dependents. Only propext, Classical.choice, Quot.sound, and declared M0 sorryAx. |
| Rule 10 | All 88 seal probes and 96 paired-control probes have verified runtime records, exact source/log/import-environment bindings, masks, and EOF coverage; complete-runtime-check.json. Both canonical variants have zero failing declarations. |
| Controls | All 48 current unsealed probes pass; each sealed negative fails exactly once and every positive passes. All four ctlcheck variants report ALL_OK True. |
| Explicit unfolding | {scan['items']} items, all actual theorems; zero foreign definition unfoldings; explicit-classified.json. |
| Lint | Style zero findings; zero new individual campaign FAIL/WARN lines against base. sk15 has one lexical statement-length false positive with Iff.rfl proof, recorded in sk15-triage.txt. |
| Sizes / names | Every file at most 1,000 lines, every line at most 100 characters; 670 names, zero clashes/duplicates. |
| Phase A / PDFs | Only the 23 permitted paths change; permitted sampler-contract imports only in designated owners; no sampler/machine construction, local contract/realiser variant, or PDF in any delivered or committed path. |
| Cache / host | 83 direct Mathlib roots, narrowed cache refreshes only when roots were added, pinned wrapper -k3. All Lean work is root-only, serial under LEAN_SLOT_TAG=io-sprg. Team-limit deviation is disclosed below. |
| Replay / bundle / manifests | Packaging verifies every commit hash by git am --empty=keep, verifies the bundle, and checks both manifests as exact path sets. See evidence/replay.json, bundle-verify.txt and payload-source-binding.json in this payload. |

Seal request totals: {dict(totals)}. Per-owner counts are in request-counts.tsv.
Strict-only failing probes: {len(strict)}; declaration-level attribution is in
seals-strict-A.tsv and seals-strict-B.tsv. Canonical coe-A/coe-B pass with the single
FinDist coercion notation exception specified by the dispatch. Historical failed or
pre-repair checks are retained and are not counted as current passes.

## Source commits

| Commit | Subject |
| --- | --- |
{commit_table}

'''
headline=(root/'evidence/meta/m0-sp-w3/mods/evidence_probes_io_sprg_m0_HeadlineAxioms.log').read_text()
source=(root/'TCSlib/Cryptography/Obfuscation/StructuredSeed/Targets.lean').read_text()
targets=[]
for label,names in [('T1',['evalTarget']),('T2',['qGenTarget']),('T3',['coreTarget']),('T4',['lpnPreTarget','prgPreTarget','ReductionTargets']),('T5',['drawSamplerTarget']),('T6',['lpnSamplerTarget']),('Conjunction',['Targets'])]:
 blocks=[]
 for name in names:
  match=re.search(r'^(?:noncomputable )?def '+name+r'\b',source,re.M);assert match,name
  end=source.find('\n/--',match.end());assert end>=0
  blocks.append(source[match.start():end].rstrip())
 targets.append('### '+label+'\n\n```lean\n'+'\n\n'.join(blocks)+'\n```\n')
text=header+body+'\n## Phase B target statements (unproved)\n\nThese are the exact frozen definitions, with parameters in their enclosing Params namespace.\n\n'+'\n'.join(targets)+'\n## Headline axiom prints at M0\n\n```text\n'+headline+'```\n'
text+='\n## Evidence status\n\nThe current gates above supersede pending-check language in the retained read-only review\nmaterial below. Those historical notes remain attributed to their actual source snapshots;\nroot remaps line references to the frozen source and records SP-W1/SP-W2/SP-W3 separately.\nSP-W3 supersedes any historical statement that all generic definitions/conclusions stayed\nunchanged: HasPolyStretch was strengthened before freeze, as its current source inventory shows.\nAll proof-candidate packets are explicitly untested and are not source or validation.\n'
p.write_text(text);print('M0_REPORT_FINALIZED',head,'strict_failures',len(strict))
