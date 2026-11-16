#!/usr/bin/env python3
"""Assemble the fourth whole-declaration checkpoint report from verified evidence."""
import json
from pathlib import Path
import subprocess

ref = subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip()
sweep = json.loads(Path('evidence/checkpoint4-sweep-summary.json').read_text())
audit = json.loads(Path('evidence/checkpoint4-security-audit-summary.json').read_text())
scope = json.loads(Path('evidence/logs/checkpoint4-exact-static/source-scope.json').read_text())
assert sweep['modules'] == 261 and sweep['current_sorry_declarations'] == 31
assert scope['helper_children'] == 67 and scope['files'] == 71
parts = [f'''# sc-yao · checkpoint 4

Issue base: `6ce4658db08a1dc2a03a149987197660db078011`.
Issued exchange pin: `f41e1b4ddaff2a140c893d510bdd8d227f83fed8`.
Local proof tip: `{ref}`. The branch `fill/sc-yao` remains local.
Only `inbox/fills/sc-yao/` is delivered, from the dedicated delivery worktree.

## Status and scope

`yaoHybrid_polyTime` is proved with its frozen signature, standard axioms only and no
admitted dependency. `yaoHybrid_simulators` still retains its base body and sketch in
the exported Yao file. The full objective continues; this is checkpoint4, not a partial final.

All generic security contracts are now complete, including both exact sampler endpoints,
the full-tape selected-coordinate law, polynomial-time all-occurrence reconstruction,
uniform B1 reduction and the polynomial gate chain. The separate complete concrete
simulator prototype also passes normal and owner-context A seals. Its body has not yet
been installed in the frozen target; that installation and the final full-source audits
remain. Every exported helper is a whole declaration without an admission.

This checkpoint has67 helper children, their single HybridProof facade and the three
approved frozen files:71 changed/new source files. Yao has1062 lines,1090 after sc-garble's
28-line growth, below the SY-2 cap1200. All other files have<1000 lines; width≤100.
Only the two authorized bodies/sketches, main-results bullet and hub import may change
in Yao. The source/header checker reports zero unexpected differences and both one-error
controls pass; its Yao count is72 public plus4 private declarations.

No unmerged proof declaration is consumed. One scope correction is included: CP3's
BobViewShape unnecessarily imported in-flight ObliviousTransfer. This import is removed;
all required functionality/readers already come from TwoMoveViews→Hybrid→Defs. Its proof
and statement are unchanged. Four ordinary merged checks and all four exact-source
BobViewShape seals pass after removal. The earlier source is retained and the correction
is recorded in evidence/logs/checkpoint4-import-correction.json.

## Contributions

| Agent | Cumulative contributions |
|---|---|
| Lead /root | CoinRead, BobIO, BobInit, ProtocolEfficiency, CallEquations, Strategies, SliceReduction, SimulationBound, OTAnswerWords, AliceStatistical, SelectedLaw; generalized CoordinateSwap's finiteness interface; corrected BobViewShape's import; frozen readers and efficiency body; integration, checks, commits and delivery. |
| /root/decoder, sc-yao-a | ChunkScanner, DescriptionDecoder, CoinGarbling, Garbling, WordLists, RowFromCoins, TablesFromCoins, AllTables, GarblingProgram, AliceProgram, FakeObjects, FakeProgram, FakeMessage, FakeSimulator, CoordinateSwap, BobViewShape, FakeSimulatorFactory, BobStageZero, GateHybridChain, GateHybridSecurity; complete concrete simulator prototype. |
| /root/evaluation, sc-yao-b | RunWithHost, Decryption, FirstTagged, EvalGate, GarbledRun, BobTables, BobProgram, BobSimulator, GateOccurrences; NonceCoordinates, SeedCoordinates, SliceReconstruction, SelectedSlices, SelectedSeed, SelectedRows, SelectedPlan, SelectedTables, SelectedAdviceBounds, SelectedStep, SelectedStepChoices, SelectedStepSecurity. |
| /root/lengths, sc-yao-c | Lengths, OTInputs, TwoMoveViews, StatisticalSwitch, AliceSimulator, CoinRelabel, RelabelGarbling, CoinSeedRelabel, GateHybrids, GateHybridMessage, SamplerEndpoints, TapeValues, SelectedFields, GateStepCases, BobStatistical; shorter concrete assembly skeleton. |

Only the lead edits frozen files, commits and delivers. Children have separate worktrees,
separate TCSlib artifact trees and read-only package symlinks. All child evidence is under
evidence/subagents/. Ownership transfers and immutable handoff hashes are retained.

## Interface and concrete premise discharges (SY-1)

Helpers are generic in the actual circuit, seed, output selectors, strategy equations and
functionality; they cannot see or name Yao's definitions. Hybrid semantics are defined once
in GateHybrids/GateHybridMessage and consumed through readers. No seed/message/protocol
semantic copy is introduced. Source headers and complete elaborated signatures (including
implicit section parameters, private and generated constants) are exported in evidence.

The efficiency body uses AliceProgram.message_poly, BobProgram.output_poly, CallEquations
and the answer-independent message bound through ProtocolEfficiency. Uniformity supplies
the actual circuit description; canonical seed readers supply all key/nonce/shift blocks.
Strategies are efficient on arbitrary private words, tapes and malformed histories.

The following describes the checked prototype, not an exported proof of the frozen target.
''', Path('evidence/subagents/a13/REPORT-fragment.md').read_text(),
Path('evidence/subagents/b-final/REPORT-fragment.md').read_text().split(
    '## Overlap and reuse — b5/v6/v7')[0],
Path('evidence/reports/common-contract-disclosures.md').read_text(),
'''## Scope requests and readers

SY-1–SY-6 govern. The only circuit insertions are isFaninTwo_iff, byte-identical to
sc-garble, plus encodeList_nil/cons, GateKind.encode_and/or/not, DAGGate.encode_eq and
DAGCircuit.encode_parts. Removing them restores base bytes. All24 reader controls are
retained:8 unsealed passes,8 sealed negatives each exactly1 error,8 sealed reader passes.
Both diagnostic forms are counted.

Four extra imports were explicitly approved, with verbatim requests/answers under
evidence/scope-request/: ThreeColoring.Machines, FromPRF.ReductionMachine,
FromPRF.HybridLemmas, Asymptotic.BlockEncryptor. The last is now actually used by
SelectedSlices via the public encodeList_eq_flatMap; no unapproved Mathlib root is introduced.
The full issued-plus-approved upstream order has193 modules, extended by68 helpers/facade.
The user authorized full edits, scoped commits/pushes and shared-wrapper checks despite
the supplied AGENTS prohibition: “Yes, follow the full objective and wrapper rules”.
Approvals persist across relocation. No other frozen-file change or scope is assumed.

## Validation and evidence

Every Lean/Lake/tree check uses /private/tmp/sc-yao-lean-slot.sh, with at most THREE Lean
processes host-wide, shared with all other jobs; tags sc-yao/a/b/c. Python is python3 -I.
No lake build or unfiltered cache fetch was used. Wrapper SHA256:
ff64d8d5b6baf4e7b1c15172a7faeb70246f22c6acf76134bbdb70c017f41f1a.
Initial packs/pins/narrow cache and package checks remain delivered. Latest resumed
preflight headroom6.368GiB, later6.180GiB, both above4GiB; disk free>130GiB.
Shared-slot histories and all interrupted/failed development versions are retained.

The full261-module checkpoint sweep passes with0 errors and fresh artifacts. Every raw
source snapshot hash matches the committed source. Comparing declaration names with the
32 base admissions yields31, exactly removal of yaoHybrid_polyTime and no addition.
See checkpoint4-sweep-summary.json and logs/checkpoint4-sweep/results.jsonl.

The merged all-stored probe prints1488 constants including1110 helper constants. Every
helper has empty transitive sorry closure and only propext/Classical.choice/Quot.sound.
The efficiency target has those standard axioms and empty closure. The simulator target
and yaoHybrid_hbcSecure still reach the target's base admission; yaoProtocol_hbcSecure
additionally reaches the two OT target admissions and hbcSecure_compose. The probe used
the pre-import-correction artifacts; no declaration body changed in that correction.
The corrected source is independently rechecked/sealed and the final audit will be rerun.
Earlier c probes covered40 explicit source roots; later c probes dynamically enumerate
278 stored constants. The lead's complete1488-constant merged audit independently closes
the earlier coverage gap; the early source-root probes are not described as exhaustive.

Every new helper has exact-version A/B strict/coe evidence from its owner. The lead has
additionally rechecked all helpers in the full sweep; its complete facade4/4, strengthened
CoordinateSwap/SelectedLaw8/8 and corrected BobViewShape4/4 full-file variants pass.
All seals cover full imported TCSlib definition/matcher closures, use -DmaxErrors=0 and
count error: and error(...). Coercion notation variants are canonical. No failed check
is hidden by a cutoff. The prepared complete-helper seal manifests are for the next final
lead verification; their generated sources alone are not claimed to be executed runs.

Frozen-file baseline diagnostics remain: DAGCircuit0 in all variants; Uniform4 inherited
errors in two old declarations; Yao A strict/coe0, B strict/coe17=15 base plus2 efficiency
call-input polynomial-evaluation mismatches. Each is attributed in the retained baseline
and efficiency seal summaries. The a12 prototype has a separate individually attributed
B9, not a four-seal pass; its owner-context exemption is documented above.

Name scan:764 new explicit namespace-resolved public/private names,0 unexpected clashes
across issue base, sc-garble a73072f1, sc-ot f62a25b3 and sc-compose bdfdcb76. The sole
intentional coincidence is the byte-identical SY-3 reader. Explicit definition review:
8970 files,1909 tactic references,17 candidates:15 local binders and2 same-file published
SelectedRows.length_eq theorem references,0 foreign-definition violations. Full source
contexts/hashes are retained. Initial parser assertions and their fixes are preserved.

Exact lint line-set comparison: Cryptography92 FAIL/102 WARN versus base92/101; the only
new WARN is the approved Yao size. Circuits0 FAIL/79 WARN, with missing-reader warnings
improved11→10 and2→1. No new FAIL or undisclosed WARN. The old Yao target-size INFO
disappears when it becomes a facade. Source scope, width, line bounds, complete facade
imports and no-helper-admission scans pass.

SelectedLaw development evidence is preserved: the320-second candidate reported five
missing finite-instance diagnostics (4.7GB peak), with no resource shortage and no signal
sent to that already-finished run. Later source-directed SIGINTs were diagnostic stops
of owned groups, not resource failures. A tool approval timeout created no process; the
single retry succeeded. The genuine prototype foreign-distAdv reduction issue was fixed
through its published reader. No other job was killed and no137/139/low-headroom E-RES
occurred. The c shortened skeleton's width is100 (earlier prose said93); the final a12
complete prototype is124 body lines, width93. Exact metrics take precedence over old prose.

## Delivery and remaining work

The complete unsigned six-patch series from the issue base includes COMMITS.tsv with all
author/committer identities/dates and signing=none. All six hashes are reproduced with
git am in a fresh shared scratch clone before pushing. Top-level and evidence manifests
are checked for exact path-set equality, no leading ./ and SHA256 byte equality.

Every retained raw source/log/results file, probe, seal/control, request, tool and child
handoff is delivered. Large raw samples are losslessly in numbered ZIPs with entry hashes;
the relocation ZIP preserves all four trees. Evidence-only unfinished ladder versions
are historical probes and are not exported library source.

The157MB SelectedLaw diagnostic stack is losslessly retained in raw-samples-03.zip, with
verified decompression hash and entry inventory. An initial unpublished local delivery
commit included the raw file; its controller was stopped after pull/rebase and before
any push. That commit is preserved on a local backup ref and replaced by the corrected
package commit. No push was refused and no force-push occurred. The exporter and delivery
tools now reject oversized individual files before submission.

Prior pushed checkpoints: f0a9a6163c5c91599147eb550fd5bb929cc68aa0,
816971fc6922646f056a47efd41b1407f762320d, acc868271367d525350da2c1043e7f470f1c0a98.
This checkpoint is rebased and pushed only under inbox/fills/sc-yao, without force.
Remaining: install the complete concrete simulator body/sketch/main-results bullet,
run final exact-source normal/all-stored/seal/static/full-sweep audits, commit and deliver
the final payload and sc-yao-rooted ZIP. No final completion or PR merge is claimed.
''']
Path('evidence/reports/checkpoint4.md').write_text('\n\n'.join(parts))
print('checkpoint4 report written', ref)
