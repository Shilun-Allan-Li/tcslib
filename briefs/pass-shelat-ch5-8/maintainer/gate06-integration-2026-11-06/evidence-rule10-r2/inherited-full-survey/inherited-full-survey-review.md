# Gate06 full-survey inherited-source review

**Internal static review; not a seal pass or merge clearance.** Exact comparison base `c7d8753a548ced71c1e1ea70e012c365af5c2171`; frozen head `e9d64158461bfe24ddc88ab885bc4017899b4c16`. Source came only from `git show` at those revisions, so later worktree changes cannot affect this classification.

The completed 51-module survey has **17 passing modules, 34 failing modules, 195 source diagnostics**. Independent parsing of every selected completed log reproduces all 195 diagnostics.

## Result and scope

- Link the previously verified **15 declarations / 16 diagnostics** under `/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/evidence-rule10-r2/inherited-observations`; they were not re-reviewed here.
- This review confirms **80 further declarations / 104 diagnostics** have byte-identical complete raw headers and bodies. All full binding/attribute prefixes match, every diagnostic is inside its extracted range, and every source/probe line copy was checked against exact Git head bytes.
- Of these 80, **55 module/name keys already occur in the historical cleanup ledger; 25 are newly observed inherited keys**.
- Combined reconciliation input: **95 declarations / 120 diagnostics**, of which **60 keys have exact historical links and 35 are newly observed**.
- **47 declarations / 68 diagnostics are in files absent from the actual base**, and **7 existing declarations / 7 diagnostics have changed code**. Those **54 declarations / 75 diagnostics remain non-exempt**. Code copied from another branch or a mechanical rename does not make them source-untouched at this base.
- Preliminary 76 touched / 119 untouched diagnostic flags therefore contain one doc-range false positive, `gi_statZK`. The recommended source-code split is 75 new/changed versus 120 inherited observations; root must record that correction explicitly. All 195 remain failing observations.

## Context checks and the gi_statZK false flag

`GraphIsomorphismZK.gi_statZK`, base/head **561–580**, is raw-identical. Its preceding docstring **535–560** changes only one sketch identifier, `coinSlice`→`coinBlock`; the formal security claim, error formula and statistical/strict-PPT deviation wording are unchanged. Imports, namespace/section/variable/open/options and attribute prefixes are identical.

The operative security declarations are also raw-identical: `StatZK` (Defs **180–182**, SHA-256 `47da7ddfed8ecec00ec3d1dc1f1e7a7d4aedc970b7868bfae2a73727140862fa`), `Riso`, `giProtocol`, `giProver` and `giVerifier`. The observed log error is `introN` at **source564/probe614**, log line **1112**, on the sealed `StatZK giProtocol Riso δ` goal before any simulator helper is used.

The relevant helper context is **not silently called literally unchanged**: `giSim` changes the tape-helper name. Its old body becomes the new body by exactly `coinSlice`→`coinBlock`; the old global `coinSlice` and new global `coinBlock` have byte-identical drop/take bodies after definition/binder name alpha-renaming. These certificates and all context hashes are in JSON. This supports a proof-code-untouched classification and explains the doc-only flag; it does not waive the actual forbidden read or prove a new native result.

Four GI proof-module closures (Efficiency, EfficiencyRep, EfficiencyRepGI, Proofs) add Adversary for the shared `coinBlock`; only Proofs adds a direct import. No candidate binding/attribute prefix changes. This is disclosed as changed import context, not a claim of identical full native environments.

Extractors also needed context review because `FinDist.probTrue` moved owners. Its three observed failures concern different, unchanged foreign operations: two `statDist` body reads and one `hashPair` conversion. `StatisticalDistance.lean` and `LeftoverHash.lean` are byte-identical files at the base/head; their operative definition-block hashes are `2cf3e00b032c7667f719f42921f9c8d8fe040c041fafa5868e418c357ffa9cad` and `10f9e47cfba3fa8a425d6b740f1cc2686d4c5d9b686f40662e3e695e8d622445`. No new ownership-boundary failure is inferred from the `probTrue` deletion.

## Confirmed source-identity groups

| Module below TCSlib | Declarations | Diagnostics | Exact historical keys | Newly observed keys |
|---|---:|---:|---:|---:|
| Cryptography/ZeroKnowledge/Defs.lean | 7 | 12 | 7 | 0 |
| Cryptography/ZeroKnowledge/GraphIsomorphism.lean | 16 | 17 | 16 | 0 |
| Cryptography/ZeroKnowledge/GraphIsomorphism/Efficiency.lean | 8 | 15 | 0 | 8 |
| Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRep.lean | 7 | 7 | 0 | 7 |
| Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRepGI.lean | 2 | 3 | 0 | 2 |
| Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean | 4 | 4 | 4 | 0 |
| Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRep.lean | 5 | 8 | 5 | 0 |
| Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean | 11 | 15 | 11 | 0 |
| Cryptography/ZeroKnowledge/GraphIsomorphismZK.lean | 5 | 6 | 0 | 5 |
| Cryptography/ZeroKnowledge/GraphIsomorphismZK/Closeness.lean | 8 | 10 | 8 | 0 |
| Cryptography/ZeroKnowledge/GraphIsomorphismZK/Simulator.lean | 4 | 4 | 4 | 0 |
| InformationTheory/Extractors.lean | 3 | 3 | 0 | 3 |

Exact base/head source ranges, complete raw/code SHA-256 values, canonical module/name, diagnostic source/probe positions, completed-log path/line/hash and historical TSV row numbers are recorded per declaration in the JSON and TSV. Historical links use exact file/name keys; names in a different module are not equated.

## Genuinely changed existing declarations: retain all seven failures

| Source file below TCSlib | Declaration | Base/head range | Why not inherited |
|---|---|---|---|
| Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRep.lean | `gniVerifierRep_efficient` | 595–617 / 595–617 | header and/or proof uses changed coinBlock/reader names |
| Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRepGI.lean | `giProverRep_efficient` | 109–128 / 109–128 | header and/or proof uses changed coinBlock/reader names |
| Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRep.lean | `gniVerifierRep_next_lt` | 146–166 / 146–166 | header and/or proof uses changed coinBlock/reader names |
| Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRep.lean | `gniVerifierRep_next_ge` | 169–174 / 169–174 | header and/or proof uses changed coinBlock/reader names |
| Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean | `giProverRep_next_even` | 210–223 / 210–223 | header and/or proof uses changed coinBlock/reader names |
| Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean | `giProverRep_next_odd` | 227–243 / 227–243 | header and/or proof uses changed coinBlock/reader names |
| Cryptography/ZeroKnowledge/GraphIsomorphismZK/Simulator.lean | `attemptAt_poly` | 254–388 / 254–388 | header and/or proof uses changed coinBlock/reader names |

The other 47 non-exempt declarations belong to actual-base-new files; all are listed in TSV/JSON with `NEW_FILE`, rather than receiving an inherited label.

## Ambiguity and root judgment

No unresolved declaration-boundary, missing-base-match or header/body identity ambiguity remains. The one touched-flag correction requiring transparent root reconciliation is `gi_statZK`; the changed helper/import context is exposed above. The recommendation is source-code-untouched inherited observation, with **zero waiver** of its real failing read.

No fresh base seal was run. A source-identical observation does not establish how the complete old environment would behave under the current combined seal, and no failing module or proof is marked passing here. Root must reconcile all historical/new observation keys and continue the authorized repair/verification workflow.

## Reproduction and evidence limits

`inherited-full-survey-reproduce.py` is this reviewer’s own read-only source comparator, not a delivered worker program. Run with `python3 -I ... --output <scratch-json>` to reproduce the core ranges/raw/code hashes, provisional classifications and exact historical key matches. The final context certificates in JSON additionally record archived probe-line, full binding/attribute, import-closure and operative-definition checks described above. The parser is a source-command parser, not Lean AST; manual/specific context checks supplement it.

No received program, Lean/cache command, app, Git mutation or library edit was executed. Historical cleanup TSVs and main records were read only. Only ignored review artifacts were saved.

**Not yet clear to merge — 75 new/changed diagnostics still require verified repairs; inherited observations require reconciliation and are not passes.**
