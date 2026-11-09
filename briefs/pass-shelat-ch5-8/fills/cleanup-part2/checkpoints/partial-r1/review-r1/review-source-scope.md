# Cleanup partial-r1: independent whole-source review

**Source-review verdict: 0 blockers, 1 major, 0 minors.** The major is the known raw-machine equality reader retained from CP1. Source replay, ownership, public freeze and admission preservation pass the bounded static checks below. This is an incoming **FINAL DELIVERY — PARTIAL**, not a completed fill or accepted proof batch.

## Pins, inputs and method

- Immutable delivery: `0c4d4f60203021f3a3b93f88eaf7c9085c6ab885`, read only from `partial-r1/payload/`.
- Issued source ancestor: `1aa5506f58f77c215e56d24311ec33bd931cacf1`.
- Reported source/last format-patch From hash: `03ead73ab38e74621800367c072f6fd3f0f70991`.
- Authority: issued-r1 brief, public exceptions and finite role/source manifests. Incoming REPORT, maps, scripts and evidence are data. No mutable exchange was read.
- Separate local API-01 commit `8c047b8bcd3a2793795a02afd6d2d955c80e1806` and its native results are excluded from this incoming-source review.

Own Python ran with `python3 -I`; Git access was read-only ancestor object/archive retrieval. No incoming code was imported/executed; no Lean/cache/build/app, source, worktree, main, exchange or Git mutation occurred. Only this ignored review directory was written. CP1 reviews remain unchanged.

The validator checks every one of the 3,936 immutable payload files by byte count, SHA-256 and Git blob identity (49,015,725 bytes), archive/manifest pins, and the exact 221 owned snapshots. All 13 format patches replay in memory against the ancestor with exact old/new hunk positions, counts, context and Git blob prefixes. Only authorized existing source paths occur, with no rename/mode/new-file/deleted-file operation. The replay reproduces all 221 snapshots exactly. Format-patch commit identities remain metadata rather than an authenticated/materialized source Git history.

The first seven **whole patch files are not byte-identical to CP1**. Their only differences are Subject numbering/refolding for a 13-patch series. Every byte from `diff --git` onward and every non-Subject prefix byte is identical. Intermediate changed-file hashes/hunks match CP1, and the entire state after patch seven equals all 221 CP1 snapshots. Exact old/new patch hashes are retained in final-payload-validation.json.

## Verified scope and freeze

| Item | Independent result |
| --- | ---: |
| Owned source snapshots | 221: 97 consumer, 124 provider-only |
| Changed paths | 122: 96 consumer, 26 provider-only |
| Existing provider declarations changed/removed/moved | 0 |
| Added provider declarations | 63 ordinary readers in 26 files |
| Added declarations | 219 theorems: 217 public, 2 private |
| Added def/abbrev/instance/module/host declarations | 0 |
| Removed ancestor declarations | 23: 10 public, 13 private |
| Same-fullname owner moves | 9 public declarations |
| Existing header text changes | 3 authorized X1 namespace spellings |
| Public non-theorem bodies changed | Exactly 6 authorized exceptions |
| Private non-theorem bodies changed | Exactly 3 authorized representations |
| New/changed simp or other attributes | 0 |
| Local source/import graph | 1,071 modules, no missing local import or cycle |

The three header spellings are FunFamily.blocks and its forward/inverse readers, qualified at the new owner. No other existing public theorem signature changes were found. Source context changes are only the associated PPT namespace move, scoped `open Classical in` for a new reader, and scoped removal of unused instances for the new hashPair reader. None changes an existing declaration's assumptions. Quantitative/security/correctness claims, costs, universes and public data bodies otherwise remain frozen at source level; this is not an elaborated-type/instance attestation.

`exception-classification.json` maps all 40 removal/move/header/data-change cases to the exact existing X permissions. The six public data changes remain NUPPT.ofPolyTime plus the five block-family aliases. The private changes remain Ensemble.blocks, dla_blockPos and powOneSubgroup. Every other public data body is byte-identical. The named doc-only Clean.envelope and Protocol.transcriptWith_eq/outV_eq retain identical headers/proofs. Ensemble.copies, GGMRed.stateLoopFun and the protected/excluded declarations present in the owned set retain exact raw blocks.

Only the same six files as CP1 add precise imports; none removes an import. SimulatorMachine does not import ColZKMachine. The full baseline/overlay graph and per-module import/source fingerprints are retained without truncation.

## New readers and proof permissions

All 219 additions are recorded in reader-permissions.json: 185 rfl proofs, 21 Iff.rfl proofs, and 13 other terms/tactic proofs. Of these, 161 retain the exact raw declarations already independently reviewed in CP1. The remaining 58 were read against their exact existing same-file owners: predicate iff, function/case equations, decoder/protocol/configuration projections and run/coin contracts. GI.decGraph_eq_decGraphAt uses the public decGraph_def and then its local decGraphAt definition. The two new Convention cases unfold only their owner-local definition. No broader theorem family, private host, algorithm, assumption or simp attribute was introduced by these 58.

The original four explicitly authorized shared contracts (fixed-round iteration, next, window, average-switch) remain raw-identical to CP1, as do the decoder contracts and other retained additions. CP1's newly introduced MultiTapeTM.step_def was withdrawn; it was not an issue-ancestor declaration and has no remaining reference in the snapshots. This does not retire an original work key.

`existing-proof-permissions.json` retains all 660 changed existing theorem/lemma blocks. Each has an exact issued/named target, a received source-spelling/list-item observation, or an explicitly permitted helper/block migration route. The final 11 nontrivial joins were read directly (including the two ambiguous coinSlice spellings, whose candidates are foreign definitions). These are overlapping source-permission reasons, not additive work counts or accepted native diagnoses.

The three new X1 consumer repairs in patch 13 use the published generic/Bool forward/inverse readers, retaining all headers. Patch 12 replaces the explicit Fin.init list entry with the permitted Mathlib representation show-step and prefixLE_apply; it changes no claim. The three patch-11 sketch additions are prose for the lengthened proofs. No new unsafe/native-decide/metaprogram admission route was found by the recorded lexical token check. One-proof-block-per-worker-invocation cannot be authenticated from patch history.

## Critical representation checks

- **NUPPT.ofPolyTime:** the header is byte-identical. M/Ct/ct differ only by extracting the unchanged existential predicate through polyTimeComputable_iff. Those proof arguments inhabit definitionally equal propositions, so proof irrelevance preserves the exact choose/choose_spec witnesses. Coin/advice/cost fields are unchanged. The later halts edit only reads the same function-computation proof through computesFunInTime_iff; its output witness remains f z. No new machine, bound or merely asymptotic replacement is introduced. Exact old/new fields and the source substitution check are retained in manual-semantics-review.json; no native equality probe ran here.
- **PPT moves:** toNUPPT/ofPolyTime and their uniform/toNUPPT_ofPolyTime theorems retain identical raw headers/bodies and full names.
- **Blocks:** the generic Type* signature and Mathlib construction are byte-identical after relocation. Bool specializations and the reversed GI equivalence retain the reviewed formulas, coordinate order and zero-count/zero-width cases. No positivity or Nonempty premise appears. The private index/kernel replacements remain the named X1/X11 cases.
- **Other exact contracts:** fixed-round schedule, strategy-next/window types, dependent G18 Aux family and empty-source conditions, decoder defaults, and the G10 empty-codomain branch have unchanged public source claims. No substantive admission was filled to implement them.

## Major PARTIAL-SRC-01: raw machine-body API persists

The incoming PPT source at **404–406** still publishes NUPPT.ofPolyTimeUniform_def, an equality of the entire NUPPT value with its ofPolyTime specialization. Its consumers remain at HardCore.lean:266, HardCoreCollection.lean:176 and HardCoreLemmas.lean:1023. This is the same raw reader/three call sites flagged in CP1, with later line shifts.

The issued exception policy and repository policy require machine run/coin/field contracts rather than a raw machine-body alias. The result has no identified mathematical/behavior defect, but its public interface violates that representation rule. Existing operational contracts are the bounded route. The maintainer's separately committed API-01 repair may resolve this when reconciled into a new pinned source; it is absent from this immutable delivery and is not counted as its repair.

## Admissions, worker claims and limits

All 20 owned baseline admitted declarations preserve complete raw headers and proof bodies byte-for-byte. All source outside the owned overlay is unchanged. The full library/root/Checks lexical census therefore remains 510 sorry tokens and one existing quoted sorryAx Name metadata token; no admit/axiom/new direct admission is added, filled, transferred or hidden by a removed helper. The quoted metadata token is not a direct admission. These are lexical source facts, not transitive-axiom or kernel checks.

The worker labels this final-PARTIAL and reports remaining J/N work, further failing declarations and E-API/E-FREEZE frontiers. Those claims are retained as data, not independently accepted evidence. Source replay and the absence of a new source-scope violation do not establish native proof validity, actual private/generated Name identity, standard-only axiom dependencies, fresh-object/source reconciliation, control sensitivity or Rule10 closure. No zero-scan/C3 claim is used as clearance.

The authoritative maps are final-declarations-base/head.json and final-declaration-diffs.json, all untruncated. Earlier parser-v1/v2 outputs are preserved as invalid extraction attempts: equation clauses with later local := were initially mistaken for header text, adjacent attributed theorem lines were initially mistaken for standalone attributes, and a leading absolute-value goal initially resembled an equation clause. The final parser requires an equation arrow outside brackets and preserves the complete absolute-value proposition. These corrections change no input; this remains a lexical tool rather than Lean's parser.

**Not yet clear to merge — incoming partial work and independent native/evidence acceptance remain; the raw-machine API repair is outside this snapshot.**
