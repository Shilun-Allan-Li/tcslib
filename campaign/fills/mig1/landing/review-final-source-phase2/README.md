# Phase 2 source freeze

**Not yet clear to merge.** The frozen twelve-file phase 2 source satisfies the approved source
contracts. This source-only review runs no Lean, screen, Git, cache or snapshot operation and grants
no API, debt or merge approval. The separate tagged-driver scope question is recorded in
`tagged-family-disposition.md` once its bounded inspection completes; it must not be described as
whole-family retirement while `fwdMapVirtual_run` retains its existential-tag induction.

## Inputs, scope and source census

`capture.json` preserves full inert snapshots at four stages: API
`1160c18f03fd318f0dec25738790935fa61379d4`, producer
`af3273f75d7602c079169f321e4536a58c7bb034`, passed pre-adoption source
`0d6b6f842a48be813dcde7fdfd2a1a161fab2383`, and the actual uncommitted phase 2 source. The original
API/producer object verification is attributed to the previous maintainer-owned capture receipts.
Six pre-adoption blobs match both the adoption receipt and prior final-actual source captures; the
other six blobs are unchanged and match those same prior captures.

The parent's fresh `phase2-adoption/scope.json` reports exactly twelve changed Lean paths from API,
exactly six dirty paths from the passed source, a clean index and no untracked Lean files. Its full
hashes and all twelve actual SHA256s were independently reconciled with this capture. No Git was
invoked here. The scope is the original eleven files plus VirtualInput's existing-API body repoint
under WORKFLOW §3. WordSize's phase 2 change is documentation only.

| Authored source declarations, all twelve files | API | Producer | Passed pre-adoption | Phase 2 |
| --- | ---: | ---: | ---: | ---: |
| Public | 384 | 381 | 381 | 381 |
| Private | 1,080 | 752 | 764 | 766 |

The earlier eleven-file census was public 364→361. The added comparison home VirtualInput contributes
its twenty existing public declarations; it adds no new public API. Relative to API, the exact public
surface remains **three forwarding exports added and six Catalog exports retired**. Relative to the
passed source there are no public additions/removals. All surviving public names, homes, visibility,
full literal headers, declaration kinds and relative order agree. Full standalone attribute commands
including their continuation lines, and all declaration annotations, are unchanged. The only API
import differences remain the two previously approved Simulation/Mathlib-Fin and Catalog/Primitives
edges; phase 2 changes no import.

## Private and executable accounting by phase

`api-to-current.json`, `producer-to-current.json`, and `prior0d-to-current.json` separate the phases.
The full balanced-header parser and four adversarial controls retain statement-local `let` values,
proof-valued lets, inner assignments and named binder assignments.

- API→phase 2 has the three existing producer private strengthenings: `Complexity.counter_count`,
  `Turing.FinTM.loopHost_contracts`, and `loopHost_prepare`.
- Producer→phase 2 has only the two existing Wrappers private transport re-expressions:
  `timedReady_dispatch` and `timed_ledger`.
- Passed source→phase 2 changes **no surviving private header**. It adds four private proof helpers:
  `Turing.catalog_ofWords_with_tapes`, `Turing.FinTM.loop_computes_of_startup`, `emCall_bank_embed`,
  and `fwdMap_back`. It intentionally removes the two unused private helpers `emCall_pair_not_mem`
  and `emCall_triple_not_mem`; a fresh identifier scan finds no remaining code caller anywhere in
  TCSlib. These are private removals, not public API retirements.

All nine original moved private type/data/instance declarations were compared again with their
actual API Catalog originals modulo the approved renames, including `f2_condHeads→timedHeads` and
the poly/forwarding families. The gated `pairMapSndTM` wrapper body and both theorem headers remain
exact modulo source formatting in the supplied frozen contracts. The visible time coefficient 22
and payload-space coefficient one are unchanged.

All surviving executable/type/data bodies are unchanged in phase 2. Across the entire API→phase 2
comparison, the only retained body exceptions are the two authorized **private final `inj'` proof
fields** in the existing emitter embeddings. Their complete headers, `toFun` fields and all data
prefix bytes remain identical after masking exactly that final Prop proof field. The earlier
CertShell proof-local initializer spelling is unchanged from the passed source; its recorded
extensional diagnostics remain attributed to its owner and are not rerun here.

All seventeen target admissions remain discharged. The original three RAM admissions, their headers
and complete proof bodies remain literal; no other static admission occurs in these twelve files.

## Complete proof roots and citation population

The exact current inventory is **144 new/changed proof roots: 66 public, 78 private**. It comprises
89 changed existing bodies and 55 new/moved proof declarations relative to API. Relative to the
passed source, eleven existing proof bodies change and four private proof helpers are added;
the two pruned selectors disappear. WordSize changes no code or proof. `QA.json` distinguishes
proof changes and doc/layout-only changes in all six phase 2 files.

`proof-roots.json` and `.tsv` contain full source names, owners, private flags and current source
lines for the parent's native inventory. Compared with the earlier 140-root list, the six additions
are the four helpers plus `bufferedSecondCfg_run` and `vhostEmitTM_runFrom`; the two pruned selectors
are removed. Every changed proof body exceeding twenty lines has a leading proof sketch.

`source-citations.json` records 2,389 resolved lexical proof/header/documentation entries, public
abbreviation implementation expansion, ambiguous tokens and unresolved lexical candidates. This
source pass is supplemented conservatively by prior compiled owner hints and the full existing
25-file population. The resulting TCSlib home union remains **25 files, with no added home**.
`screen-population-final-review.txt` is the complete proposed file list; no screen was run here.
The tagged invariant route additionally cites existing Mathlib `Set.MapsTo.iterate`
(`Data/Set/Function.lean:152`) and `add_right_iterate` (the additive companion at
`Algebra/Group/Basic.lean:184`), whose availability was established by the earlier isolated route
probe. This is not a new native inventory claim.

The two existing on-demand compiler equation materializations, `solveSplit.eq_def` and
`solveSplitWith.eq_def`, remain separately disclosed in the earlier source/compiled accounting.
An authored source public delta of zero in phase 2 is not a whole-module compiled census result.
The parent owns the fresh native 144-root descendant/citation/axiom inventory, actual current3 chain
and subsequent merged-tree replay. The passed 394-module replay was for the pre-adoption source;
this review does not transfer that result to the new tree.

## Verification limits

All twelve actual source hashes were checked stable at capture and again in final QA. The exact
six public retirements were searched across all current TCSlib and the maintained-document
population; results are retained in `retirement-enumeration.json`, with historical documentation
separated from code. Source-only preparation errors and their corrections are preserved in
`preparation-errata.json`; they changed no Lean source or proof.

No actual source, repository state, compiled artifact, cache or shared snapshot was changed here.
No gate was closed, fill performed, dispatch sent, commit/push made or merge clearance granted.
