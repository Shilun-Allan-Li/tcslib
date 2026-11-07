# MIG-1 landing: Composition, Wrappers and Loop audit repairs

**Not yet clear to merge.** The owned repairs and this bounded evidence are complete; this does not replace the combined landing validation, external gate or merged-tree replay that the maintainer runs.

## Stable sources and actual elaborations

| Source in `scratch/wt-epad` | SHA256 | Successful actual-module receipt |
| --- | --- | --- |
| `TCSlib/Complexity/TuringMachine/Composition.lean` | `72db4da9cff279bfae399dd3b79e2e5f56eb19bf010125f9b4a834f7c55b4b20` | `composition-branch-consumer-1.json` |
| `TCSlib/Complexity/TuringMachine/Build/Wrappers.lean` | `3846089b096822f7e9233da0afb648b7f2bc0097dcd63245bdf75657d4f88bb9` | `wrappers-space-consumer-2.json` |
| `TCSlib/Complexity/TuringMachine/Build/Loop.lean` | `956fe914732375be3aa2121922a8918d1f049f9b7c7f767c3bc2b409bcc7a736` | `loop-final-module-1.json` |

Each receipt records the actual wrapper command, input/log hashes, exit, error count and unchanged-input check. `compiled-inputs-final.json` pins the six freshly compiled dependency/module oleans in this review's **private complete overlay** `scratch/oleans-mig1-comp-loop-20261107`, cloned from the complete `oleans-reading-preflight2` tree. Simulation, Encoding and ClassP/TimeConstructible were freshly elaborated before the three owned modules. This is a partial dependency-chain check, not a claim to the whole MIG-1 sweep. Lean was invoked only through the managed wrappers; no shared snapshot was modified.

Composition and Wrappers have no warnings in their successful module logs. Loop has 61 warnings, each located in a byte-unchanged legacy declaration; `source_review.py` verifies that none is in the twenty affected proof regions. No linter option was disabled.

## Resulting repairs

* Composition uses a private consumer-specific `condTM_branch_run`: the **actual fixed-false controller table** agrees with the explicitly transported branch view, and the approved `branchTM_runFrom_independent` contract supplies the chosen verdict. Its public consumer keeps the exact statement.
* Wrappers uses explicit branch views and approved field equations throughout the new time/head/space proofs. Unchanged `timed_start` and `timed_branch_run` remain opaque same-home dependencies; their results are normalized on both sides using the public shape equations. The actual timed fixed-false table was independently checked in `TimedFixedFalse-v1`; it is not an assumed premise.
* Loop's changed preparation/head/output proofs consume the public configuration readers. The omitted `loopHost_input_rewind` is included in source/seal coverage. T3's twelve repeated frame-side proofs now use two private selector-disjointness lemmas. Both complete bank proofs use `embedEmitCfg_unselected`, its selected-field counterparts and the published `Cfg.mapState` fields, avoiding an implicit reduction of `runFrom` at zero.

No admission was filled in this maintainer repair, and no new public API was added. The generic cross-file first-entry twins are outside this change: `emCall_first_entry` is byte-preserved. Primitives is owned and validated separately.

## Source freeze and private headers

`source-review.json` compares the three initial source archives with the final blobs: all 56 public declaration headers, their visibility/order, all imports/attributes and all **82 existing executable declarations** are preserved byte for byte. The three added declarations are private proof helpers: `condTM_branch_run`, `emCall_pair_not_mem` and `emCall_triple_not_mem`.

Exactly two existing **private headers were re-expressed**, `timedReady_dispatch` and `timed_ledger`. Their full old/new headers and unchanged mathematical content are in `private-header-transports.md`. The approved `branchTM_k`/`branchTM_State` equations explicitly transport the machine to the fixed sum carrier. Do not label all private headers byte-identical. The source parser's header boundary handles nested `input := x` and the new top-level let-view; its checks are retained in `source_review.py`.

The same report hashes the unchanged `condTM_start`, five timed legacy helpers and the pending first-entry lemma. These opaque same-home legacy proofs are **not** claimed to have a global rule-10 seal.

## Strong source-region checks

| Source scope | Effective operational definitions | Passing primary probe |
| --- | --- | --- |
| All ten changed/new Composition proof declarations | 23 | `composition-new-seal-v1` |
| Whole new timed Wrappers suffix, headers included (nine theorems and one private layout definition) | 22 | `wrappers-new-seal-v3` |
| All twenty changed/new Loop proof declarations, including rewind and both T3 bank proofs | 30 | `loop-new-seal-v11` |

Each guarded source is an exact full-source copy with only section/attribute instrumentation; all three actual default TCSlib `simp` definitions (`Action.apply`, `Cfg.init`, `MultiTapeTM.initCfg`) are removed in the guarded regions. Complete ranges/hashes are retained for Composition and Loop. The two final rewind source probes additionally mark the generated matcher irreducible; that **ineffective attribute is not counted** in the table above.

`control-definitions.txt` lists the thirty effectively sealed definitions. Every definition has a point equation (projecting a data field where appropriate) and a whole defining-function equation. All sixty positive goals pass with kernel-checked proof declarations; all sixty sealed goals fail, each with its own matching diagnostic. `control-check.json` verifies exact identities/multiplicities and rejects four deliberately corrupted evidence variants. Negative-control exit 1 is expected.

`foreign-inventory.json` accounts for all direct compiled foreign definitions: 24 with regular value hints are covered by the appropriate owner-specific seal, 14 true reducible projection/`Halted` exclusions have actual default-validation refusal diagnostics, and one generated matcher is reported separately. `matcher-review.md` gives the precise boundary: six constructor-specialized controls pass both ways, while two variable/whole-head controls fail already unsealed. The accepted matcher attribute is non-discriminating. It appears only in the values of `loopHost_input_rewind` and `timed_ledger`, through the literal pattern in the published rewind premise; no covered root type or descendant directly mentions it. No landing source names/unfolds the generated constant. This scoped limitation remains visible for external review; no general exemption or new reader requirement is asserted.

`command-arguments.md` retains the inspected lexical inventory of 244 rewrite/simplification/unfold/show/change occurrences. No imported operational definition is passed directly to the rewriter/simplifier. Core Fin index equalities are built by `show ... from rfl` and then supplied as equality proofs to `rw`; published Fin case equations perform the ensuing rewrite. The lexical scanner is an aide; source reading and actual guarded elaboration govern the claim.

## Compiled inventory and source population

`metadata-current.out` and its reviewed probe retain an **unfiltered census** of all 809 compiled constants in the three modules, including 684 private and 747 internal names. `metadata-roots.json` identifies forty covered roots, including the private layout definition; all fifty-six compiled descendants are included in the axiom and direct-definition inventory. All 96 recursive axiom walks use subsets of `{propext, Classical.choice, Quot.sound}`: 62 use all three, 30 use `{propext, Quot.sound}`, and four use `propext` alone. No `sorryAx` or nonstandard axiom is present in those walks. All forty roots are non-simp. This is not an axiom claim about every unrelated legacy declaration.

`census-current.json`, `axioms-current.json`, `metadata-summary.json`, and `foreign-inventory.json` are mechanically checked against the raw log by `analyze_evidence.py`. All directly reached regular foreign definitions are controlled in their consumer's own source scope. The complete imported default-simp definition inventory is also recorded rather than guessed.

The direct foreign source homes are **Build/Convention, Build/Embed, Build/Wrappers, Configuration, Deterministic, Finite, Simulation and StateRenaming** (under `TCSlib/Complexity/TuringMachine/`). Together with the three owned source files this is ten unique files. Root must union these with the other landing owners' actual cited homes; this review does not assert that an inherited sixteen-file list is complete. In particular, StateRenaming is needed for T3. The optional closed-rewind comparison in `matcher-review.md` additionally cites Build/InputRewind; include it if that discussion is carried into the gate pack. No issued MIG-1 packet/input was altered here.

## Evidence integrity and limits

All probe sources, raw outputs and failed intermediate attempts remain in this folder as `.lean.txt`, `.out` and `.json`. `receipt-index.json` indexes 61 actual Lean invocations and recounts diagnostics from their raw logs. One historical receipt, `composition-cond-seal-v1`, recorded two errors before the runner learned to count Lean's tagged diagnostics; its raw log has three. That original receipt is retained, and the discrepancy is explicit in the index. The failed attempt is not used as passing evidence. The instrumentation typo involving the unavailable private `embedSlot` spelling is likewise retained and corrected in later probes. The first manifest-only path assumption failure is retained separately.

`SHA256SUMS` covers this folder's finalized artifacts except itself and the later read-only Primitives plan (if added). The source freezes and module/probe receipts are the primary evidence. This child performed no Git mutation, commit, push, screen, cache operation, shared-snapshot edit or Primitives edit. Root retains ownership of integration, final combined validation, packet publication and gate disposition.
