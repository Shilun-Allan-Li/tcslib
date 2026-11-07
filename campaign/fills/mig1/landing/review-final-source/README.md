# Final source freeze and proposed documentation repairs

**Not yet clear to merge.** The eleven-file source freeze is consistent with the approved source scope. Three Catalog rule-10 holds and the unchanged cross-file first-entry interface remain with the maintainer. The separate compiler-equation publication accounting below must also be dispositioned explicitly. This review grants no API or debt approval and runs no Lean or screen.

## Frozen inputs and result

`capture.json` pins all eleven current source SHA256s, independently verifies API commit `1160c18f03fd318f0dec25738790935fa61379d4` and producer commit `af3273f75d7602c079169f321e4536a58c7bb034`, and confirms exactly the eleven owned Lean files differ, with no untracked Lean files. A second check at finalization confirms every source is still unchanged. Inert full snapshots of all three stages are preserved.

The authored source census is **364→361 public declarations**, precisely the three gated forwarding exports and six Catalog retirements, and **1,079→763 private declarations**. All surviving public names, visibility, homes, full literal headers and relative order are preserved. The only import changes are the two approved Simulation/Mathlib-Fin and Catalog/Primitives edges. Standalone attributes, including the reader-generation commands, are unchanged. This is a source census, not the compiled namespace census.

`header-controls.json` checks nested named assignments, statement-local lets, proof-valued let assignments and an inner proof assignment. The full header reader skips each let value and its indented proof block. It does not stop at the first `:=` or truncate the Wrappers transport statements.

All **17 target admissions are discharged** in the captured source. The exact original three RAM admissions and their bodies remain frozen. No other static admission appears in the eleven files. `admissions.json` names every target and residual.

## Exact per-phase exceptions

API→current has three producer-level private strengthenings: `Complexity.counter_count`, `Turing.FinTM.loopHost_contracts`, and `loopHost_prepare`. They supply the intrinsic head bounds and explicit coefficient needed by the frozen public targets; the strengthened preparation is carried by the final statement-gate/brief. Producer→repair has exactly two private header re-expressions, both in Wrappers: `timedReady_dispatch` and `timed_ledger`. They explicitly transport the same branch through the approved tape-count/state equations. These are five changes across different comparison phases, not two unchanged private headers overall.

All **nine moved private data/type/instance declarations** match their actual API Catalog originals modulo the approved renames, including `f2_condHeads→timedHeads`, `polyHeads` and the forwarding controller family. The `pairMapSndTM` wrapper body and both theorem headers match the gated forwarding contract. Time coefficient **22** and payload-space coefficient **one** remain fixed.

All surviving executable declaration bodies are preserved except the two authorized private embedding `inj'` proof fields; only those final Prop fields are masked, leaving complete `toFun`/data prefixes unchanged. CertShell additionally changes a proof-local initializer expression to its explicit existing label. Its unsealed diagnostic, attributed to the CertShell owner, proves equality of the initializer, whole machine and transition table; production uses `runFrom_with_q₀`. Do not describe every proof-local witness expression as byte-identical.

`api-to-current.json` records **87 changed existing proof bodies plus 53 new/moved proof declarations = 140**: **64 public, 76 private**. `producer-to-repairs.json` records 81 repair-phase proof roots. Catalog has 24 changed existing proofs and three new helpers; the four framed run rows are **doc-only**. The repair-phase Catalog public proof delta is thirteen, including the four T5 endpoint/increment proofs and nine time/space-row repairs. WordSize has no code/proof change. CertShell and WordSize each have one separate leading-doc-only change.

All eleven current blobs match the passing owner/root source milestones (`supplemental.json`, fourteen exact receipt/source bindings). These elaborations are attributed to their original runners; none was executed by this read-only review.

## Compiler-equation accounting

The two new explicit rewrite references are `Turing.solveSplit.eq_def` and `Turing.solveSplitWith.eq_def`. The earlier name/type checks showed that the names resolve; they did not establish already-stored Convention declarations. The actual final compiled census materializes **two additional non-private, non-internal theorem constants owned by Primitives**, beyond the three authored source exports.

Lean 4.25 reserves these names and realizes their equation theorems on demand. The parent reports an independent native Convention-only before/after probe confirming that the reserved names are realizable before migration. `compiler-equations-excerpts.lean.txt` and `generated-equation-accounting.json` retain the compiler mechanism and actual final owner records. The defining functions live in Convention; the materialized declarations in this tree live in Primitives. Dynamic availability is not silently treated here as user approval, a hand-authored source addition, or Convention ownership. The pack must disclose the +2 materializations and the parent's published-reader/scope disposition.

## Citation population and retirements

`proof-roots140.json` and `.tsv` provide exact full names, owners, private flags and source lines for the native probe. Source citation ownership is retained in `source-citations.json`, including public-abbreviation implementation expansion and uncertain lexical candidates. The parent's subsequent native inventory confirms all **140 roots plus 228 descendants**, standard axiom closures, and 5,390 direct TCSlib citation edges across twenty homes. That native check is separately owned and recorded at `../changed-proof-citations/summary.json`.

The full proposed comparison population is **25 files**, `screen-population-final-review.txt`: the conservative union with the existing twenty-two, plus route/comparison context. InputCall is retained through actual `exists_inputCallTM` references in unchanged consumer helpers; `callTM_run` itself is in Loop. InputRewind is explicitly cited by the peer matcher route comparison. Contract/Basic and StepBlock are retained conservatively; the initial lexical `.trans`/`exit` matches are not asserted as native dependencies. The native twenty-home inventory adds no file outside this union. No screen was run here.

Exact retired-name enumeration covers **all 929 TCSlib files** and the explicit maintained-document population: **zero code hits and zero comment hits**. The three live-document hits are one historical backlog ruling, intentionally retained, and two registry pointers. `proposed-postmerge-registry.patch` updates those two pointers only after the retirement merges; it makes no premature merge/status claim.

## Comment-only proposals

`proposed-source-comments.patch` contains **22 comment edits in four files**. It corrects Catalog's obsolete Primitives-byte-identity claim, Simulation's “everything public” claim, the Primitives witness list/admission status/packaging description, and Loop's historical unproved/ledger prose. Ten moved forwarding proofs gain specific leading sketches, wrapped to at most 100 columns without generic book-attribution tags. Every proposed source has identical non-comment tokens to its captured source (`comment-proposals.json`); no actual source was changed. The parent reviewed the corrections and requested the final wrapping/ledger wording.

All source snapshots, comparison inputs, complete per-file counts, proposed full comment sources, patch bases, static preparation failures/corrections and hashes are retained. No source or Git mutation, snapshot/cache operation, Lean process, screen, dispatch, commit or push occurred in this review. The parent may now apply the authorized comments, re-pin the resulting source hashes and proceed with its draft PR and final replay while the human interface rulings remain pending.
