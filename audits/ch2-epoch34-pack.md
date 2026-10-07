# External audit pack — Chapter 2, epoch-3/4 fill gate

Audits the **proofs** of the 21 epoch-3/4 targets — the six-member
exponential padding cluster (`ntime_expPow_subset_NEXP`,
`NEXP_eq_iUnion_NTIME`, `NEXP_subset_iUnion_NTIME`,
`EXP_eq_NEXP_of_P_eq_NP`, `P_ne_NP_of_EXP_ne_NEXP`, `EXP_subset_NEXP`);
the SAT track (`SAT_mem_NP`, `SAT3_mem_NP`, `SAT_reducible_SAT3`); the
five snapshot-locality lemmas (`snapshotAt_zero`, `snapshotAt_state_succ`,
`snapshotAt_inputSymbol`, `snapshotAt_workSymbol`,
`oblivious_schedule_eq`); `TAUTOLOGY_mem_coNP`; and the epoch-4 summit —
`NPHard.polyTimeReducible`, **`SAT_NPHard`, `SAT_NPComplete`,
`SAT3_NPHard`, `SAT3_NPComplete` (Cook–Levin, Theorems 2.10.1–2.10.2)**
and **`TAUTOLOGY_coNPComplete`** (Example 2.21) — filled by **16 Codex
commits across 14 accepted zip deliveries** with **1,206 net new private
declarations** in six files: `ClassNP/{Nondeterminism, EXP, SAT,
Tautology}.lean`, `CookLevin/{Snapshot, Hardness}.lean`. With this gate
the Chapter-2 ledger stands at **59 of 59** original admissions proved:
the campaign tree is **admission-free** — 11,436 checked kernel
declarations across the 65-module surface, zero `sorryAx`, axioms at
most `propext`/`Classical.choice`/`Quot.sound` everywhere.

The **statements are not in question here**: all 21 were frozen at the
phase-1/3/4 statement gates (`audits/ch2-phase{1,3,4}-*`), with one
recorded carrier exception — merge #1's `TAUTOLOGY` definition retype
onto the refactored `Std.Sat.DNF` wrapper, a **ride-along re-audit item
below**. This is the fill-epoch proof audit in the mold of the epoch-1,
epoch-2, and emitter fill gates: proof correctness and helper hygiene
against the frozen statements, the inherited invariant/boundary tables
(carried verbatim in the attached briefs), and the audited
machine-construction and emitter libraries. Gate closes on **zero
blockers/majors**. Record findings in `audits/ch2-epoch34-findings.md`.

**Evidence separation.** Out of scope: the machine-construction library
(`Build/`, two closed gates) and the **emitter increment** (statement
gate closed in three rounds, fill gate in one —
`audits/emitter-{infra,fill}-resolutions.md`; its four Codex fills lie
inside this span but were audited there); the phase-gate statement
layers; the colleague's Chapter-6/TimeHierarchy/SpaceComplexity trees
(their own audit responsibility; only their **touches on the six owned
files** are in scope, itemized in the span attestation §3); the
`SizeClasses.lean` and LMN sorries (outside the campaign surface, on
record since the ch6 gate). The fills' *consumption* of every audited
contract — `exists_emitLoopTM`, `exists_installCallTM`,
`exists_emitCallTM`, `computesFunInTime_splitSolveWith`, `capture_run`,
`emit_run`, the catalog — is very much in scope.

## Maintainer-side integration attestations (verify or challenge)

The full evidence is the attached
`audits/evidence/ch2-epoch34/span-attestation.md`; summary:

1. **Whole-span accounting closes exactly.** Over `b55180a8` →
   `9e9494aa`, the six owned files change by fills +20,325/−98, merge #1
   +35/−39, merge #2 +217/−236 — summing to the endpoint delta to the
   line. The −98 decomposes as the 21 target `sorry` lines, A-3's 34
   sanctioned scaffolding deletions, 4A-5's 33 intra-delivery
   patch-1-rewrite deletions, and single-digit disclosed splices. The
   21 base sorries are exactly the 21 targets.
2. **Per-delivery verification** (each recorded at integration):
   archive checksums; per-patch deleted-lines audits; byte-identical
   format-patch replay in isolated worktrees before every `git am -3`
   (tree + blob hashes matching the REPORT claims); zip-embedded brief
   provenance from 4A-3 on.
3. **Surface.** All 1,206 net new source declarations are private; the
   fills changed no public name anywhere. Kernel-level surface passes
   (generated declarations included) hold for Hardness and Tautology.
   The merges' owned-file surface changes: the `TAUTOLOGY` retype
   (merge #1) and two public additions to `EXP.lean` (merge #2:
   `enumWord` promoted, `exists_proj_decider` new) — both itemized,
   neither deletes or retypes any frozen target.
4. **Elaboration.** Fresh-olean sweeps at every integration, zero
   `error:` lines; owned-file admissions stepping 21 → 13 → 6 → 5 → 5 →
   5 → 5 → 1 → **0**, each step predicted and matched. Final sweep
   65/65 with **zero sorry warnings tree-wide** (attached).
5. **Axioms.** The two committed closure programs (attached) and their
   logs: all 21 targets empty-rooted at the standard triple;
   no-allowlist whole-module enumerations (Hardness 1,550 checked
   declarations, Tautology 439); the whole-surface pass — 11,436
   checked `TCSlib` declarations, zero `sorryAx`.
6. **Policy.** Lint 0 FAIL throughout; five recorded size exceptions
   (Hardness 9,937; Nondeterminism 5,835; SAT 4,815; EXP 3,268;
   Tautology 1,749), all under exclusive single-file fill ownership,
   all queued for the approved post-gate routine-layer retrofit.
7. **Deviations on record**: the 4A chain's four verified partial
   checkpoints (each inside its continuation provision; 4A-5's
   output-identity checkpoint committed before semantics); the
   duplicate A-3 dispatch with β selected on recorded criteria and α
   discarded whole (hashes in the attestation); the A-cont-2 brief's
   maintainer scoping error, agent-escalated and resolved by
   reordering; four hosts' `/proc/<pid>/exe` shim and 4B's
   official-API cache recovery (pins unchanged everywhere); the A3/A5
   in-flight kernel-surface fixes via `delta`; the E3-D "68 vs 67"
   private-count discrepancy resolved by name-level inventory.

## Ride-along review items (first class, not errata)

* **Merge #1 carrier retype**: `TAUTOLOGY` restated on `Std.Sat.DNF`
  (wrapper type; `DNF.eval`/`DNF.Tautology`/`dual` pair/`eval_dual`/
  `tautology_dual_iff` renames), and the colleague's own adaptation of
  the 3D fill to it. Both Tautology targets were subsequently filled
  against the retyped definition. Attached: `Formulas/DNF.lean`,
  `Formulas/CNFEncoding.lean`. Review: the retype's faithfulness (the
  DNF reading of the shared serialization; the fallback-outside-
  TAUTOLOGY convention) and the adapted membership proof.
* **The duplicate A-3 dispatch**: review the selection criteria
  (integrity tie → audited-surface consumption → route fidelity →
  economy) and the no-hybridization rule as governance for duplicate
  parallel runs.
* **Merge #2 drift on owned files**: private rewiring in `SAT.lean`/
  `EXP.lean` toward the colleague's shared modules after those files'
  fills closed, plus the two `EXP.lean` public additions; the module
  order grew 57 → 65 (dependency-asserted; the first merged sweep's
  honest failure and resume are in the attached merge log's committed
  copy). Review: that the rewires preserve the audited proofs'
  substance (the sweeps and traversals say yes; challenge the method
  if not the result).

## What is under audit, and priorities

The 21 proofs and 1,206 private helpers, against the frozen statements,
the phase-gate boundary/invariant tables (verbatim in the attached
briefs), the audited library contracts they consume, and the agent
REPORTs (attached; challenge any attestation the maintainer layer does
not independently cover). Priorities, riskiest first:

1. **The 4A-5 semantics** (`clA5Reconstruct`, `clA5Certificate`,
   `clA5Sound`/`clA5Complete`/`clA5Equisat`, `clA5NoFalse`,
   `clA5Decider_accept`, `clA5Reduction`): the strong induction over
   time against **raw bitwise** product slices (decoded equality only
   after raw equality — the junk-block discipline); certificate
   recovery from the pinning units; acceptance solely from the total
   decider's exact singleton output at the horizon (silence never
   accepts; no `[false] ++ serialize` prefix); the reduction through
   `decode_serialize` with no well-formedness branch.
2. **The 4A-5 output identity and budget** (`clA5OutputIdentity`,
   `clA5Output_of_nativeChunk`, `clA5Round`, `clA5Fuel`): the
   `clEmitter_of_body` + `clTableau_chunks` instantiation yielding
   exactly `serialize (clTableau …)`; the one common polynomial `P`
   covering startup/fuel/every whole round, **distinct from the horizon
   `T` and from the producer ledger**; positive rounds including the
   silent saturated round at `min (i+1) (R+1)`; the family order,
   `R`-last-index-versus-`R+1`-members, and the sole final terminator.
3. **The 4A-4 producer** (`clPackedRecords_native`/`_machine` and its
   47-declaration assembly): the greatest-strictly-earlier search built
   from charged sequential loads (`clWipe*`/`clFresh*` resets
   discharging the reader's overwrite precondition on every restart —
   the reader moves forward only); the strict prefix `s < t`; time-zero
   and frozen-visit cases; `clVisitCode` distinguishing absence from
   predecessor zero; the honest replay-recomputation accounting (every
   reference-run replay charged — verify no uncharged lookup); the
   total ledger's composition to one monomial.
4. **The 4A-3 recorder and comparator**: the stored inclusive
   trajectory `0..T` (`clRec_complete`, initial and final rows); the
   silence invariant; signed positions as **cross-sums**
   (`clSigned_eq`, `clCmp*` — never raw-encoding equality); the shifted
   input coordinate and clamp-before-counter; counts frozen after halt;
   the stored-format theorems being pure (no free indexed access).
5. **The 4A-2 preparation**: the exact header fields (zero
   coefficient/degree/horizon cases); the silent reference simulation
   identified with the public all-false schedule at every time
   (verdict suppressed, effects-first terminal writes); the counter's
   **deliberate machine change** from its `TimeConstructible` source
   (silent absorbing return; carry/rewind re-proved, first return
   `≤ 2|w|+2`).
6. **The 4A pure layer** (77 privates): `clTableau` on the fixed
   Claim-2.13 templates (no one-hot consistency families); the product
   encoding's totalized decoder (junk blocks to halted/blank); the
   chunk-exact `clTableau_chunks` (empty groups occupy rounds; sole
   last terminator); the quadratic bound as **output-size only**; the
   conditional `clEmitter_of_body`'s hypotheses actually discharged by
   items 1–2.
7. **3B-cont** (`SAT_reducible_SAT3` as an `exists_emitLoopTM`
   instantiation at `R n = n` under the binding r2-finding-5 normalized
   schedule): marker-free seams; round-local buffering; the chunk table
   as the banked `satChain`/`satSplitClause`/`satTransformFrom`
   induction; validation including trailing data before the first
   clause marker; the discarded raw transducer states as sanctioned.
   Then the **B wave** memberships: complete-syntax-pass-first, the
   `[true,false,false,true]` case on the accepting fallback branch,
   width scan only after full parse, `(1,1)` certificate splits.
8. **The padding cluster** (A/A-cont/A-cont-2/A-3 β): the
   `splitSolveWith` exponential instantiations; β's direct consumption
   of `exists_installCallTM` destructuring `0 < C.k`; Theorem 2.22's
   pre-validation bit bound with both exact checks; the reverse host's
   binary countdown; the width-parametric evaluator at
   `f n = 2^((n+1)^c)`; the A-cont bank's clean seams (track/clear
   discipline).
9. **3C locality and the Tautology pair**: the Derivation-A row-by-row
   discharge (strict `s < t` from `List.range`; the halting write
   retained; `some none` erases, outer `none` preserves); 3D's dual
   verifier (empty term forces rejection, empty formula acceptance)
   under the retyped carrier; **4B**: the five definitional hardness
   links on every string; the `R(n)=0` one-round transducer (the
   malformed branch's sole `[false]` emission equal to the serialized
   dual fallback; no valid-looking prefix from malformed suffixes; the
   polarity bit as the last bit of each literal record; linear ledger).
10. **Hygiene across the span**: the no-touch rule (checkpoint strata
    cited or ignored, never modified — verify no final proof routes
    through a superseded helper with an unfinished contract, notably
    the A-chain's `clFill*`, `clCertificateCall`'s deliberately
    narrower variant, and `clTrack_schedule`); privates match stated
    contracts; nothing public-worthy smuggled private; library
    contracts consumed at their audited statements; the deliveries'
    kernel-traversal claims spot-checked against the attached programs.

## Dispositions requested

* **E5-closure dedup scope**: the superseded strata now include the
  A-chain's banked-but-unconsumed components alongside the epoch-2
  families. Maintainer position: one serial post-gate dedup under the
  standing E5 discipline. Review the deferral; flag anything whose
  retention masks an unaudited route.
* **The five size exceptions → the routine-layer retrofit**: recorded
  decision (2026-10-06) to retrofit after the §12 design gates, folding
  D7. Review whether anything forces earlier action.
* **The 65-module order**: review the extension's legitimacy as the
  campaign's verification surface (dependency-asserted insertions; the
  colleague's shared modules now inside the sweep).

Severity scheme as always: blocker / major / minor / note; findings to
`audits/ch2-epoch34-findings.md`; this pack is immutable once sent
(errata via the resolutions file).

## Verification appendix (runs and manifest)

* Integration sweeps: logs committed per integration
  (`audits/logs/ch2-e3-*`, `e3contA3B-*`, `e4A-checkpoint-*`,
  `e4A2/3/4-checkpoint-*`, `e4A5-closure-*`, `colleague-merge2-*`,
  `e4B-closure-*`); the final three attached.
* Closure attestations: the two committed programs (attached) and
  their logs; the 4B log attached, exit 0, every expectation met.
* Lint: `e4B-closure-lint.log` (attached): 0 FAIL in scope.
* Bundle manifest — **45 attachments** after the pack: the 6 owned
  sources (`Nondeterminism`, `EXP`, `SAT`, `Snapshot`, `Tautology`,
  `Hardness`); the 3 carrier/model files (`Formulas/DNF`,
  `Formulas/CNFEncoding`, `ClassNP/CoNP`); the 14 briefs
  (`ch2-epoch3-batch{A,B,C,D}`, `ch2-e3cont-batch{A,A2,A3,B}`,
  `ch2-epoch4-batch{A,A2,A3,A4,A5,B}`); the 14 agent REPORTs
  (epoch-3: `batch{A,B,C,D}`, `batchA-cont{,2,3}`, `batchB-cont`;
  epoch-4: `batch{A,A2,A3,A4,A5,B}`); the 2 closure programs; the 4
  final logs (`e4B-closure-{sweep,axioms,lint}`,
  `e4A5-closure-axioms`); the span attestation; the 65-module order
  list. Total 6 + 3 + 14 + 14 + 2 + 4 + 1 + 1 = 45. The phase-gate
  findings/resolutions, the emitter-gate records, the design document
  (§11–§11d), the decision log, and all earlier integration logs are
  committed in the repository at the paths the briefs and REPORTs cite.
