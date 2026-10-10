# Backlog

The consolidated tracking file for the Arora-Barak campaign branch
(`complexity/arora-barak-ch1`) and adjacent repository work: human-review
design questions, queued and on-hold campaign work, deferred formalizations,
pending decisions, and housekeeping. Consolidated 2026-09-18 from the two
campaign plans, the audit resolutions records, and session assessments.

**Conventions.** This file is the *canonical home* of the human-review
question statements (§1) — the plans keep stable numbered stubs, since audit
documents cite the numbering — and the *tracking index* for everything else
(scope prose remains in the plans; decision-log history is never moved).
New items land here; an item leaves only by a decision recorded in the
relevant plan's decision log. From the next audit round onward this file
joins the bundle attachment set.

---

## 1. Human-review design questions (reserved — never closed by an automated gate)

Flagged for a **human** auditor/maintainer: the LLM audit rounds verify
correctness, but these are matters of architectural taste and trust-surface
policy.

### CH1-Q1 — the 3A Mathlib-computability bridge

*Origin: `AroraBarakChapter1Plan.md` §5 (epoch 3, batch A);
`MathlibBridge.lean`, `Turing.exists_effectiveMachineCode`.*

The audited docstring sketch called for the canonizer machine to be
**hand-assembled from this repository's composition combinators** ("its
construction uses the composition combinators", optionally with a polynomial
`canonizerTime`). The delivered proof instead (i) proves the canonization
*function* primitive recursive, (ii) compiles it through **Mathlib's verified
recursion-theory pipeline** (`ToPartrec.Code.exists_code` →
`PartrecToTM2.tr_eval`), (iii) simulates the resulting TM2 stack machine in
our model with a bespoke private `bridgeTM`, and (iv) lands in the binary
alphabet via the proved `alphabet_reduction`, extracting the time bound by
finite maxima (no polynomial bound claimed — permitted, since
`canonizerTime` is existential). The batch flagged the deviation itself; the
maintainer verification pass confirmed the proof is sorry-free with the
standard axiom footprint and zero public-interface drift. **Open questions
for a human:** (a) is the heavyweight `Mathlib.Computability.TMToPartrec`
import into the TM tree acceptable, or should the bridge be quarantined
behind the planned phase-5 `MathlibBridge` module boundary (it effectively
front-runs that module)? (b) is the enlarged trust/review surface (Mathlib's
TM2 semantics + the private `bridgeTM` simulation, ~150 private
declarations) preferable to a longer but self-contained combinator
construction? (c) should the abandoned polynomial-`canonizerTime` claim be
recorded as permanently out of scope, or re-derived later from the
combinator route if one is ever written? Since the epoch-3→4 merge the
bridge lives in the dedicated `MathlibBridge.lean`, which implements the
quarantine that part (a) contemplates — the `TMToPartrec` import is confined
to that one module and nothing outside `exists_effectiveMachineCode` depends
on it — but the implemented quarantine does **not** dispose of this
question: parts (a)-(c) remain open for human review (epoch-4 audit,
finding 3: an earlier version of this text misplaced the bridge inside
`Encoding.lean`).

*Cross-link: part (c) gained relevance in Chapter 2 — see §3, "Polynomial
canonizer for a concrete scheme".*

### CH1-Q2 — the 3B universal-interpreter proof architecture

*Origin: `AroraBarakChapter1Plan.md` §5 (epoch 3, batches B + B2);
`Universal.lean`, `Turing.universal`.*

The proof followed the audited sketch's outline (prefix-only startup,
canonizer capture onto a table tape, four-work-tape interpreter with a fixed
finite controller), but the realized architecture is by far the campaign's
most involved artifact: 2465 lines (2831 after the epoch-4A timed fill), 104
private declarations built across two agent sessions (WIP `f191b918` +
continuation), a bespoke checkpoint relation (`universalRelation`) with
generic block-simulation assembly (`universal_block_run` /
`universal_from_blocks`), a virtual left boundary via a marker tape, a unary
state tape with group-wise table scanning, and an *exact* per-phase cost
ledger realized to `universalBlockBound = 3L + 5N + 20`. The kernel checks
all of it, and the public statement is frozen and audited — but the *design*
was never itself an audit deliverable at this level of detail. **Open
questions for a human:** (a) is this the right load-bearing shape — and
which parts (the capture wrapper, the block-run/`universal_run_join`
assembly, the marker-directed rewind and unary-copy gadget patterns, all
flagged by the agents as promotion candidates) should graduate to shared
modules rather than being re-derived? (b) is the exact-ledger posture
(`3L + 5N + 20` proved to the transition) worth its brittleness against any
future change to `CodeTM.serialize`, or should the maintained invariant be
an existential bound with the exact ledger demoted to documentation? (c)
does the interpreter's claim to *be* the book's universal machine (as
opposed to satisfying the frozen statement, which the kernel settles)
deserve a targeted human read of the construction's core definitions
(`UniversalControl`, `universalInterpreter`, `universalRelation`), given no
executable diagnostics of the whole interpreter ever ran (the batch-B smoke
tests aborted on deep recursion and were discarded)?

*Cross-link: question (b)'s exact ledger is now also load-bearing for the
Chapter-2 `TMSAT_mem_NP` fill (the quantitative public bridge, §2), which
will expose a form of the constant publicly.*

### CH2-Q1 — generality of `HALT_not_mem_NP`

*Origin: `AroraBarakChapter2Plan.md` (phase-1, round-2 audit, finding 3);
`ClassNP/Reductions.lean`.*

The statement is currently at `Turing.EffectiveMachineCode` generality
because its proof route reuses Chapter 1's `HALT_not_computable`, whose own
proof runs the universal evaluator. The round-2 auditor showed this
restriction is **not mathematically necessary**: a direct diagonalization —
the public diagonal-pairing machine, the searcher's finite-control transform
with the halt/loop roles swapped, `Turing.exists_codeTM`, no evaluator —
proves `HALT` undecidable for *every* lawful `Turing.MachineCode` (and the
earlier "trivial-machine scheme" counterexample is unlawful: constant
decoding violates `decode_encode`). **The question:** add that diagonal
lemma as a new audited statement (a strengthening of Chapter 1's
uncomputability story that shares its main fill obligation, the
control-transform lemma, with `HALT_NPHard`) and generalize
`HALT_not_mem_NP` to `MachineCode` — or keep the conservative signature as a
documented API/proof-route restriction? Maintainer's provisional choice,
pending review: the conservative signature, with the docstring stating the
restriction honestly; the diagonal lemma is deliberately *not* slipped into
a repair round, since it would enlarge the audited surface of Chapter 1's
uncomputability chapter.

---

### CH7-D1 — the block stack's per-loop lemma family (duplication threshold crossed)

*Origin: the ch7 fill gate, run on the merged ch3-4 tree after PR #11
(`audits/ch7-fill-pack.md`, question 7); maintainer pre-screen
`audits/evidence/ch7/ch7-fill-duplication-screen.md`. This item is opened
under `workflow.md` §4, which leaves no discretion once a file passes one
fifth copied material.*

The OR, XOR and strict-majority block loops each re-prove the same orbit,
length and init lemmas under renaming. The proofs are identical up to the
step function's name, so a single lemma quantified over the step function
would serve all three. Six `private` members:

- four in `ClassNP/PolyTimeBlockMajority.lean`: **4 of its 14 declarations
  (28.6%, 85 lines), over the threshold**;
- two in `ClassNP/PolyTimeBlockTests.lean` (2 of 25).

No pre-existing repository material is copied. **The question:**
acknowledge the debt and name its owner and resolution window. The fill
gate's auditor is instructed to report the family at major ("human
acknowledgment required", `audits/TEMPLATE.md` failure mode 5), and the gate
cannot close until this is answered.

Maintainer's provisional proposal, pending review: the owner is the
Chapter-7 campaign (Aparna). The window is the post-gate cleanup her pack
already proposes for splitting the counting layer out of
`Randomized/Classes.lean`. The resolution is one generic orbit/length lemma
set in `PolyTimeBlockLoop.lean` consumed by all three loops, with statements
unchanged. The alternative is to fold it into 12.2c alongside the EmitIter
harmonization.

**Answered (user, 2026-10-10): fold into 12.2c.** The debt is acknowledged.
The owner is the user's own 12.2c per-theme refactor, not the ch7 campaign:
deduplication is being done there anyway, and colleagues are spared it. The
resolution is one generic lemma set with statements unchanged, coordinated
with the ch7 owner because the files are hers, and run after the ch7 fill
gate closes.

---

## 2. Campaign work queued or on hold

* **Chapter-2 fill campaign (E1-E5)** — **active** (hold lifted
  2026-10-02 after the ch-6 integration and audit closed). All four
  statement-phase gates closed; 59 audited-true admissions.
  **Epoch/batch partition recorded** in `AroraBarakChapter2Plan.md` §4
  (fill-campaign subsection): E1 assemblies + poly-calculus + formula
  mathematics (batches 1A–1D, 28 targets), E2 enumerator + compilations +
  Ex 2.1/HALT + `TMSAT` (2A–2D, 11), E3 padding + SAT track + snapshot
  locality (3A–3D, 14), E4 the Cook-Levin summit + TAUTOLOGY dual (4A–4B,
  6), E5 closure. Padding moved E2 → E3 (recorded refinement);
  `EXP_subset_NEXP` 1C → 3A (recorded amendment). **E1 integrated 2026-10-02**
  (27/27 targets filled, nine agent commits, freeze audit clean, 32
  admissions remain, zero `sorryAx` across all fills); **epoch-1 gate CLOSED**
  2026-10-02, single round, 0 blockers/majors
  (`audits/ch2-epoch1-resolutions.md`); 27/59 proved, 32 remain.
  Deferred from E1: promotion of 1D's `foldr_max_le_of_forall` **and its
  companion `le_foldr_max_of_mem`** (auditor suggestion) to a shared list
  utility (disposition D3).
  **E2 briefs issued** 2026-10-02
  (`briefs/ch2-epoch2-batch{A,B,C,D}.md`; 10 targets + the mandated
  `timed_universal` bridge statement; inheritances embedded verbatim;
  hardened repo/branch headers; D1 axiom wording).
  **E2 checkpoints integrated 2026-10-03 — all four batches partial, epoch
  gate OPEN** (four Codex commits `da8bd091`…`4b4cd418` off `6c09453e`;
  maintainer verification clean — deleted-lines, surface, replay, fresh
  53-module sweep with 29 direct admissions, axiom-root traversal matching
  every REPORT; logs `audits/logs/ch2-e2-checkpoint-{sweep,axioms}.log`;
  decision-log row in the ch2 plan). 5 of 10 target bodies written;
  admission-free closure: `timeConstructible_poly` only. Uniform frontier:
  concrete machine construction/timed integration (147 helpers delivered,
  145 admission-free). Open sites: 2A's single `enumMachine_contracts`
  (closes `NP_subset_EXP` **and** both HALT targets), 2B's
  `choiceVerifier ∈ P` + untouched reverse direction, 2C's two verifier
  memberships (`CONTINUATION.md` shipped), 2D's `D-MEM`/`D-WRAP`/`D-EMIT`
  (+ the bridge escalation — **RESOLVED 2026-10-03**: Chapter 1 exports
  `Turing.timed_universal_concrete` and the TMSAT bridge is discharged
  via `tmsat_concrete_coefficient` + monotonicity; `TMSAT_mem_NP` now
  roots at `D-MEM` alone, tree admissions 46; decision-log rows in both
  plans). 2C also requests promotion of `prefixTM`/`fixedPair`
  fixed-prefixing lemmas (held with D3; subsumed by Build P3/P6 at the
  shared round).
  Next (sequencing per the frozen library design, 2026-10-03; spec
  layer and bridge export both landed 2026-10-03): the shared
  infrastructure audit pack (Build spec surface + the bridge export and
  its TMSAT discharge) → gate → library fills (harvest-adaptation
  batches; loop flagged for continuation budget) → E2 continuation
  briefs citing the library → epoch-2 audit.
* **Machine-construction library** (`machine-library-design.md`, design
  FROZEN 2026-10-03; decision-log rows in `AroraBarakChapter1Plan.md`):
  `TuringMachine/Build/{Convention,Wrappers,Loop,Primitives}.lean` — 12
  primitives (P1–P12, harvest-heavy), capture/silence + halt-redirect +
  timed cond wrappers, the bounded-loop combinator factored from 2A's
  `enumMachine_contracts`. **Spec layer LANDED 2026-10-03** (design §9a
  refinements recorded): `Cfg.ofWords` seam + pure vocabulary fully
  proved; 18 sorried contracts (4 wrapper, 2 loop, 12 primitive); order
  list and facade at 57 modules. **Bridge export landed 2026-10-03**
  (`Turing.timed_universal_concrete`; TMSAT bridge discharged, tree
  admissions 46). **Infra audit pack prepared 2026-10-03**
  (`audits/ch1-infra-{pack,bundle}.md`). **Round 1: gate OPEN** (blocker:
  `exists_loopTM` refuted by zero-step advances; majors: all-state-word
  round domain, D5 interface gaps). **Round-2 repairs executed +
  re-audit pack prepared 2026-10-03** (`audits/ch1-infra-r2-{pack,
  bundle}.md`): loop redesigned (positive duration, input-indexed `Inv`,
  input-dependent step/accept), `exists_loopFindTM` + P13 `pairConcat` +
  P14 `pairDup` + C1 `pairMapSnd` added, sketches corrected, errata
  acknowledged, historical evidence supplied, D5 re-issued as a concrete
  mapping; Build 22 contracts, tree 50 admissions. **Round 2: 0
  blockers, 1 major, 3 minors** (loops/P13-P14-C1/tables passed; the
  major: the final-answer loop conclusion cannot discharge
  `enumMachine_contracts`). **Round-3 repair executed + pack prepared**
  (`audits/ch1-infra-r3-{pack,bundle}.md`): `exists_loopCfgTM`
  configuration-level export + §9c translation, coefficient-shift and
  pairing-derivation notes adopted, D5 v3 narrowed to epoch-2 + P10;
  Build 23 contracts, tree 51 admissions. **GATE CLOSED 2026-10-03**
  (round 3: 0 blockers/majors, 3 documentation minors swept in the
  closing commit; `audits/ch1-infra-resolutions.md`): the spec surface
  is audited-true, D5 v3 approved (D-MEM explicitly limited; 2B
  component-level; E3/E4 deferred to their brief audits), the
  `enumMachine_contracts` translation certified exactly. **Fill briefs
  issued 2026-10-03** (`briefs/lib-fill-batch{W,P,L}.md`: 4 + 15 + 4
  targets, 14/34/18 pts, P and L with continuation anticipated;
  sanctioned roots `capture_run` → P/L and `exists_loopFindTM` →
  P-splitSolve; L carries the round-3 item-4 construction ledger as
  binding). **Checkpoints integrated 2026-10-03**: W complete (4/4,
  admission-free; `cond` multiplier 5; two promotion requests held for
  the fill-audit round), P 11/15 (frontier `pairLenCheck`; sanctioned
  roots unused), L the 2A pattern (`loop_run` + both summation lemmas
  proved; combinators at the single admitted `loopHost_contracts`;
  `capture_run` consumed in the helpers). Tree: 57/57 zero errors,
  **33 admissions**; size exceptions for `Primitives.lean` (1,687) and
  `Loop.lean` (1,466) recorded. **Continuation briefs issued 2026-10-03**
  (`briefs/lib-fill-batch{P2,L2}.md`, base `90273dd6`): P2 = targets
  12–15 (14 pts; one sanctioned root, `loopHost_contracts` via
  `exists_loopFindTM`, for `splitSolve` only); L2 = `loopHost_contracts`
  (10 pts; zero sanctioned admissions — completion ends the file
  admission-free; the checkpoint agent's continuation document is
  binding). Next: dispatch, then integration, then the library
  fill-audit round (carrying W's two promotion requests and the P/L
  size exceptions), then the E2 continuation briefs.
  **Round 2 integrated 2026-10-04: L2 COMPLETE** (`loopHost_contracts`
  proved; the loop admission-free end to end, realized constant 10),
  **P2 13/15** (12–13 filled via the proved W layer; target-14
  relocation support proved; frontier `pairMapSnd`/`splitSolve`).
  Tree: 57/57 zero errors, **30 admissions**; 21/23 contracts
  admission-free. **P3 closure brief issued 2026-10-04**
  (`briefs/lib-fill-batchP3.md`, base `b2f46419`; targets 14–15, 8 pts,
  zero sanctioned admissions; completion = 23/23, the whole `Build/`
  tree admission-free). **P3 integrated 2026-10-04: `pairMapSnd`
  PROVED (coefficient 40), 22/23**; `splitSolve` reduced to the body
  controller (`splitSolve_of_body` + proved components; one named
  gap). Tree: 57/57 zero errors, **29 admissions**. **P4 closure brief
  issued 2026-10-04** (`briefs/lib-fill-batchP4.md`, base `494d4835`;
  one target, 5 pts, zero sanctioned admissions; the P3 frontier
  document's ten steps are the work plan; completion = 23/23).
  **P4 integrated 2026-10-04: THE LIBRARY IS COMPLETE — 23/23,
  `Build/` admission-free, tree at 28 campaign-only admissions**
  (W 1 round, L 2, P 4; ~250 new privates; every sanctioned root
  closed at merge). **Fill-audit pack prepared 2026-10-04**
  (`audits/ch1-libfill-{pack,bundle}.md`; whole-span attestation:
  net deletions = exactly the 23 placeholders, zero non-private
  additions). **GATE CLOSED 2026-10-04, single round: 0 blockers, 0
  majors, 2 instrument/documentation minors swept in the closing
  commit** (`audits/ch1-libfill-resolutions.md`). **The library is
  complete and audited end to end.** D6 approved-deferred (serial
  promotion of `timed_input_bound`/`timed_rewind`, post-gate); D7
  approved-trailing (the `Loop`/`Primitives` split, ride-along
  audited, with the auditor's cross-file-privates qualification
  binding). **E2 continuation briefs issued 2026-10-04**
  (`briefs/ch2-e2cont-batch{A,B,C,D}.md`, base `64d82f84`).
  **Integrated 2026-10-04: A/C/D COMPLETE, B 1-of-3** — nine of ten
  epoch-2 targets admission-free (enumerator cluster incl. the HALT
  pair; Exercise 2.1; the full TMSAT package); B's one frontier is
  the integrated reverse NDTM host (guessing phase, coverage, and
  normalization banked; five-step plan in its REPORT). Tree: 57/57
  zero errors, **23 admissions**; ch2 ledger **36/59 proved**. Next:
  the B reverse-compiler continuation brief, then the epoch-2 audit.
  **B2 brief issued 2026-10-04** (`briefs/ch2-e2cont-batchB2.md`, base
  `e72d95bf`; 9 pts; zero sanctioned admissions; completion closes the
  epoch at 10/10). **B2 integrated 2026-10-05: EPOCH 2 CONSTRUCTION
  COMPLETE — all ten targets admission-free** (commit `1514fd6b`;
  Theorem 2.6 machine-checked both directions; 42 new `b2*` privates;
  scheduler seam closed by read-normalization, dispatch on the actual
  first halt, definitional table coincidence; independent kernel
  traversal `audits/logs/ch2-e2cont-B2-axioms.log`). Tree: 57/57 zero
  errors, **21 admissions** (5 padding + `EXP_subset_NEXP` + 15 E3/E4
  statement layer); ch2 ledger **38/59 proved**. **Epoch-2 audit pack
  prepared 2026-10-05** (`audits/ch2-epoch2-{pack,bundle}.md` + the
  whole-span attestation under `audits/evidence/ch2-epoch2/`; 34
  attachments). **GATE CLOSED 2026-10-05, PASS in one round: 0
  blockers, 0 majors, 2 minors (audit-material errata, swept via
  `audits/ch2-epoch2-resolutions.md`), 11 notes** — the auditor
  rebuilt all 57 modules from empty oleans and verified all 386
  privates / 1,167 kernel declarations admission-free. **Epoch 2 is
  complete and audited end to end.** The post-gate serial queue is
  unblocked, in order: **D6 promotions — EXECUTED 2026-10-05**
  (`Turing.MultiTapeTM.timed_input_bound` in `Deterministic.lean`,
  symbol-generalized; `Turing.FinTM.timed_rewind` in `Simulation.lean`
  verbatim; Wrappers privates removed, clients on the public API;
  57/57 zero errors, 21 admissions unchanged, promoted lemmas +
  epoch-2 closure regressions all clean —
  `audits/logs/d6-promotion-{sweep,axioms,lint}.log`), then **D7 —
  EXECUTED AS A MEASURED DEFERRAL 2026-10-05**
  (`audits/evidence/d7-split-analysis.md`; tool
  `scripts/d7_split_analysis.py`): pure relocation infeasible — each
  file is one private family (96–99.9% span); compliant splits need
  ≥ 125 cross-file promotions program-wide (34/43/24/16/8 per file),
  intersecting E5's live-replacement/deletion sets, so the physical
  splits run **after E5** via one internal-namespace visibility
  proposal, ride-along reviewed in the E3 pack (pilot: the
  Nondeterminism forward/reverse cut, cost 5); size justifications
  stand — then **E5 — EXECUTED 2026-10-05, deletion-only** (the three
  inventoried dead families removed: 28 privates, 549 lines; EXP
  2,887 → 2,534, Nondeterminism 2,627 → 2,454; live routes untouched;
  contract-evidence lemmas deliberately retained; 57/57 zero errors,
  21 admissions unchanged, closure regressions PASS —
  `audits/logs/e5-dedup-{sweep,axioms,lint}.log`; D7 re-measured
  post-E5: 34/43/24/13/8, deferral confirmed). **The post-gate serial
  queue is complete.** **E3 briefs issued 2026-10-05**
  (`briefs/ch2-epoch3-batch{A,B,C,D}.md`, base `b55180a8`; 3A padding
  cluster 26 pts / 3B SAT track 24 pts (continuation anticipated) / 3C
  snapshot locality 22 pts / 3D TAUTOLOGY membership 6 pts; zero
  sanctioned admissions; completion closes the E3 statement layer at
  15 targets). **Integrated 2026-10-05: C/D COMPLETE, B 2-of-3, A at
  the exponential split body** — 8 new closures (the five snapshot
  locality lemmas, both SAT memberships, TAUTOLOGY membership); tree
  57/57 zero errors, **13 admissions**; ledger **46/59 proved**. Two
  new size exceptions recorded (SAT 2,363; Tautology 1,278). A's
  frontier: the native exponential split-search body existential
  (five-step plan in its REPORT; 35 `e3_*` privates banked). B's
  frontier: run lemmas + time proof for `satRedTM`'s streaming states
  9–34 (startup proved; all reduction mathematics banked).
  **Emitter-increment design drafted 2026-10-05**
  (`machine-library-design.md` §11, awaiting decisions 11.1–11.3:
  `emitLoop` + `emitPhase` + P16–P18 + width-parametric split search;
  ≈ 27 pts; 3B-cont and 4A are the customers). **3A-cont brief issued
  2026-10-05** (`briefs/ch2-e3cont-batchA.md`, base `b75b6771`,
  bespoke in parallel with the design review; zero sanctioned
  admissions). §11 approved 2026-10-05 (11.1–11.3); **emitter spec layer
  landed** (5 sorried contracts + 2 transformers + 2 vocabulary defs;
  57/57 zero errors, 18 = 13 + 5 admissions exactly; regressions
  PASS) and the **emitter-infra audit pack prepared**
  (`audits/emitter-infra-{pack,bundle}.md`, 14 attachments; gate on
  zero blockers/majors, findings to
  `audits/emitter-infra-findings.md`). 3A-cont dispatched by the user
  (bespoke, independent); **integrated 2026-10-05 as a verified
  partial checkpoint** (69 `e3c*` privates banked — the full phase
  family for the split-search body; zero targets closed, zero new
  admissions; a maintainer base-hash erratum in the brief was caught
  by the agent and is recorded with its process correction). **Round 1: 0 blockers / 2 majors / 3 minors** (adequacy, not
  falseness); repairs landed (the two clean-call bridge contracts in
  `Loop.lean`, the 3B/4A mappings in §11b, the forwarding-host sketch
  correction, token/doc sweeps; 57/57 zero errors, 20 = 13 + 7
  admissions; full-print regressions PASS) and **round-2 pack
  prepared** (`audits/emitter-infra-r2-{pack,bundle}.md`, 31
  attachments incl. the evidence addendum both majors demanded).
  **Round 2: 0 blockers / 2 majors / 1 minor** (R1 3–5 closed;
  constructions validated); **round-3 repairs landed** (`0 < C.k` on
  both bridges — the zero-tape degeneracy; §11c's corrected 4A
  stage-to-seam mapping superseding §11b item 3; the §11a marker) and
  the **round-3 pack prepared** (36 attachments incl. the phase-4
  reaudit table and the A-cont `e3c*` provenance). **A-cont-2 brief issued
  2026-10-05** (`briefs/ch2-e3cont-batchA2.md`, base `d5ac2377`,
  rev-parse-verified; targets 2/4/5 only — 1/3/6 deferred to
  post-fill instantiation via `splitSolveWith`; ≈ 13 pts, zero
  sanctioned admissions, dispatches in parallel with the r3 audit).
  **EMITTER GATE CLOSED 2026-10-05** (round 3: 0/0/1 —
  `audits/emitter-infra-resolutions.md`; the attribution minor swept
  comment-only in the closing commit; binding fill/brief handoffs
  recorded). **Fill briefs issued 2026-10-05**
  (`briefs/emitter-fill-batch{L,P,W}.md`, base `d7b5b6f9`; L ≈ 17 pts
  bridges-then-emitLoop via the forwarding host, P ≈ 10 pts
  splitSolveWith under the gate disciplines, W 3 pts emit_run; zero
  sanctioned admissions each; the `e3c*` family as harvest template;
  completion drops the tree 20 → 13). **W integrated 2026-10-05**
  (`emit_run` proved, one private, Wrappers admission-free; spec
  7 → 6). **A-cont-2 integrated 2026-10-05**: the exponential
  reverse host closed (29 `a2*` privates; B2 host + native binary
  countdown); targets 4/5 escalated over a recorded maintainer
  scoping erratum (the Thm 2.22 route cites the excluded
  `EXP_subset_NEXP`) and move to **A-cont-3, now covering 1/6/3/4/5**
  post-`splitSolveWith`. **P integrated** (2/3: appendBit + unaryToken closed;
  `splitSolveWith` at the body wall with 83 privates banked incl.
  the whole-bank cleaner `emitterBankTM` + the conditional
  `emitterSplit_of_body`). **L integrated — COMPLETE 3/3**
  (`Loop.lean` admission-free, 5,713 lines, 119 privates; unified
  `emCallTM` bridge controller at the audited envelope; forwarding
  host + `emLoop_sum`). **The emitter layer stands at 6/7**; tree at
  **13 admissions** (12 campaign + `splitSolveWith`). **P2 brief issued 2026-10-05**
  (`briefs/emitter-fill-batchP2.md`, base `08884731`; the last
  contract against the predecessor's five-step plan, with the proved
  W/L layer now citable and L's `emCallTM` as the controller
  precedent; completion = emitter 7/7, tree 12). **P2 integrated 2026-10-05 — THE
  EMITTER LAYER IS COMPLETE (7/7, `Build/` admission-free)**: the
  split-search body closed via the proved install bridges in one
  round — the increment's thesis confirmed at first consumption; 68
  privates; tree at **12 admissions, all campaign**. **Fill-audit pack
  prepared 2026-10-05** (`audits/emitter-fill-{pack,bundle}.md`, 22
  attachments; whole-span attestation name-exact at 271 privates;
  gate on zero blockers/majors, findings to
  `audits/emitter-fill-findings.md`). **FILL GATE CLOSED 2026-10-05, PASS
  in one round (0/0/2/7)** — the emitter increment is complete and
  audited end to end (`audits/emitter-fill-resolutions.md`; both
  minors maintainer errata, swept). **The closing wave is dispatched-ready
  2026-10-05**: A-3 (`briefs/ch2-e3cont-batchA3.md`, 1→6→3→4→5 via
  `splitSolveWith`; zero sanctioned), 3B-cont
  (`briefs/ch2-e3cont-batchB.md`, the emit-loop rebuild under the
  r2-finding-5 schedule; zero sanctioned), 4A
  (`briefs/ch2-epoch4-batchA.md`, the summit under the embedded
  boundary table; one sanctioned root via 3B-cont for the SAT3
  pair; Astra distillation explicitly non-binding). **A-3 (run β of a
  recorded parallel-run incident; α discarded whole under logged
  criteria) and 3B-cont integrated 2026-10-05**: the padding cluster,
  `EXP_subset_NEXP`, and `SAT_reducible_SAT3` closed; tree at **6
  admissions** (`TAUTOLOGY_coNPComplete` + Hardness five); ledger
  **53/59**. **4A checkpoint integrated 2026-10-05**: 1/5 closed +
  77 privates banking the summit's whole pure layer (tableau,
  product encoding, chunk-exact serialization identity, quadratic
  ledger, oblivious normalization, certificate call, conditional
  emitter assembly); frontier = the packed-record producer, the
  round controller, equisatisfiability (four-step plan); tree at
  **5 admissions**; ledger **54/59**; Hardness 1,193 lines (new
  recorded exception). **4A-2 brief issued 2026-10-05**
  (`briefs/ch2-epoch4-batchA2.md`, base `f815da30`; the four-step
  plan binding; sanctioned root withdrawn — zero admissions
  sanctioned; producer = the checkpoint boundary).
  **4A-2 native-preparation checkpoint integrated 2026-10-06**
  (Codex `a4ca9302`): a verified partial *earlier* than the
  complete-producer boundary — **52 new proved privates** for the
  native preparation phase (the exact arithmetic header
  `clPrepHeader`, the all-false reference simulation
  `clRef*`/`clRefClock*` identified with the public
  `oblivious_schedule`, the in-place binary counter `clCount*`
  with carry/rewind re-proved on a silent absorbing machine, and
  the `clRefCount*` administrative frame); **no target closed,
  zero new admissions**, tree still at **5 admissions**, ledger
  **54/59** unchanged; Hardness.lean now 2,112 lines (size
  exception continues). Verification independently reproduced
  (checksums 25/25; freeze 919/0; byte-identical replay; 57/57
  sweep; whole-module traversal = 375 decls / 4 sorry roots; lint
  0 FAIL / 1 WARN; `audits/logs/e4A2-checkpoint-*`). **4A-3
  frontier**: the complete packed-record producer (trajectory +
  signed-position records + greatest-strictly-earlier last-visit
  search with a sequential-access ledger), genuine `initCfg`
  startup, the ordered emission controller under common budget
  `P` ≠ `T`, and the output-identity-then-equisatisfiability
  close. **4A-3 brief issued and the recording checkpoint
  integrated 2026-10-06** (Codex `9f1808a6`): **150 more proved
  privates** — the stored inclusive trajectory (`clRec_complete`,
  rows `0..T`, silence + `(4l+7)(T+1)²` cost + `2l(T+1)²` length),
  signed/clamped tracking, the cross-sum comparator, the charged
  sequential field reader — no target closed, zero new admissions,
  tree still at **5 admissions**, ledger **54/59**; Hardness.lean
  4,471 lines (exception continues); three-pass traversal 757
  decls / 4 roots / kernel surface = the five theorems
  (`audits/logs/e4A3-checkpoint-*`). **4A-4 frontier (still step 1,
  components complete — producer assembly is the minimum bar)**:
  header unpacking, row loader + greatest-strictly-earlier search
  with scratch resets and one charged ledger, the complete
  producer, then startup, the controller under `P` ≠ `T`, output
  identity, equisatisfiability. **4A-4 complete-producer checkpoint
  integrated 2026-10-06** (Codex `8e2d7ee1`): **step 1 closed** —
  `clPackedRecords_machine` proves the entire packed result (header +
  inclusive trajectory + full greatest-strictly-earlier visit table)
  from native input in one machine with total ledger `a*(|x|+1)^r`;
  176 new privates (455 total); no target closed, zero new
  admissions, tree still at **5 admissions**, ledger **54/59**;
  Hardness.lean 7,446 lines (exception continues; prime
  routine-layer retrofit target); three-pass traversal 1191 decls /
  4 roots / surface = five theorems
  (`audits/logs/e4A4-checkpoint-*`). **4A-5 frontier (the body,
  expected to close the gate)**: final install with the producer +
  genuine `initCfg` startup → ordered controller with common budget
  `P` (≠ `T`, ≠ producer ledger) → `clEmitter_of_body` +
  `clTableau_chunks` output identity → pure equisatisfiability;
  sanctioned checkpoint only at the proved output identity.
  **4A CLOSED 2026-10-06** (Codex `57507830`+`06ce95fa`): the
  five-target completion gate passes — Cook–Levin machine-checked
  end to end on the campaign's own audited model; `SAT_NPHard`,
  `SAT_NPComplete`, `SAT3_NPHard`, `SAT3_NPComplete` all empty
  roots at the standard triple; `Hardness.lean` admission-free
  (9,937 lines, 618 privates — THE prime routine-layer retrofit
  target); net deletions = exactly the four authorized `sorry`
  bodies; no-allowlist traversal 1550 decls / 0 sorryAx / surface =
  five theorems (`audits/logs/e4A5-closure-*`,
  `audits/programs/ch2-e4A5-ClosureAxioms.lean`). **Ledger 58/59;
  tree at 1 admission** (`TAUTOLOGY_coNPComplete`). **4B brief issued 2026-10-06**
  (`briefs/ch2-epoch4-batchB.md`, base `b133a3d4`; the docstring
  route binding; new DNF names binding; fallback-flips-sides and
  empty-term/empty-DNF pitfalls pinned; ≈ 7 pts; completion = the
  campaign tree admission-free). **4B CLOSED 2026-10-06** (Codex
  `9e9494aa`): `TAUTOLOGY_coNPComplete` via the audited dual route —
  the five definitional links + the `R(n)=0` one-round emit-loop
  transducer (28 privates, linear time); **ledger 59/59, the
  campaign tree at ZERO admissions** — the whole 65-module surface
  (11,436 kernel declarations) admission-free
  (`audits/logs/e4B-closure-*`,
  `audits/programs/ch2-e4B-ClosureAxioms.lean`). → the epoch-3/4
  audit pack — **GATE CLOSED 2026-10-06, PASS in round 3** (0 blockers /
  0 majors cumulative; findings/resolutions on record)
  (ride-alongs included: colleague's DNF adaptation, the parallel-run
  provenance, the discarded α hash, **colleague merge #2's 9-module
  private rewiring + the 57→65 order extension**) → E5 closure — **phase 1 complete 2026-10-06**
  (dedup 153 privates, drift attestation CLEAN, closure pack,
  zero-sorry sweep + traversal PASS); **phase 2 (blueprint
  increment) pending a user decision on the dep-graph refresh**
  (stale `dep_graph.json`; refresh needs the banned build —
  options: one-off artifact build in a throwaway worktree, or
  defer past the main merge) → the machine-routine layer +
  retrofit (recorded decisions).
  Subsumes 2C's
  `prefixTM`/`fixedPair` promotion requests. Dedup of superseded batch
  privates is an E5 closure task — **auditor-adopted live/dead guidance (epoch-3/4 round 1, finding 14)**: `clFill*` → producer path is LIVE; `clCertificateCall` and `clTrack_schedule` dead at source; `e3c*` mixed (`e3c_bits_injective` live); SAT's max-pass prefix live; dedup from a kernel-derived inventory, never by prefix or checkpoint label. Also queued for the retrofit: the 11 disclosed generated kernel artifacts (imported-definition equation lemmas + the private-structure `deriving` instance in SAT.lean). Mathlib TM2 rejected as substrate
  (evaluation recorded in the ch1 decision log).
* **Machine-routine layer (user decision 2026-10-06: build once
  chapter 2 is done, in the E5-closure/D7 window, before chapter 3).**
  Three pieces, sized by the A-chain's evidence (≈ half of the A2/A3
  deliveries' 202 native privates are hand-rebuilt universal routines;
  `emitterBank*`/`emitterP2*` relocation privately re-harvested three
  times; A3's proved costs `3|w|+3` copy / `2|w|+2` clear match the
  prior art's `3w+2`/`2w+2` to within one step):
  1. a generic **bank-embedding theorem** — a verified routine on its
     own small tape set runs on any selected tape subset of a `k`-tape
     machine, cost unchanged, all other tapes/heads framed (the public
     generic form of `emitterBank*`/`clBank*`/`clSlot*`);
  2. a generic **seam-composition lemma** — sequential composition of
     two controllers at a canonical `Cfg.ofWords` seam with first-return
     cuts and additive budgets (the generic form of the per-batch
     dispatch gluing);
  3. **catalog promotion** of transfer/clear/copy/compare/increment as
     public machines with exact costs, seeded from the already-audited
     A-chain privates (D6-style promotion, not new proof work).
  **Survey update 2026-10-06 (pre-§12, recorded ahead of the
  colleague meeting 2026-10-07)**: the colleague's ch6 merge already
  supplies the **function-level half** of this layer —
  `TuringMachine/CounterProg{,Run}` (goto programs over unary
  registers, compiled once into `FinTM`, `t` abstract steps ≤
  `t(2t+3)` machine steps, FP bridge), `ClassNP/Transducer` (Mealy
  machines as work-tape-free FinTMs in `|x|+1`), `ClassNP/
  PolyTimePairing`/`PClosure` (FP/`P` closure, built ON our audited
  catalog), `UnaryTape`. The §12 design must **consume, not
  duplicate** these; the remaining gap is the **config-level half**
  (bank-embedding, seam-composition at canonical `Cfg.ofWords`
  seams — the emitter r1 finding stands: function contracts cannot
  deliver clean-return seams) plus residual catalog promotions.
  Items for the meeting: colleague roadmap (more campaign-module
  rewiring?), `CounterProg` as general substrate vs. sibling
  module, `Build/*` ownership during the retrofit window, ch3/
  TimeHierarchy alignment. Citation duty now extends to the
  colleague's modules alongside lax-434930.
  Mechanism: a design addendum (`machine-library-design.md` §12) →
  statement gate → fills → audit, folded into the queued D7
  internal-namespace visibility proposal. **Citation discipline
  (binding, user guideline 2026-10-06): diligently cite the code this
  adapts — the design is inspired by Édouard Bonnet's
  `classical-complexity` (Lax Archive lax-434930), module
  `proofs/Lax434930Proofs/InclusionAux/TimeCompiler/` (StackProgram's
  `compile_correct`, StackRename's `rename_executes`/`executes_in_sum`,
  and the transfer/clear/copy/for/repeat routine catalog), commit
  `0c0840319318215fd7b36a9a822b81ce55cf6941`, Apache-2.0. The §12
  addendum, the affected module docstrings, and the blueprint entries
  must each carry this citation. Adapt design, never code: different
  toolchain (their Lean 4.33 / our 4.25) and machine model (TM2 keyed
  stacks vs FinTM tapes with heads); nothing is imported or
  transcribed, and the external files stay out of the repo.**
* **`Build/` catalog layout refactor toward per-theme files (queued;
  user decision 2026-10-08, §12 open decision 12.2).** The routine layer's
  new catalog rows land in a single `Build/Catalog.lean` (option (a)) to
  keep the audited `Primitives.lean` byte-identical; once the retrofit
  shrinks the `Build/` files, refactor the catalog toward the symmetrical
  per-theme layout (option (c): `Build/Catalog/{Transfer,Arith,…}.lean`),
  folded into the queued D7 split window. *Origin:
  `machine-library-design.md` §12, decision 12.2.*
* **Retrofit pass over chapters 1–2 with the routine layer (user
  decision 2026-10-06: queued as backlog, explicitly important — to be
  done at some point, not time-bound).** Once the machine-routine layer
  is audited, revisit the existing ch1 and ch2 formalizations —
  Cook–Levin included — and simplify them against it: replace the
  privately re-derived bank/relocation/dispatch/frame families
  (`emitterBank*`, `emitterP2*` relocation, `clBank*`/`clSlot*`,
  `clCopy*`/`clCmp*`/`clRead*`/`clCount*`, and their ch1 analogues in
  `Build/Primitives.lean`/`Build/Loop.lean`) with catalog citations and
  the two generic theorems. Expected effect: large private-count and
  line-count reductions in the five size-exception files, directly
  serving the deferred D7 splits. Statement freeze applies — public
  surfaces never change; every replacement batch goes through the
  standard sweep + traversal + audit protocol. Prerequisite: the
  machine-routine layer's gate is CLOSED.
  **Inventories + partition recorded 2026-10-09** (plan §4d; verbatim
  reports `audits/retrofit-inventory/`): realizable conservative scope
  ≈ −98 privates / −1,900 lines, dominated by dead code (`emitterBank*`
  itself is dead — delete, not port); the R1/R2/catalog-shaped glue is
  overwhelmingly LEAVE under the strict-simplification bar (monolithic
  hosts, loop back-edges, canonical-only rows, missing selected-tape
  exports). Batches RB1 (Loop) / RB2 (Primitives) / RB3 (Hardness),
  `Universal*` excluded; **integration by side branch + PR, user merges
  manually** (user rule 2026-10-09). Decisions D-R1 (Embed selected-tape
  exports, proposed to ride the §13 Z1 gate), D-R2 (Primitives ownership
  — option (a) deferred to 12.2c with feasibility proven; stretch (c)
  inside RB2), D-R3 (machine-agreement transfer lemma, deferred) are in
  §4d. The artifact-count note above corrects to **12** generated kernel
  artifacts, located in `Nondeterminism`/`EXP`/`SAT`, none in Hardness.
* **Audit-mandated fill-brief inheritances** (each brief must carry these
  verbatim from the cited records):
  - `NP_subset_EXP` enumerator: the contract-by-contract table —
    `audits/ch2-phase1-round3-findings.md` (via `…-resolutions.md`).
  - NTIME/Theorem-2.6 compilations: the simulator invariant tables and
    branch-correspondence contracts — `audits/ch2-phase2-findings.md`
    (note 3: no untimed composition or bare computability substitutions).
  - `TMSAT_mem_NP`: the `PolyBound` budget chain and the **new public
    quantitative bridge** for `timed_universal`'s constant — one simulator
    chosen before code and input, both success and timeout clauses, the
    suggested form `(3|α| + 14·canonizerTime(|α|) + 50)·(t+1)²` avoiding a
    `PolyBound` import into Chapter 1; Chapter-1 surface growth via the
    shared-file mechanism, flagged for its own audit —
    `audits/ch2-phase3-{findings,reaudit-findings,resolutions}.md`.
  - `TMSAT_NPHard`: exact-value emission case table and the explicit `T'`
    deadline formula (never majorize the certificate length) — same records.
  - Cook-Levin emitter (E4): the six-stage output-silence contract **and**
    the round-2 boundary-check table, the product snapshot encoding, and the
    exact serialization-length ledger (never constant-per-clause) —
    `audits/ch2-phase4-{findings,reaudit-findings,resolutions}.md`.
  - Locality fills: strict `s < t` in `prevVisit`; keep no-write and
    write-blank distinct (`some none` erases); writes on the halting
    transition count — phase-4 Derivation A.
  - `TAUTOLOGY_mem_coNP`: the DNF evaluation-congruence bridge as a private
    lemma — phase-4 round 1, note 6.
* **Chapter-2 blueprint increment** — at campaign closure (E5), per the
  Chapter-1 precedent (dep-graph merge, writer agents, validator).
* **P3.4 — Ladner's theorem (queued; user decision 2026-10-08: CH34-Q6
  core-late, moved to backlog at the P3.3 draft).** The last undrafted
  statement phase of the chapters-3-4 campaign
  (`AroraBarakChapters3-4Plan.md` §4): `Diagonalization/Ladner.lean` with
  `SAT_H` (SAT padded by the diagonal gaps of `H`), Ex 3.6(a) (`H`
  computable in polynomial time), the Claim of [AB09, Theorem 3.3]'s proof,
  Ex 3.6(b), and Theorem 3.3 itself (`P ≠ NP` gives an `NP`-intermediate
  language), ~6 sorried statements. Draft when the live rounds settle (the
  `Diagonalization.lean` facade unfreezes at the P3.2 close); it consumes
  the closed chapter-2 `SAT` surface and the received `polyTimeComputable`
  layer, and is independent of P3.3's code layer. *Origin:
  `AroraBarakChapters3-4Plan.md` §4 (P3.4 row), decision CH34-Q6.*
* **ARM extensions + colleague sync (moved to backlog 2026-10-09; user
  decision — outreach to Hydroxyi/Jason Dong initiated the same day).**
  The three proposed extensions to the co-owned `LogProg` tree
  (`AroraBarakChapters3-4Plan.md` §2.5), each a future infrastructure
  statement phase with its own audit gate once agreed: (1) a
  **nondeterministic ARM** — a `choose` instruction compiling to
  `FinNDTM` with the space theorem carried over (customers: `PATH ∈ NL`,
  Immerman-Szelepcsényi, Cor 4.21); (2) a **polynomial-width ARM
  variant** — `poly(n)`-bit registers for the `PSPACE`-level algorithms
  (`TQBF ∈ PSPACE`, `NP ⊆ PSPACE`, Savitch at polynomial level); (3) the
  **configuration codec as a program** — extends Hydroxyi's deterministic
  `ConfigCount` to NDTMs, adapting (citing, never vendoring) cslib's
  upstream `ConfigBound` design. Also on the sync agenda: `CounterProg`'s
  one-way input (the `2^O(S)` searches need indexed access or a rewind
  instruction), and the two citation-audit provenance questions, asked as
  questions (their `LogProg` compiler vs lax-434930's `TimeCompiler`;
  `ConfigCount.core` vs cslib `ConfigBound`'s `Cfg.core`). **Blocks fills
  only, never statements**: the machine-heavy P4.x fills named above plus
  the ARM interface statements deferred out of P4.1; every other fill
  epoch and the retrofit proceed. Returns to the plan on Hydroxyi's
  reply. *Origin: plan §2.5, §4a/§4b stage 1, CH34-Q2; the 2026-10-08
  citation-audit row.*

---

## 3. Deferred formalizations

### Chapter 1

* **Phase 5 (deliberately unscheduled; "a task for much later"):** the
  `O(T log T)` oblivious simulation ([AB09] §1.7 / Ex 1.6); the RAM-TM
  exercise (Ex 1.9); a fuller mathlib recursion-theory bridge beyond the
  `MathlibBridge` quarantine. *Origin: ch1 plan §5, decision of 2026-09-16.*
* **Waived model bridges** — revisit only if a downstream result ever needs
  a formal bridge: the append-only-output and start-marker-initialization
  conventions vs. [AB09]'s model (no read-write-output machine is
  formalized; no exact [AB09] step count is ever imported). *Origin: ch1
  plan §5 phase-2 notes; ch1 phase-2 audit findings 3/13.*
* **`Universal.lean` factoring** — 2831 lines (escalation recorded at
  epoch 4A): ~1100 lines are stopped-interpreter administrative copies
  forced by per-module `match` auxiliaries; the 4A report's three
  shared-lemma generalizations are the designated future factoring. Also
  CH1-Q2(a)'s promotion candidates. *Origin: ch1 decision log, epoch-4A row.*
* **Polynomial canonizer for a concrete scheme** (CH1-Q1(c) continued):
  Chapter 2's `TMSAT_mem_NP`/`TMSAT_NPComplete` now carry the hypothesis
  `PolyBound c.canonizerTime`; a combinator-built effective scheme with a
  *proved* polynomial canonizer would discharge the hypothesis for a
  concrete scheme and reconnect Q1(c). *Origin: ch2 phase-3 audit.*
* **Blueprint planner refinement** — writers flagged planner `\uses` edges
  not present in the cited proofs (reproduced verbatim per pipeline rules).
  *Origin: ch1 decision log, blueprint-extraction row.* **Ch2 increment
  instances (2026-10-06/07)**: `NPHard.polyTimeReducible` → `clLastRound`;
  `clA5Equisat` → `SAT_NPHard` (forward edge); `sat_comp_on_image` → `SAT`;
  `satHost_clean` → `SAT_reducible_SAT3` (forward edge);
  `choice_certificate_iff` → `capturedSummary`; `cont_split_bridge` →
  `contPairTM`; `goes_loop` → `run_pos_le`, `MOp`;
  `pairedVerifier_malformed` → `paddedVerifier`; `emit_run` → `redirectTM`;
  `taut_membership_of_verifier` → `TautSyntax`; `taut_machine_pair` →
  `tautSplit` (forward edge); `foldr_max_le_of_forall` →
  `falsifyingClause_eval_false`; `polyTimeComputable_of_linear` →
  `pairMapSnd`; `PolyTimeReducible.trans` → `mem_P_of_polyTimeReducible`;
  `acceptTM_halts_iff` → `prefixTM`. The forward edges (a helper "using" the theorem it serves)
  suggest the planner attributes by source-range adjacency or docstring
  mentions rather than by kernel dependency; the kernel walker used for the
  E5 dedup could supply exact edges.
* **Blueprint `\difficulty` calibration across writers** — parallel
  writers split on trivial structural inductions whose cases each close in
  one line: some rate them 3 (no real branching), others rubric-literal 4
  (any induction or case split). Observed in the ch2 increment (NP,
  Snapshot, CNFEncoding at 3; Nondeterministic, CounterProg at 4). The
  dataset would benefit from one normalization pass, which is mechanically
  detectable from the proof source; or tighten the rubric text in the
  writer agent definition. *Origin: blueprint-writer reports, ch2
  increment parts 2–3.*
* **For the colleague: `ClassNP/PClosure.lean` docstring/statement gap** —
  the `lenEq_mem_P`/`lenLe_mem_P` docstrings speak of *pairs*, but the
  languages range over all bit strings, the total projections sending a
  non-pair to the empty word (so every non-pair lies in the `lenEq`
  language). The statements are fine; the docstrings undersell their
  domain. The blueprint documents the Lean behavior. *Origin:
  blueprint-writer report, ch2 increment part 4.*
* **Blueprint-writer process fix: require the per-entry strict check** —
  in the ch2 increment, writers that ran `statement_quality.py` /
  `dataset_hygiene.py` from the command line were grading the dataset
  *cache*, not their chapter, and every one of the 178 strict-rubric
  flags came from exactly those five writers (SAT, Primitives, EXP, CoNP,
  PClosure); writers that imported `check(..., strict=True)` and ran it
  per entry produced zero. Fix: state the per-entry function-call check
  as a hard requirement in `.claude/agents/blueprint-writer.md` (and
  ideally add a `--chapter` mode to the scripts). The orchestrator-side
  uniform pass used here (`build_dataset.parse_blueprint` + both checks,
  names demangled via `PRIVATE_RE`) could also become a `/blueprint-
  extract` step. *Origin: ch2 increment, 2026-10-07.*
* **Stale module docstring: `Build/Primitives.lean`** — still says every
  theorem below is sorried; the emitter fill gate closed every one of them.
  Comment-only fix, eligible for the next comment-only sweep (comment-
  stripped byte-identity check per precedent). Same sweep: the
  `emitterP2EraseCfg` docstring says the input stays "at its origin", but
  the definition places the head at position 1 (the first input cell) —
  the blueprint now states the Lean behavior. *Origin: blueprint-writer
  reports, ch2 increment parts 1 and 6.*

### Chapters 2-3

* **§2.4 web of reductions** (`INDSET`, `0/1 IPROG`, `dHAMPATH`, exercise
  problems) — each needs a graph/arithmetic encoding surface; the legacy
  `Complexity/NPReductions/*` files may eventually be **retargeted** as the
  structure-level halves (see §5). *Origin: ch2 plan §1.*
* **§2.5 decision-versus-search** (Theorem 2.18). *Origin: ch2 plan §1.*
* **Parsimonious and Levin reductions** ([AB09] §2.3.6). *Origin: ch2 plan §1.*
* **Ex 2.6, the universal NDTM** — Chapter 3's tool. *Origin: ch2 plan §1.*
* **Ex 2.30, Berman's theorem.** *Origin: ch2 plan §1.*
* **General Boolean formulas** — `TAUTOLOGY` is deliberately stated on the
  documented DNF fragment; a general-formula carrier (AST, evaluation,
  serialization) is new work, and any future general `TAUTOLOGY` must not be
  silently identified with the fragment. *Origin: ch2 phase-3/4 audits.*
* **`MathlibBridge` poly-time upgrade** (open lever): `bridgeTM` costs O(1)
  native steps per TM2 operation, so a Mathlib `TM2ComputableInPolyTime`
  certificate would transfer. (The Chapter-6 bridges were built on native
  machines without it; see §3.)
  *Origin: ch2 plan decision log ("revisit at phase 3" — still open).*
* **Oracle complexity classes** (Chapter 3): `Oracle.lean` has the raw model
  and both lockstep embeddings, audited; the class layer, the
  persistent-vs-auto-erased query-tape statement (polynomial overhead only —
  constant overhead provably impossible), and relativization (Baker-Gill-
  Solovay) are future Chapter-3 work. *Origin: ch1 plan §5 phase-2 notes;
  session assessment 2026-09-18.*

### Chapter 6 (Arora–Barak §§6.1–6.5): what is proved, and what remains

The machine-facing Chapter-6 bridge theorems this section used to list are all
**proved, sorry-free** (headline `#print axioms`: `propext`, `Classical.choice`,
`Quot.sound` only), over the book's DAG model `BoolCircuit.DAGCircuit`:

* Thm 6.6 `P ⊆ P/poly` — `Complexity.P_subset_PPoly` (oblivious tableau,
  `CircuitComplexity/PSubsetPPoly*.lean`); `P ⊊ P/poly` (p. 110) —
  `Complexity.P_ssubset_PPoly`, with the machine-model `UHALT`
  (`Complexity.UHALT_not_mem_P`, `UHaltMachine.lean`).
* Lem 6.10 / 6.11 — `BoolCircuit.dagCktSatLang_NPComplete`,
  `BoolCircuit.dagCktSatLang_polyTimeReducible_SAT3`, and Cook–Levin via circuits
  `Complexity.SAT3_NPHard_viaCircuits` (the p. 111 alternative proof); CKT-SAT `∈ NP` is
  `BoolCircuit.dagCktSatLang_mem_NP`, circuit evaluation `BoolCircuit.CVAL_mem_P`.
* Remark 6.7, Thm 6.13 — `Complexity.tabFamily_isPUniform`,
  `Language.mem_P_iff_exists_isPUniform`; Def 6.14, Thm 6.15 and the logspace half of
  Remark 6.7 — `Complexity.tabFamily_isLogspaceUniform`,
  `Language.mem_P_iff_exists_isLogspaceUniform`.
* Def 6.16, Ex 6.17, Thm 6.18 — `Complexity.DTIMEAdvice`,
  `Complexity.mem_PAdvicePoly_of_le_allOnes` (with the named `UHALT` instances
  `Complexity.UHALT_mem_DTIMEAdvice_one`, `Complexity.UHALT_mem_PAdvicePoly`),
  `Complexity.PPoly_eq_PAdvicePoly`, and the book's advice length `n^d` literally:
  `Complexity.PPoly_eq_iUnion_DTIMEAdvice_pow` (`P/poly = ⋃ DTIME(n^c + 1)/n^d`,
  `PAdviceSubsetPPoly.lean`). The time `n^c + 1` is forced, not cosmetic: the literal
  `DTIME(n^c)/a` is empty for `c ≥ 1` (`Complexity.DTIMEAdvice_pow_eq_empty`, zero steps
  on the empty input), so the literal union collapses to constant time
  (`Complexity.iUnion_DTIMEAdvice_pow_eq`); also
  `DTIME(T)/0 = DTIME(T)` for `T(n) ≥ n + 1` (`Complexity.DTIMEAdvice_zero_eq_DTIME`)
  and `⋃_c DTIME(n^c + 1)/0 = P` (`Complexity.iUnion_DTIMEAdvice_zero_eq_P`).
* Thm 6.19 Karp–Lipton — `Complexity.PH_eq_SigmaP_two_of_NP_subset_PPoly`; Thm 6.20
  Meyer — `Complexity.EXP_eq_SigmaP_two_of_EXP_subset_PPoly`, and the p. 115 corollary
  `Complexity.not_EXP_subset_PPoly_of_P_eq_NP`.
* Thm 6.21 — `BoolCircuit.exists_hard_function_dag` (book bound `2ⁿ/(10n)`), with the
  p. 115 probabilistic form `BoolCircuit.prob_computableDAG_shannon_le`, proved by the
  book's steps: `BoolCircuit.prob_eval_eq_apply` (`Pr[C(x) = f(x)] = 1/2`),
  `BoolCircuit.prob_computes` / `prob_computes_eq_prod` (`Pr[C computes f] = 2^{-2ⁿ}`, the
  product of the per-input probabilities) and the union bound `BoolCircuit.prob_computableDAG_le_count`
  (`ShannonProbabilistic.lean`).
* p. 108 circuit remarks — Lupanov `O(2ⁿ/n)` (`BoolCircuit.exists_dagCircuit_faninTwo_size_le_div`,
  `Lupanov.lean`); fan-out two (`DAGCircuit.exists_fanoutTwo`, `FanOut.lean`), including
  `¬¬v` buffers under the literal fan-in-exactly-two convention
  (`DAGCircuit.exists_fanoutTwo_notNot`, `5S`; `DAGCircuit.IsStrict.exists_fanoutTwo`,
  `20S`; `StrictFanOut.lean`); the literal Def 6.1 (`DAGCircuit.IsStrict`,
  `Language.inPPoly_iff_inStrictPPoly`); formulas as fan-out-one circuits, both ways
  (`TreeCircuit.toDAG_fanout_le_one`, `DAGCircuit.exists_treeCircuit_of_fanout_le_one`,
  `FormulaFanOut.lean`).
* Def 6.5's literal `⋃_c SIZE(n^c)` — empty (`Language.not_inSIZE_pow`); `P/poly` is the
  literal bound from length 2 on (`Language.inPPoly_iff_eventually`, `PPoly.lean`).

Remaining Chapter-6 items (each documented as a divergence in its file):

* **Thm 6.22, the size hierarchy over the book's `SIZE`** — only the tree-circuit
  analogue exists (`BoolCircuit.treeSize_ssubset`, `Hierarchy.lean`); the DAG version
  needs a DAG-native padding/counting argument on top of `exists_hard_function_dag`.
* **Tree-circuit CKT-SAT** (`Encoding.lean`, `CircuitSat.lean`) carries no `≤ₚ` claim —
  only equisatisfiability and a clause count; the book's Lem 6.11 is the DAG version
  above.
* The `O(T log T)` oblivious simulation (Remark 1.7) is Chapter 1's Phase 5 above; the
  circuits of `P ⊆ P/poly` are quadratic instead, which suffices for every Chapter-6 use.

---

## 4. Decisions pending (user)

* **Chapter-6 integration** — the Chapter-6 theorem surface is complete up to the
  items listed in §3 (Chapter 6); resolved in part: ch6 was merged into the
  campaign branch (`a2a2728b`), and the circuit nomenclature pass agreed
  with the ch6 authors landed 2026-10-01 in three commits: `HasLogDepth`
  → `HasPolylogDepth`; the `ACP` namespace unbundled (generic circuit
  material → `BoolCircuit`, the Razborov–Smolensky chain →
  `RazborovSmolensky`, `AC_GateOps` → `BoolCircuit.stdGateOps`);
  `FeedForwardCircuit.lean` relocated to
  `Complexity/CircuitComplexity/FeedForward.lean` (since renamed
  `LayeredCircuit.lean`), so `Complexity` no
  longer imports from `BooleanAnalysis` (verification:
  `scripts/circuit_module_order.txt`, the 23-module dependency sweep).
  Still open: their `Formulas.lean` defines `Literal`/`Term`/`DNF`/`CNF`
  at the **root namespace** (policy §1 leak; future ambiguity against
  `Std.Sat.CNF`/`Std.Sat.Literal`) — namespace choice deliberately
  deferred (user: `BoolCircuit` is not the right home for formulas);
  three CNF ecosystems coexist (their width-indexed `CNF n`, legacy
  `NPReductions.CNFFormula V`, the audited `Std.Sat.CNF ℕ`) with three
  SAT→3SAT artifacts; `UHalt.lean` introduces a **second computability
  framework** (Mathlib `ComputablePred` vs. the campaign's quarantine and
  its own `HALT_not_computable`) — the machine-model counterpart
  `UHaltMachine.lean` (`Complexity.UHALT_not_mem_P`) now carries `P ⊊ P/poly`,
  so `UHalt.lean` is a parallel statement, not a dependency; the merged circuit
  surface **passed the external audit protocol**
  2026-10-02 (three rounds, 0 blockers throughout;
  `audits/ch6-circuits-resolutions.md`, CLOSED) — campaign statements may
  cite its definitions, subject to the recorded divergences (the audit's
  interface notes 12–15 in `audits/ch6-circuits-findings.md` were followed by the
  bridge theorems now listed in §3). The dangling `ch6/PLAN.md` references were repointed
  here in the round-1 repairs. Loose ends for the colleagues:
  `Basic.lean` at 691 lines (> 600 target); and the audit's sweep logs
  show the **LMN tree is not sorry-free** (five `sorry` warnings across
  `CircuitCompression`, `IterativeReduction`, `Depth3Switching`,
  `CircuitTreeManip`) — outside the audited surface, flagged for its
  authors.
* **Fill-campaign start** (§2) — on hold by the same instruction.
* **Disposition of the three §1 questions** — CH1-Q1, CH1-Q2, CH2-Q1.
* **`TCSlib.Tactics` blueprint exclusion** — 92 metaprogramming-scaffolding
  declarations deliberately excluded from the dataset; user may override.
  *Origin: ch1 blueprint-extraction row.*
* **Fate of `AroraBarakChapter1Plan.md` at merge** — graduate to `docs/` vs.
  superseded by the blueprint. *Origin: ch1 decision log (final row).*

---

## 5. Repository housekeeping

* **Legacy `Complexity/NPReductions/*`**: 14 pre-existing style-lint FAILs
  (missing docstrings/References), outside the campaign surface; eventual
  fate coupled to the §3 retargeting idea. The ch6 branch adds (clean,
  additive) counting lemmas to `SATTo3SAT.lean`.
* **Dependabot**: 88 alerts on the repository default branch (2 critical,
  16 high) — repo-level, unrelated to this branch's content.
* **`AGENTS.md` / `.claude/CLAUDE.md`** partially superseded by campaign
  practice (`workflow.md` §7 records the boundary): the `lean_proof/`-based
  flow and the LeanInfoView-only verification guidance predate the gate
  script; align or annotate eventually.
* **`audits/TEMPLATE.md`** predates the evolved pack format (attestation
  evidence separation, bundle conventions); refresh before the next fresh
  campaign starts from it.
* **Statements-only package split (idea; no near-term action):** a
  `concepts`/`proofs`-style two-package layout — frozen statement surfaces
  compiled without proof code, importable by downstream chapters — would
  mechanize the statement-freeze discipline the campaign currently enforces
  by protocol (statement gates, briefs, audit packs). Observed in external
  prior art: Lax Archive lax-429075/lax-434930 (Bonnet, Cook–Levin on Lean
  4.33; examined 2026-10-05, scratchpad-only, Apache-2.0, non-binding, never
  imported), where each claimed result is an `axiom` in a statements package
  and a platform replay checks the proof network closes. Composes with the
  §2 D7 internal-namespace visibility proposal; revisit no earlier than
  that proposal, if at all. *Origin: prior-art comparison, 2026-10-05.*
* **`HANDOFF.md`** — the have→lemma extractor campaign's own tracking
  document; deliberately *not* absorbed here.
