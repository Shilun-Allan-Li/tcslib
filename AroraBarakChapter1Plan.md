# Formalization Plan: Arora-Barak Chapter 1

**Branch:** `complexity/arora-barak-ch1` · **Governing standards:** [`policy.md`](policy.md)

This document is the working plan for formalizing Chapter 1 of Arora & Barak,
*Computational Complexity: A Modern Approach* (CUP 2009) — "The computational model — and
why it doesn't matter" (book pages 9–37) — in TCSlib. It records the foundation decision,
the architecture that keeps the model robust to variations (oracles, nondeterminism), the
module layout, and the phasing. Source tag throughout the development: `[AB09]`.

## 1. Scope: what Chapter 1 contains

| Section | Content | In scope |
|---|---|---|
| §1.2 | k-tape TM `(Γ, Q, δ)`: read-only input tape, work tapes, output tape (read-write in [AB09]; append-only write-only in our model — a variation [AB09, p. 19] itself sanctions, declared in `DTIME.lean`); start configuration; halting; Example 1.1 (palindromes in 3n steps) | Yes |
| §1.3 | Computing `f` in time `T(n)` (Def 1.3); time-constructibility; Claim 1.5 (alphabet reduction, `4 log|Γ|` slowdown); Claim 1.6 (k tapes → 1 tape, `5kT²`); Remark 1.7 (oblivious TMs); Claim 1.8 (bidirectional → unidirectional, `4T`) | Yes (oblivious: statement only at first) |
| §1.4 | Machines as strings: every string decodes to some TM, every TM has infinitely many encodings; universal TM; Theorem 1.9 (universal simulation), relaxed `O(T²)` version; time-bounded universal TM | Yes |
| §1.5 | Uncomputability: `UC` via diagonalization (Thm 1.10); `HALT` via reduction (Thm 1.11); §1.5.2 Gödel discussion | Thms 1.10–1.11 yes; Gödel material is prose — out of scope |
| §1.6 | `DTIME(T(n))` (Def 1.12, with constant absorption), `P` (Def 1.13), examples | Yes |
| §1.7 | Hennie-Stearns `O(T log T)` universal simulation (amortized zone argument) | Stretch goal, off the critical path |

Additionally in scope, ahead of the book's own ordering: the **oracle TM** definition
(the book defers it to §3.4). We pull it forward to validate that the architecture supports
model variations before the expensive theorems are built on it.

## 2. Foundation decision

**Decision: vendor cslib's multi-tape TM model; do not build on Mathlib's TMs; do not take
cslib as a dependency.** Findings behind this (surveyed Sept 2026, against our pinned
mathlib `029db123ddaa`, toolchain v4.25.0):

- **Mathlib** is a computability library, not a complexity library. It has no multi-tape TM
  (TM0/TM1 are single-tape, TM2 is a stack machine); its model-simulation theorems carry no
  time bounds; `TM2ComputableInPolyTime` is a stub whose only instance is `id`. Building
  Arora-Barak on it means fighting the design. What we do reuse: `Language`,
  `Turing.FinEncoding`, and (later, as an optional bridge) the recursion-theory stack
  (`Nat.Partrec`, `Halting`/Rice, `Reduce`, `RecursiveIn`).
- **cslib** (github.com/leanprover/cslib, `Cslib/Computability/Machines/Turing/MultiTape/`,
  Apache-2.0) has an Arora-Barak-style `MultiTapeTM` (its write-only output tape is an
  [AB09, p. 19]-sanctioned variation of the book's read-write one): read-only input
  tape, k work tapes, explicit time and space semantics, a nondeterministic
  variant, and configuration-count bounds — actively developed, with a complexity roadmap
  (issue #611) that plans oracles as a wrapper over any model.
- **Why vendor rather than depend:** cslib targets Lean v4.35.0-rc1 with the new module
  system; TCSlib is pinned to v4.25.0 and the PFR dependency chains us there. The vendored
  surface is small (~1,400 lines). We stay structurally aligned with upstream so we can
  migrate to a real dependency at the next toolchain bump, and upstream anything we prove
  that they lack (universal TM, robustness claims).
- Vendored files follow `policy.md` §2: original copyright headers preserved, source commit
  recorded, local modifications listed (expected: de-module-system syntax, import-path
  ports to v4.25 mathlib).

Reference mechanization to mine for proof architecture: the Isabelle AFP entry
`Cook_Levin` (Balbach) — the only completed Arora-Barak-faithful development. Its lemma
decomposition, especially for TM composition and the universal machine, transfers.

## 3. Architecture

### 3.1 The Action/apply split (model variations)

cslib's configuration layer mentions no machine: a step is an **`Action`** (input-head
move, per-work-tape write/move, optional output symbol, successor state) plus
**`Action.apply`** (its effect on a configuration). A *machine* is then just the thing
that **chooses** the action from the current state and read symbols. Every model twist is a
different chooser over the same configurations, the same `apply`, and the same run/time/
space measures:

| Model | Chooser |
|---|---|
| Deterministic TM (Ch. 1) | function `State × reads → Action` |
| Nondeterministic TM (Ch. 2) | relation over actions |
| Oracle TM (§3.4, Definition 3.4, pulled forward) | function consulting `O : Language _` via query tape and `q_query`/`q_yes`/`q_no` states (pairwise distinct: `OracleTM.WellFormed`) |
| Probabilistic TM (Ch. 7, future) | two transition functions + coin |

Because `DTIME`-style definitions are stated over the shared run layer, `P`, `Pᴼ`, and
later `NP`/`BPP` are instances of one pattern, not parallel developments. Phase 1 locks
the design with sanity theorems in both directions: a plain machine embeds as an oracle
machine whose runs are in lockstep with the original under *every* oracle
(`ofMultiTapeTM`), and conversely an oracle machine run with the empty oracle is
eliminated into a plain machine in exact lockstep (`plainEmptyOracle`).

### 3.2 Finiteness: raw layer vs. bundled layer

Finiteness of `Γ` and `Q` is mathematically non-negotiable: with infinite states, δ can
memorize the input and decide any language in linear time (P would collapse to all
languages), and `⌞M⌟` has no finite representation. The design question is only *where*
the hypothesis lives:

- **Raw layer** (`MultiTapeTM k Γ Q`, parametric types, no finiteness): configurations,
  `step`, runs, time/space counting, and simulation *constructions*. Deferring finiteness
  here keeps semantics lemmas clean and lets compound state types (`Q × Γᵏ`, `Option Q`,
  sums) arise without instance-threading; finiteness of a constructed machine is an
  afterthought (`inferInstance`). This follows both cslib and mathlib TM0/TM1 practice.
- **Bundled layer** (`FinTM Symbol`: a raw machine bundled with `Fintype`/`DecidableEq`
  instances for its *state* type — analogous to mathlib's `FinTM2`): **all headline
  definitions and theorems** — `DTIME`, `P`, `⌞M⌟`, Theorem 1.9, oracle classes — are
  stated exclusively over the bundled layer, so a finiteness hypothesis can never be
  forgotten. The alphabet is *not* bundled: it stays an explicit parameter, fixed to
  `Bool` by the headline classes; results over a general `Symbol` (e.g. machine
  encodings) take `[Fintype Symbol]`/`[DecidableEq Symbol]` at their statements, and
  oracle complexity classes (Ch. 3) will introduce a finite oracle-machine bundle
  before they are defined. Encoding needs `Fintype`/`DecidableEq` as *data* (δ's table
  must be enumerated), which is why the bundle carries instances rather than `Finite`
  propositions.

Per `policy.md` §1 (layering), the raw layer is internal plumbing; the bundled layer is
the textbook object.

### 3.3 Conventions

- **Strings/languages:** `{0,1}*` as in the book; languages via mathlib's `Language`.
- **Namespaces:** `Turing` for the vendored core (minimizes diff against upstream; no
  clashes with mathlib's `Turing.*` at our pin), `Complexity` for classes and
  uncomputability. Revisit only if a clash appears.
- **NP/NTM:** strictly Chapter 1 here. cslib's nondeterministic file is in the vendorable
  set but lands with the Chapter 2 effort.

## 4. Module layout

Per `policy.md` §1: facades, 150–600-line files, precise imports, `TCSlib.lean` exports.

```
TCSlib/Complexity/TuringMachine.lean          -- facade + module docstring
TCSlib/Complexity/TuringMachine/
  Configuration.lean      -- Cfg, Action, Action.apply, space measure   [vendored]
  Deterministic.lean      -- MultiTapeTM, run, ComputesInTime(AndSpace) [vendored]
  Finite.lean             -- bundled FinTM layer (§3.2)
  Oracle.lean             -- oracle wrapper over the same Cfg/Action layer
  Composition.lean        -- sequential composition, basic combinators
  Robustness/
    AlphabetReduction.lean  -- [AB09, Claim 1.5]
    SingleTape.lean         -- [AB09, Claim 1.6]
    Bidirectional.lean      -- [AB09, Claim 1.8]
    Oblivious.lean          -- [AB09, Remark 1.7] (statement; proof deferred)
  Encoding.lean           -- ⌞M⌟ : TM ↔ string; totality + padding [AB09, §1.4]
  Universal.lean          -- [AB09, Thm 1.9] relaxed O(T²) + timed variant
  UniversalEfficient.lean -- [AB09, §1.7] Hennie-Stearns O(T log T)  [stretch]
TCSlib/Complexity/Uncomputability.lean        -- facade
TCSlib/Complexity/Uncomputability/
  Computable.lean         -- computable functions, no time bound [AB09, §1.4-§1.5]
  Diagonalization.lean    -- UC, [AB09, Thm 1.10]
  Halting.lean            -- HALT, [AB09, Thm 1.11]
  MathlibBridge.lean      -- link to Nat.Partrec / Rice  [optional, later]
TCSlib/Complexity/ClassP.lean                 -- facade
TCSlib/Complexity/ClassP/
  DTIME.lean              -- decides, DTIME with constant absorption [AB09, Def 1.12]
  TimeConstructible.lean  -- time-constructibility [AB09, §1.3]
  P.lean                  -- P, closure basics, model-invariance [AB09, Def 1.13]
  Examples.lean           -- PAL ∈ DTIME(n+1) [AB09, Ex 1.1]; selected Ex 1.14
```

## 5. Phasing

Each phase lands first as a **compiling sorry-skeleton** (the GraphTheory/Core precedent):
statements are the contract, proofs fill in via the sorry-ladder workflow. Per `policy.md`
§3, proof sketches are written at skeleton time — each `sorry` corresponds to a named
sketch step. After each phase compiles: dep-graph rebuild, `/blueprint-extract`,
`blueprint_validate.py --strict`, `dataset_hygiene.py --strict`. The blueprint is
**late-bound**: extraction runs only at phase boundaries, and no blueprint LaTeX is
written by hand ahead of the Lean.

### Audit protocol (between phases)

Right after a phase's skeleton lands — statements frozen, proofs mostly `sorry` — an
**external audit** runs before the next phase begins: an LLM from a different vendor, in
a fresh context, reviews the phase's trusted surface (definitions, theorem statements,
remaining sorries) against the book, adversarially. Statement bugs are the dominant
failure mode of formalization (Lean already checks proofs) and are cheapest to fix at
this moment. Mechanics: instantiate `audits/TEMPLATE.md` as `audits/phaseN-pack.md`, hand
it plus the listed files to the auditor, record results in `audits/phaseN-findings.md`;
every finding is fixed or explicitly waived before the next phase starts. An optional
light second pass when a phase's proofs complete diffs the statements for quiet
weakening. Audits complement, not replace, in-Lean sanity theorems, which are the
machine-checked and permanent form of the same checks.

1. **Core model + classes.** Port the two vendored files to v4.25; `Finite.lean`;
   `ComputesInTime`, `decides`, `DTIME`, `P`; the oracle wrapper + trivial-oracle sanity
   theorem; PAL as an end-to-end usability check. *This phase alone unblocks future
   chapters (NP needs only these definitions).*
2. **Robustness.** Claims 1.5, 1.6, 1.8; `Composition.lean` combinators; corollary that P
   is invariant under the model tweaks. First real machine-construction proofs — builds
   the simulation vocabulary everything later reuses. The convention obligations
   recorded by the phase-1 audit are dispositioned per the phase-2 audit (findings 3
   and 13): the append-only-output and initialization bridges are **waived** (no
   read-write-output model is formalized; no exact step count is ever imported from
   [AB09]), to be revisited only if a downstream result needs a formal bridge; the
   persistent vs auto-erased query-tape statement (polynomial overhead only — constant
   overhead provably impossible) moves to the Chapter 3 oracle-class work.
3. **Encodings + universal machine.** `⌞M⌟` with totality and padding lemmas; Theorem 1.9
   in the relaxed `O(T²)` form (U simulates the one-work-tape *binary* normal form from
   phase 2 — `FinTM Bool`, i.e. three tape symbols counting blank; if the construction
   wants [AB09]'s four-symbol alphabet, that is an additional named embedding step) and
   the time-bounded variant.
4. **Uncomputability.** Thm 1.10 (needs only encoding + semantics; the diagonalization is
   short); Thm 1.11 (needs composition + the universal machine). Proof blueprints for
   both are in `audits/phase3-reaudit-findings.md`, Argument F. Scope additionally
   includes the API pieces that audit identified: a **guarded/partial composition (or
   guarded-simulation) lemma** with buffered intermediate output — the total-function
   `computesFunInTime_comp` cannot take the partial evaluator as a component — and,
   where a proof needs a globally chosen evaluator or a semantically identified code,
   an explicitly stated named-evaluator interface.
5. **Stretch — explicitly off the critical path, and deferred to a much later
   effort.** §1.7's `O(T log T)` simulation; oblivious TMs; the RAM-TM exercise
   (Ex 1.9); the mathlib recursion-theory bridge. **Not scheduled** (decision of
   2026-09-16): phase 5 is a task for much later — it is not part of the current
   push, no audit pack will be prepared for it, and it is revisited only after the
   phase-1-4 fill campaign completes. Chapter 1's critical path *ends with phase 4*.

### Fill campaign (epochs and batches)

With all four phase gates closed, the remaining critical-path work is filling the
21 audited-true sorries. The campaign runs in **epochs** — sequential, with an
audit round at each epoch boundary — each consisting of **batches** run in
parallel, one agent per batch, with disjoint file ownership. Difficulty points
(1-15 scale) are planning estimates. Agents work in the cloud from the
self-contained briefs in `briefs/`, branching off `complexity/arora-barak-ch1`
and PRing back into it (`github.com/Shilun-Allan-Li/tcslib`). Verification is
`scripts/lean_check_tree.sh` over `scripts/ab_ch1_module_order.txt` (direct
`lean`; `lake build` stays banned).

| Epoch | Batch | Contents (points) | Owned files |
|---|---|---|---|
| **1** | 1A | `Computes.exists_computesFunInTime` (2), `UC_not_computable` (2), `universal_quadratic` (2), `UC_computable_of_HALT_computable` (3) — the assembly/integration tests | `Uncomputability/{Computable,Diagonalization,Halting}.lean`, `Universal.lean` (quadratic only) |
| 1 | 1B | `computesFunInTime_const` (2), `computesFunInTime_ifEq` (3), `exists_cond` (6) | `Composition.lean` |
| 1 | 1C | `pairEncode_injective` (3), `computesFunInTime_pairEncode_diag` (4), `exists_codeTM` (5) | `Encoding.lean` |
| 1 | 1D | `PAL_mem_DTIME_linear` (4), `timeConstructible_id` (5) | `Examples.lean`, `TimeConstructible.lean` |
| **2** | 2A | `exists_comp_partial` (8) then `computesFunInTime_comp` (7) — shared infrastructure, sequential within the batch | `Composition.lean`, `Simulation.lean` |
| 2 | 2B | `one_work_tape` (12) | `Robustness/SingleTape.lean` |
| 2 | 2C | `nonnegative_heads` (7), `alphabet_reduction` (8) | `Robustness/{Bidirectional,AlphabetReduction}.lean` |
| **3** | 3A | `exists_effectiveMachineCode` (13) | `Encoding.lean` |
| 3 | 3B | `universal` (15) | `Universal.lean` |
| 3 | 3C | `oblivious_of_mem_DTIME` (12) — droppable per the phase-5 deferral without reopening any gate | `Robustness/Oblivious.lean` |
| **4** | 4A | `timed_universal` (10), reusing `universal`'s infrastructure | `Universal.lean` |
| 4 | — | Closure: zero-sorry sweep with build evidence (phase-4 finding 8), final drift attestation across all gates, fill-round audit pack, `/blueprint-extract` | — |

Epoch loads: ≈ 41 / 42 / 40 / 10 points. Rationale: epoch 1 maximizes
risk-retirement per point (the assemblies machine-check that the phase-3/4
interfaces compose; the machine batches validate the invariant pattern at small
scale), epoch 2 retires the two biggest technique risks (guarded composition
with buffered output; sweep-based simulation), epoch 3 climbs the summit with
every needed technique already precedented in-repo, epoch 4 is wind-down.

**Ground rules** (binding on every batch; full text in each brief): (1)
exclusive file ownership — helpers live `private` in owned files; lemmas
belonging in shared files are *requested* via the PR description and added
serially at epoch merge, flagged for audit; (2) statement freeze — audited
declarations are never renamed, re-signatured, or re-stated by a fill PR; a
target that looks unprovable as stated is an *escalation*, reported in the PR
with the obstruction, never "fixed" inline; (3) verification per batch via the
check script, zero `error:` lines, sorry warnings only at documented
out-of-scope items; (4) at epoch merge the maintainer re-runs the full sweep,
produces the comment-stripped drift attestation, and prepares the epoch's
fill-round audit pack with elaboration evidence.

**Blueprint reference ingestion:** ingest Chapter 1 as
`blueprint/src/references/arora-barak-ch01-*.md` (raw/clean pair, ch. 13 shows the format)
so `\statementsource`/`\proofsource` citations are possible once proofmatch runs are
approved.

### Open design questions (human review required)

These are flagged for a **human** auditor/maintainer decision — the LLM audit
rounds verify correctness, but these are matters of architectural taste and
trust-surface policy that should not be closed by an automated gate.

1. **The 3A Mathlib-computability bridge** (epoch 3, batch A;
   `Encoding.lean`, `exists_effectiveMachineCode`). The audited docstring
   sketch called for the canonizer machine to be **hand-assembled from this
   repository's composition combinators** ("its construction uses the
   composition combinators", optionally with a polynomial `canonizerTime`).
   The delivered proof instead (i) proves the canonization *function*
   primitive recursive, (ii) compiles it through **Mathlib's verified
   recursion-theory pipeline** (`ToPartrec.Code.exists_code` →
   `PartrecToTM2.tr_eval`), (iii) simulates the resulting TM2 stack machine
   in our model with a bespoke private `bridgeTM`, and (iv) lands in the
   binary alphabet via the proved `alphabet_reduction`, extracting the time
   bound by finite maxima (no polynomial bound claimed — permitted, since
   `canonizerTime` is existential). The batch flagged the deviation itself;
   the maintainer verification pass confirmed the proof is sorry-free with
   the standard axiom footprint and zero public-interface drift. **Open
   questions for a human:** (a) is the heavyweight
   `Mathlib.Computability.TMToPartrec` import into the TM tree acceptable,
   or should the bridge be quarantined behind the planned phase-5
   `MathlibBridge` module boundary (it effectively front-runs that module)?
   (b) is the enlarged trust/review surface (Mathlib's TM2 semantics + the
   private `bridgeTM` simulation, ~150 private declarations) preferable to
   a longer but self-contained combinator construction? (c) should the
   abandoned polynomial-`canonizerTime` claim be recorded as permanently out
   of scope, or re-derived later from the combinator route if one is ever
   written? Until reviewed, the bridge stays private in `Encoding.lean` and
   nothing outside `exists_effectiveMachineCode` depends on it.

2. **The 3B universal-interpreter proof architecture** (epoch 3, batches B +
   B2; `Universal.lean`, `Turing.universal`). The proof followed the audited
   sketch's outline (prefix-only startup, canonizer capture onto a table
   tape, four-work-tape interpreter with a fixed finite controller), but the
   realized architecture is by far the campaign's most involved artifact:
   2465 lines, 104 private declarations built across two agent sessions
   (WIP `f191b918` + continuation), a bespoke checkpoint relation
   (`universalRelation`) with generic block-simulation assembly
   (`universal_block_run` / `universal_from_blocks`), a virtual left
   boundary via a marker tape, a unary state tape with group-wise table
   scanning, and an *exact* per-phase cost ledger realized to
   `universalBlockBound = 3L + 5N + 20`. The kernel checks all of it, and
   the public statement is frozen and audited — but the *design* was never
   itself an audit deliverable at this level of detail. **Open questions for
   a human:** (a) is this the right load-bearing shape for epoch 4, where
   `timed_universal` must reuse the interpreter with a step counter — and
   which parts (the capture wrapper, the block-run/`universal_run_join`
   assembly, the marker-directed rewind and unary-copy gadget patterns, all
   flagged by the agents as promotion candidates) should graduate to shared
   modules at the epoch-3→4 merge rather than being re-derived? (b) is the
   exact-ledger posture (`3L + 5N + 20` proved to the transition) worth its
   brittleness against any future change to `CodeTM.serialize`, or should
   the maintained invariant be an existential bound with the exact ledger
   demoted to documentation? (c) does the interpreter's claim to *be* the
   book's universal machine (as opposed to satisfying the frozen statement,
   which the kernel settles) deserve a targeted human read of the
   construction's core definitions (`UniversalControl`,
   `universalInterpreter`, `universalRelation`), given no executable
   diagnostics of the whole interpreter ever ran (the batch-B smoke tests
   aborted on deep recursion and were discarded)?

## 6. Risks and honest effort assessment

- **The proof-sketch gap is the main cost.** The book proves Claims 1.5/1.6 and Thm 1.9 in
  a paragraph each; formally these are the expensive items. The AFP `Cook_Levin` entry
  spent most of its effort exactly here. `Composition.lean` is the hidden load-bearing
  file — budget for it.
- **Vendoring means drift** against a fast-moving upstream. Mitigation: minimal local
  modification, source commit recorded per file, periodic upstream diffs.
- **Definitions before theorems pays off:** phases 1–2 already give TCSlib a citable,
  blueprint-documented model of computation with P and oracles, onto which the existing
  `Complexity/NPReductions/` files can eventually be retargeted — even if phases 3–5 fill
  slowly.

## 7. Decision log

| Decision | Status |
|---|---|
| Vendor cslib `MultiTapeTM`; reuse mathlib only for `Language`/`FinEncoding`/bridge | Decided |
| Finiteness deferred in raw layer, enforced via bundled `FinTM` for all headline defs | Decided |
| Oracle wrapper lands in phase 1 (ahead of book order) | Decided |
| Work on branch `complexity/arora-barak-ch1`; verify via `scripts/lean_check.sh` (CI runs on main only) | Decided |
| Namespaces: `Turing` (vendored core) / `Complexity` (classes) | Working assumption; revisit on clash |
| NP/NTM signatures deferred to Chapter 2 work | Decided |
| §1.7 `O(T log T)` and oblivious-TM proofs are stretch goals | Decided |
| Blueprint: late-bound — generated from compiled Lean at phase boundaries only, nothing hand-written ahead of the Lean | Decided |
| External audits between phases: cross-vendor LLM with prepared packs (`audits/`), findings gate the next phase | Decided |
| Vendored cslib source commit: `a374775894efb9b7196cccf11235c60a97086dc1` (2026-09-14); relational semantics (`RelatesInSteps`) dropped in the port | Decided |
| Phase-1 audit round 1 (`audits/phase1-findings.md`): all 8 sorries confirmed true; 3 majors fixed — `TimeConstructible` repaired to `∃ c > 0, … c·(T n + 1)` (the literal exact bound refutes AB's own `id` example in this model), `OracleTM.WellFormed` added, oracle-tape constant-overhead claim corrected to polynomial; minors swept; audit-requested sanity statements added. Oracle citation is [AB09, Definition 3.4] (not 3.6) | Decided |
| Phase 1 requires a clean re-audit of the fixes before phase 2 starts | Decided |
| Phase-1 audit round 2 (`audits/phase1-reaudit-findings.md`): zero blockers/majors — all round-1 resolutions verified, all 8 new sorries confirmed true (with a worked `timeConstructible_id` witness machine reusable in the fill phase); 5 prose minors swept, blankness-certificate lemma added per note 6. **Phase-1 audit gate closed**; see `audits/phase1-resolutions.md` | Decided |
| Phase-2 renderings: Claim 1.6 rendered as **one work tape** (the merged input/work/output single-tape model is a genuinely different structure — it has an `Ω(n²)` palindrome lower bound our model beats — and is out of scope, with no identification claimed); Claim 1.8 rendered as **`NonnegativeHeads`** (our tapes are already bidirectional, so the meaningful direction is unidirectional use); obliviousness constrains input/work-head trajectories only — it does **not** force length-determined halting (phase-2 audit finding 1 refuted that with a stationary-head counterexample) and leaves emission schedules unconstrained; the `TimeConstructible` hypothesis in Exercise 1.5 is needed by the padding construction, not by the definition | Decided — audited (phase-2 round 1) |
| Output-tape/initialization convention obligations (phase-1 finding 4): **waived**, per phase-2 audit finding 3 — no formal bridge is possible without formalizing [AB09]'s read-write-output model, which this development does not do; the compensating restriction is that no exact-step-count transfer from [AB09] is ever claimed (all bounds carry existential constants, all results are self-contained in-model). The buffer-and-flush technique is documented in `Composition.lean`; a formal bridge is added only if a downstream result needs it | Decided — waiver accepted by phase-2 audit as a labeled option |
| Persistent-vs-erased query-tape polynomial-overhead statement moved from phase 2 to the Chapter 3 oracle-class work, where polynomial overhead is meaningful (class level); the impossibility of constant overhead stays documented in `Oracle.lean`. Outstanding obligation before importing any oracle-class invariance | Decided — deferral accepted by phase-2 audit (finding 13) |
| Phase-2 audit round 1 (`audits/phase2-findings.md`): 4 majors, 6 minors, 3 notes — **no theorem formula refuted**; all 11 new sorries assessed true as stated. Majors were prose/sketch-level: the false frozen-heads implication removed, the oblivious-simulation sketch replaced by the audit's corrected construction, the convention-discharge overclaim converted to the waiver above, ModelInvariance's invariance claims stated at delivered strength (alphabet: DTIME up to constants; tape count: P only). Sketch repairs: all-blank block for logical blank (1.5), tagged `Option Γ` payloads and `k = 0` case (1.6), piecewise fold coordinate with origin tags and safe-halt on non-embedded symbols (1.8) | Decided |
| Phase-3 audit round 2 (`audits/phase3-reaudit-findings.md`): zero blockers/majors — both round-1 counterexamples formally excluded (`serialize` proved injective and prefix-free from its parse grammar; the canonizer contract shown to decide the undecidable set for Argument A's scheme, so it cannot instantiate `EffectiveMachineCode`; code-first startup arithmetic verified with no input-length term). The α-dependent evaluator constant confirmed **necessary** (Argument E) — never to be described as [AB09]'s machine-dependent constant. Two minors swept (left-boundary marker in the evaluator sketch; `Nat.bits` order wording). Argument F provides complete phase-4 proof blueprints and identifies the guarded-composition API obligation. **Phase-3 audit gate closed**; see `audits/phase3-resolutions.md` | Decided |
| Phase-3 audit round 1 (`audits/phase3-findings.md`): **two blockers on the phase-3 statements, both accepted** — (1) the algebraic `MachineCode` admits noncomputable-meaning schemes against which no universal machine exists (Argument A), repaired by `EffectiveMachineCode`: an in-model canonizer into the new **fixed scheme-independent** `CodeTM.serialize` (canonizing into the scheme's own encode provably does not exclude the pathology); (2) the input-first `pairEncode x α` layout falsifies all three time bounds (Argument B), repaired by the **code-first** layout `pairEncode α x`. Majors: `universal` restated as the all-string evaluator `U(x, α) = M_α(x)` with a divergence-preservation converse and α-dependent constants; `universal_quadratic` labeled as the total-function corollary; `serialize` records the initial state (finding 5's collision). Minors: deadline-inclusive timeout convention documented; pack namespace erratum (`Complexity.succ_pow_le`). Fill round and supporting lemmas: audited clean (findings 9-13). Re-audit pending | Decided |
| Fill round 1 (commit `f8621285`): 20 of 28 phase-1/2 sorries proved — all semantics/arithmetic/chaining obligations, both oracle lockstep theorems, `mem_P_iff`, and `computesFunInTime_id` with an explicit machine. The 8 remaining sorries are exactly the heavy machine constructions (`const`, `comp`, the four robustness simulations, `timeConstructible_id`, `PAL_mem_DTIME_linear`), each with an audited outline. Repository-side verification: no audited declaration signature changed or was removed. Phase-3 skeleton delivered (5 statement sorries): `CodeTM`, abstract `MachineCode` scheme, `pairEncode`, Theorem 1.9 (linear for coded machines / relaxed quadratic / timed). Audit round covering fills + phase-3 pending | Decided |
| Phase-2 audit round 2 (`audits/phase2-reaudit-findings.md`): zero blockers/majors — both corrected load-bearing sketches certified as adequate proof outlines; 4 prose minors swept (fold alphabet `Bool × Option Γ × Option Γ`, waiver-prose synchronization, `O((k+1)·L)` overhead, one-work-tape *binary* normal form in phase 3); Lean-code identity between the audited commits verified repository-side by comment-stripped git comparison. **Phase-2 audit gate closed**; see `audits/phase2-resolutions.md` | Decided |
| Phase-4 skeleton landed (after the closed phase-3 loop, gate commit `b61e876d`): `Uncomputability/{Computable,Diagonalization,Halting}.lean` + facade — `Complexity.Computable`, `UC` (over an **arbitrary** `MachineCode`: the diagonalization never computes `encode`/`decode`, per round-2 Argument F; effectivity appears only in Theorem 1.11), `HALT` (totalized `false` off the `pairEncode` image; pair format = the evaluator's code-first layout), `UC_not_computable`, the reduction `UC_computable_of_HALT_computable` (uses only the *forward* clause of `universal`), `HALT_not_computable` (proved from the two). The audit-mandated guarded API landed in `Composition.lean` (`exists_comp_partial` — partial sequential composition with buffered intermediate output; `exists_cond` — branch on a decided predicate; `computesFunInTime_ifEq`), plus `computesFunInTime_pairEncode_diag` in `Encoding.lean` and `FinTM.Computes`/`ComputesInTime.output_unique`/`ComputesFunInTime.computes` in `Finite.lean` (additions to audited files, flagged for the phase-4 audit). 7 new sorries (21 total), every phase-4 proof sketch names only stated results. Phase-4 audit pack pending | Decided |
| Phase-4 audit round 1 (`audits/phase4-findings.md`, audited at `49d25a27`): **zero blockers, zero majors — the first single-round gate**. All 18 new declarations blind-restated in agreement; both headline arguments (UC diagonalization over an arbitrary `MachineCode`; `HALT → UC` reduction using only the forward evaluator clause) independently re-derived end-to-end from stated interfaces — no missing machine-construction API. One minor swept (the diagonal-pairing sketch's step count corrected to the auditor's `4n + 5 ≤ 6(n+1)` schedule; statement unchanged); note-level sketch refinements (unconditional first rewind move + empty-buffer boundary tag in `exists_comp_partial`; `HALT` off-image convention warning for downstream clients). **Phase-4 audit gate closed** — Chapter 1's critical path is fully specified and audited; see `audits/phase4-resolutions.md`. Remaining critical-path work: the 21-sorry fill campaign | Decided |
| Phase 5 (§1.7 `O(T log T)`, oblivious proofs, RAM-TM, mathlib bridge) **deferred to a much later effort** — not scheduled in the current push; revisit only after the phase-1-4 fill campaign completes | Decided |
| Fill campaign schedule (2026-09-16, §5 "Fill campaign"): 4 epochs of parallel disjoint-ownership batches (E1 ≈ 41 pts: assemblies + small machines + encoding list layer + classic machines; E2 ≈ 42: guarded-composition core + `one_work_tape` + remaining simulations; E3 ≈ 40: canonizer + `universal` + oblivious (droppable); E4 ≈ 10: `timed_universal` + closure), audit rounds at epoch boundaries. Cloud agents work from `briefs/epoch1-batch{A,B,C,D}.md`, branch off `complexity/arora-barak-ch1`, PR back into it; verification via `scripts/lean_check_tree.sh` + `scripts/ab_ch1_module_order.txt` | Decided |
| Epoch-1 fill round audited and closed (`audits/epoch1-findings.md` → `audits/epoch1-resolutions.md`): **zero statement-level blockers/majors** — freeze, all 22 elaborations, and all 13 axiom footprints independently reproduced; all four delivered machines certified against their audited schedules. One major was a pre-existing **tooling** defect: `scripts/lean_check_tree.sh` discarded Lean's exit status (false success on a diagnostics-free crash) — fixed (status propagation + fresh-olean requirement + failing sweep recipe), exploit reproduced against old and new gates, full sweep re-run under the strengthened gate. Auditor-endorsed epoch-2 merge pre-work: promote `Computes.exists_computesInTime_iff` (A) and a `Symbol`-generalized `computesInTime_iff` (B) into `Finite.lean`; create `TuringMachine/StateRenaming.lean` reusing `Turing.Action.mapState` (from Oracle.lean) at the raw layer; split the ~950-line `Composition.lean` (also resolves the finding-11 source-order obligation — epoch-1 gadgets sit *after* the remaining composition sorries, and they are not yet a buffered-composition simulator: 2A owes buffer/virtual-input invariants and explicit time bounds) | Decided |
| Epoch-2 merge refactor executed (commit `24687122`), per the epoch-1 resolutions: new `TuringMachine/StateRenaming.lean` (public `Action.mapState` moved verbatim from `Oracle.lean`; `Cfg.mapState` + application lemma; `MultiTapeTM.relabelState` + step commutation + `relabelState_runFrom_init`), new `TuringMachine/Simulation.lean` (the epoch-1 gadget layer made public and moved out of `Composition.lean`, with the finding-11 scope note that the embeddings are not yet a buffered simulator), the two `Finite.lean` promotions (`computesInTime_iff` generalized to any alphabet; `Computes.exists_computesInTime_iff`), and rewired `Encoding.lean`/`Halting.lean`/`Oracle.lean`. Declaration check: no public name lost (7 privates retired, 6 publics added); 24-module sweep clean under the strengthened gate, same 9 sorries. Epoch-2 briefs in `briefs/epoch2-batch{A,B,C}.md`, base `24687122`; **delivery is a zip archive** (runners have no GitHub write access — no PR step), standardized contents per epoch-1 findings 1 and 13: report, full sources, format-patch, git bundle, complete sweep log, per-theorem `#print axioms` log, SHA256 manifest | Decided |
| Epoch-2 fill round integrated (agent commits `3794a29c`-`6969c5f9` via git am; hygiene `ee32391c`; pack `f823daad`): **all five targets proved** — `exists_comp_partial` + `computesFunInTime_comp` (batch A: 26 new public `Simulation.lean` declarations, the buffered/virtual-input layer, `c = 2`), `one_work_tape` (batch B: 75 privates, `9k + 6`, 1315-line file escalated and accepted), `nonnegative_heads` (`c = 1`) + `alphabet_reduction` (`3L + 2`, one-hot code) (batch C: 88 privates). Maintainer-side verification: net freeze 10 removals = 5 sorries + 5 flagged docstring tails; 24-module sweep clean under the strengthened gate; **Theorem 1.10 now fully machine-checked (no `sorryAx`)** along with the whole normal-form chain — remaining admissions flow solely through `universal`. 17/21 sorries proved; 4 remain (= epochs 3-4). New `scripts/style_lint.py` provides the policy-conformance attestation (first catch: StateRenaming References section; NPReductions legacy FAILs recorded out of scope). Epoch-2 audit pack/bundle ready (`audits/epoch2-{pack,bundle}.md`); gate awaits `audits/epoch2-findings.md` | Decided |
| Epoch-2 fill round audited and closed (`audits/epoch2-findings.md` → `audits/epoch2-resolutions.md`): **zero mathematical blockers/majors** — all 26 public `Simulation.lean` declarations blind-restated clean; all three constructions certified (boundary/tag case table, independently re-summed sweep ledger, fold crossing identities, ~63k bounded executable checks); freeze and lint independently reproduced. Three minors swept: `AlphabetReduction` module docstring now discloses the one-hot width vs the sketch's logarithmic width; pack import-inventory erratum acknowledged (future packs generate it programmatically); `style_lint.py` declaration tally now comment-stripped. Epoch-3 merge pre-work endorsed: promote the optional-write normalization (raw layer), `source_bounds`, and B's sweep/zipper + indexed-transducer layers into a separate raw sweep module (not into `Simulation.lean`), `Nodup` hypothesis preserved. Epoch-3/4 obligations recorded: `universal` needs a prefix-only startup invariant (not dischargeable by `computesFunInTime_comp` alone); `timed_universal` counts source transitions in an explicit interpreter; UC's admission-free status is per supplied scheme (concrete schemes await `exists_effectiveMachineCode`) | Decided |
| Epoch-3 merge refactor executed (commit `71721842`), per the epoch-2 resolutions: new raw `TuringMachine/Sweep.lean` (the one-work-tape construction's generic zipper/transduction layer promoted verbatim — tape zippers + exact-cost transductions both directions + indexed transducers with the load-bearing `Nodup` + initialized-run `source_bounds`); `Turing.Action.apply_workTapes` promoted at the raw layer in `Simulation.lean` with `AlphabetReduction` rewired to it; `SingleTape.lean` down to 981 lines (policy WARN cleared); unused-tape promotion (rec 5) deferred until a consumer appears. 25-module sweep clean; campaign tree fully style-lint clean. Epoch-3 briefs in `briefs/epoch3-batch{A,B,C}.md`, base `71721842`, zip delivery: 3A canonizer (with the extract-the-bound-from-totality simplification via `Computes.exists_computesFunInTime`; short-circuit parser binding; no appeal to `universal`), 3B `universal` (prefix-only startup + captured-table correspondence obligations, virtual left boundary, unary state tape, regression axiom prints for the downstream theorems), 3C oblivious (masked-clock lockstep, full-schedule idling, trajectory-lockstep invariant, no appeal to `alphabet_reduction`) | Decided |
| Epoch-3 deliveries received (zips; PR path remains unavailable): 3A complete (`exists_effectiveMachineCode`, via the Mathlib computability bridge — **deviation from the audited sketch, recorded as open design question 1 above**), 3C complete (`oblivious_of_mem_DTIME`, three-layer schedule/decoration/parallel-coding architecture, explicit constant `c = 18(a+1)² + 23(a+1) + 3b + 25`), 3B an honest WIP (`fill/epoch3-B` @ `f191b918`: startup, captured table, boundary, halting/output correspondence and both assembly directions proved; **one** scoped sorry — the live-source table-lookup/record-application block — with four enumerated sub-obligations and an intended, unproved ledger `B(α) = 3L + 5N + 20`) | Decided |
| Epoch-3 A+C **verification pass** (scratch branch `epoch3-verify` = `cead5966` + the four agent commits via `git am -3`; **integration into `complexity/arora-barak-ch1` deliberately held for user go**): SHA256 manifests verified; ownership disjoint and respected (A: `Encoding.lean` only; C: `Robustness/Oblivious.lean` only); vendored freeze intact; diff removals are exactly the 2 target sorries + their 2 sketch-tail lines; the `cead5966` statement-prose docstring survived the 3-way merge; **zero public-declaration drift** in both files (fills are purely private: +153 / +233); full 25-module fresh-olean sweep exit 0, zero `error:` lines, sorry warnings only at `universal`/`timed_universal`; `#print axioms`: `exists_effectiveMachineCode` and `oblivious_of_mem_DTIME` **clean** (no `sorryAx`), `UC_not_computable` clean, `HALT_not_computable` admits only through `universal`. Style lint: campaign tree clean except the two expected size WARNs — `Encoding.lean` 2263 and `Oblivious.lean` 4086 lines, **escalations accepted here** pending the epoch-3→4 merge splits (A's bridge → its own module, C's decoration/coding layers). 19/21 sorries now verified proved | Decided |
| Batch B2 continuation brief written (`briefs/epoch3-batchB2.md`): base = branch `fill/epoch3-B` @ `f191b918` (created locally from the 3B bundle; **push pending**), scope = the single live-step obligation only, private WIP machinery revisable (including `universalBlockBound`), public statements frozen, delivery `epoch3-B2` zip with regression axiom prints; expected residual sorries in that lineage: `exists_effectiveMachineCode`, `oblivious_of_mem_DTIME`, `timed_universal`. Epoch-3 audit pack deferred until B2 lands (or `universal` is carried as the sole admission if B2 stalls) | Decided |
| Epoch-3 batches A and C **integrated** on user go (agent commits `1b16fcb8`-`cf4618bd` via `git am -3`, authorship preserved): the campaign branch's `TCSlib/` tree is byte-identical to the verified `epoch3-verify` state (the full-sweep and axiom-print evidence carries over verbatim; scratch branch deleted after the identity check). 19/21 sorries proved and integrated; the only remaining admissions are `universal` (B2 in flight from `fill/epoch3-B` @ `f191b918`) and `timed_universal` (epoch 4). Still owed at the epoch-3 boundary: B2 delivery, comment-stripped drift attestation, epoch-3 audit pack (must flag: the 3A bridge design question above, both size escalations, and the two batches' import additions) | Decided |
| Batch B2 delivered and **integrated** (agent commits `089d9057` + `179d736b` via `git am -3`, WIP commit included unchanged, authorship preserved): `Turing.universal` **proved** — the live-source block realized the WIP's intended ledger exactly (`universalBlockBound = 3L + 5N + 20` unchanged; per-phase proved costs in the B2 report, with the skipped-length refinement `P = P_g + P_b`), 22 new privates mapped to the brief's four sub-obligations, no WIP machinery revised, `Universal.lean` at 2465 lines (escalation accepted; split due at the epoch-3→4 merge alongside the `universal_run_join` shared-lemma request). Maintainer verification on the **combined** A+C+B2 tree (never elaborated in any agent lineage): series removes exactly one line (the `sorry`); freeze intact; zero public-decl drift (3 public / 104 private); full 25-module fresh-olean sweep exit 0, zero errors, exactly one sorry warning (`timed_universal`); axiom prints — `universal`, `universal_quadratic`, `exists_effectiveMachineCode`, `oblivious_of_mem_DTIME`, `UC_not_computable`, `UC_computable_of_HALT_computable`, and **`HALT_not_computable` all clean** (no `sorryAx`); only `timed_universal` still admits. **20/21 sorries proved and integrated — Theorems 1.9 (untimed + quadratic), 1.10, and 1.11 are fully machine-checked**; epoch 4 owes `timed_universal` + closure. Next at the epoch-3 boundary: drift attestation + audit pack | Decided |
| Epoch-3 boundary artifacts prepared: **drift attestation** (comment-stripped multiset over the fill span `71721842 → b519a004` — the only Lean line removed anywhere is `sorry` ×3; `Halting.lean`'s statement-prose fix verified comment-only; zero public-decl drift on all three owned files) and **epoch-3 audit pack** (`audits/epoch3-{pack,bundle}.md`, 40 attachments incl. all four agent reports in `audits/epoch3-agent-reports/`). Design question 2 added to §5 on user instruction: the 3B universal-interpreter proof architecture (shape for epoch-4 reuse; exact-ledger brittleness; targeted human read of the core definitions) joins the 3A bridge as human-reserved. Pack instructs the auditor that both constructions' *correctness* is in scope but their design *disposition* is a human decision. Gate awaits `audits/epoch3-findings.md` | Decided |
| Epoch-3 fill round audited and closed (`audits/epoch3-findings.md` → `audits/epoch3-resolutions.md`): **zero blockers/majors** — all three constructions certified from the definitions (3A parser/canonization on every word + the Mathlib bridge joints checked against the pinned sources; B2's ledger independently re-summed within `3L + 5N + 20` with the `h' < L` cursor argument; 3C's constant re-derived exactly, obliviousness at every physical time incl. post-halt absorption), ~14,000 bounded executable model checks with no counterexample, freeze independently reproduced with *ordered* comparisons + a GitHub fill-span cross-check, bundle SHA-256 confirmed. One minor swept: the superseded polynomial-canonizer sketch paragraph in `exists_effectiveMachineCode`'s docstring is now explicitly bracketed as original-and-superseded (comment-only, verified; the pack's "anywhere" overclaim acknowledged as an erratum, pack preserved per precedent). Notes adopted: ordered+multiset drift methodology; finding-8's `timed_universal` obligations recorded verbatim for the 4A brief (clock/α separation, canonize only `α`, buffered emissions, per-transition decrement, halt interception, deadline-inclusive success, budget-zero → `[false]`); degenerate-test vacuity and reproduction-scope acknowledgments. **Both human-reserved design questions remain open.** **Epoch-3 audit gate closed** | Decided |
| Epoch-3→4 merge refactor executed (three parallel mechanical splits, maintainer-verified): `Encoding.lean` 2269 → **`Encoding` 481** (pre-fill audited layout restored, `exists_codeTM` back in place) + **`CodeParser` 790** (the 3A grammar layer) + **`MathlibBridge` 1100** (primrec + TM2 bridge + `exists_effectiveMachineCode`, quarantining the `TMToPartrec` import; placement still pending design question 1); `Universal.lean` 2465 → **`UniversalStartup` 591 + `UniversalInterpreter` 1020 + `UniversalBlock` 794 + `Universal` 208** (statements only); `Robustness/Oblivious.lean` 4086 → **`ObliviousSchedule` 688 (incl. the relocated public `FinTM.Oblivious` def) + `ObliviousCandidate` 1127 + `ObliviousSetup` 1102 + `ObliviousLedger` 219 + `Oblivious` 1147** (ledger tail + theorem). **151 private→public promotions** (21 A incl. 8 pre-fill Encoding privates / 53 B / 77 C), each forced by a cross-module reference, all with statement-prose docstrings (7 minimal ones added in CodeParser); public statements byte-identical; verification: per-split multiset **and** ordered declaration-sequence comparison (finding-7 methodology) — B and C sequences identical (107/240 decls), A identical modulo the `exists_codeTM` relocation (block byte-diffed identical); the **single code change** anywhere is one `rfl` added in private `dataCfg_backward_step` (Lean mints `match` auxiliaries per module; the same constraint moved B's Interpreter/Block cut to line 1590 — both recorded in module docstrings). Full 34-module fresh sweep exit 0, zero errors, one sorry warning (`timed_universal`); all 8 axiom prints unchanged. Size WARNs: 4086-line worst case eliminated; five files remain at 1020-1147 lines, **justified**: Interpreter/Block cut fixed by matcher identity, ObliviousCandidate/Setup/residual bounded by interleaved-layer seams, MathlibBridge kept whole as the single foreign-trust quarantine. Facade + order file now 34 modules | Decided |
| Epoch-4A delivered and **integrated** (agent commit `37d70522` via `git am -3`, authorship preserved): **`Turing.timed_universal` proved — the fill campaign is complete at 21/21.** The deadline interpreter `timedUniversalTM` (six lanes: table, state, work, boundary marker, clock, output buffer; 130 new privates in `Universal.lean`, now 2831 lines — **escalation recorded**: the brief forbade splitting and ~1100 lines are stopped-interpreter administrative copies forced by per-module `match` auxiliaries; the report's three shared-lemma generalizations are the future factoring) discharges all five finding-8 obligations with a realized `α`-only constant `C = S + B + 14` (`S = 3A + K + L + 2h + 2q + 16` startup, `B` the untimed block bound, `2w + 4` per-step countdown). Maintainer verification: diff removes exactly the final `sorry`; zero public drift; statement/docstring byte-identical; **full 34-module fresh sweep: zero errors, ZERO sorry warnings**; **all eight headline axiom prints clean — `sorryAx` is gone from the development**: Theorems 1.9 (evaluator, quadratic, timed), 1.10, 1.11, `exists_effectiveMachineCode`, and Exercise 1.5 are fully machine-checked. Remaining closure work: final drift attestation, epoch-4 audit pack (must carry: this integration, the merge-refactor splits, both open design questions, the 2831-line escalation), blueprint extraction | Decided |
| Epoch-4 (final) boundary artifacts prepared: **campaign-closure drift attestation** — tree-wide public-name comparison `b519a004` → `fd7bb18e`: 227 → 378 public declarations, **zero lost, exactly 151 gained** = the recorded refactor promotions (4A added zero publics); per-split multiset + ordered-sequence verification carried from the merge; fill span removes exactly the final `sorry`; three byte-verified file relocations; soundness scans on both spans (one new import each: `FinCases`, `Nat.Bits`; `TMToPartrec` confined to `MathlibBridge`) — and **epoch-4 audit pack** (`audits/epoch4-{pack,bundle}.md`, 43 attachments incl. the 4A agent report and the three split-execution reports). Pack priorities: the timed fill's five obligations + ledger, the timeout clause on divergent sources, merge-refactor conformance via the public GitHub span comparisons, statement identity across gates, closure sanity; both design questions remain human-reserved. Gate awaits `audits/epoch4-findings.md` — the campaign's final audit round | Decided |
| Fate of this file at merge (graduate to `docs/` vs. superseded by blueprint) | Open — decide at merge time |
