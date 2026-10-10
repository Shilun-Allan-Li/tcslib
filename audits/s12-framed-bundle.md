# External audit pack — §12.6 framed catalog contracts (statement gate)

**Surface under audit:** five new sorried theorem statements in
`TCSlib/Complexity/TuringMachine/Build/Catalog.lean`, in the section "Framed
contracts (design §12.6)" just after the R3 rows:
`transferTM_run_ofCfg`, `copyTM_run_ofCfg`, `clearTM_run_ofCfg`,
`incrementTM_run_succ_ofCfg`, `incrementTM_run_overflow_ofCfg`. No machine is
defined or changed; the five machines (`transferTM`, `copyTM`, `clearTM`,
`incrementTM`, and their phase types) are the gate-closed §12 R3 definitions.
Record findings in `audits/s12-framed-findings.md`. **The gate closes on zero
blockers and zero majors**, which commissions the fill batch.

## Why these exist

The zone shift machines (`Build/Zone.lean`, `exists_zoneShiftInTM` and
`exists_zoneShiftOutTM`) have exactly two tapes: the zoned data tape and a
scratch tape that starts and ends as the unary level word. Their staging,
cleanup and binary navigation counter all run at **displaced heads beside
unrelated data**. The R3 rows are stated only from `Cfg.ofWords`, with heads at
the origin and globally buffered tapes, so none of them applies there.

The fill agent for those rows (ZF-A2, `audits/zone-agent-reports/f1-A2-REPORT.md`,
attached) stopped on this gap rather than copying the catalog's private trace. It
supplied a kernel-checked boundary regression: a bare transfer from a displaced
head on a valid carrier erases a cell belonging to the next zone. It also
supplied the typechecked type of the transfer contract it needed. Both are
attached. The statement under audit is that type, re-expressed in place, plus
the four siblings the same consumer needs. The design rationale is
`machine-library-design.md` §12.6 (attached).

## The common shape (verify for each)

Each contract quantifies over an **arbitrary** configuration `d` in the
routine's start phase. Its only hypothesis about the tapes is about the touched
word: for every relative offset `p` with `-1 ≤ p ≤ |w|`, the cell at
`pos + p` equals `bufferTape w p`. That is, the word sits at the head, with a
blank on each side. It then asserts three things.

1. **The exact configuration at the exact time** (`2|w| + 2`; for a successful
   increment, `2p + 2` where `p = (w.takeWhile id).length`). It is `d`
   with the state moved to the exit anchor and the word intervals rewritten.
   Every other cell, both head positions, the native input position and the
   output are unchanged.
2. **No earlier visit** to the exit anchor.
3. **Trajectory**: up to the exit, each touched head stays in
   `[pos − 1, pos + |w|]` (for a successful increment, `[pos − 1, pos + p]`),
   and every other head is fixed.

## Specific questions

1. **Truth at every boundary.** Check each statement at `w = []`; at an
   increment with `p = 0` and with `p = |w| − 1`; at overflow with `w = []`
   and `w` all `true`; and at heads displaced to negative coordinates.
   Previous gates in this campaign were lost on exactly such side conditions,
   so attempt at least three adversarial instantiations per statement.
2. **Hypotheses: necessary and sufficient.** Is the left delimiter at `-1`
   needed in each case? The return pass reads leftward until a blank. Is the
   right delimiter at `|w|` needed in each case? For a successful increment it
   is never read; requiring it is deliberately stronger, and consumers
   delimit anyway. Say whether this costs any consumer anything. Is anything
   assumed about the **destination** of transfer and copy? It should not be,
   since neither machine branches on the destination read. Check this against
   the transition tables.
3. **The finish configurations.** Are the rewritten intervals exactly right?
   For example, the transfer's destination interval holds
   `bufferTape w (q − pos_dst)` on `[pos_dst, pos_dst + |w|)`, and its
   delimiter cells are visited but never written. Does `incFixed` preserve
   width, so that the successful increment's interval `[pos, pos + |w|)`
   holding `v` is consistent?
4. **Specialization.** Does each framed contract imply its canonical R3 row
   (`transferTM_run`, `copyTM_run`, `clearTM_run`, `incrementTM_run_succ`,
   `incrementTM_run_overflow`) at `d := Cfg.ofWords …`? The fill brief will
   require the canonical rows to be re-derived from the framed ones, so this
   must hold.
5. **Fitness for the consumer.** Read the zone row statements in the attached
   `Build/Zone.lean`. Can a two-tape controller establish the delimited
   hypothesis, by saving the boundary cells in finite control, installing
   blanks, running the routine, and restoring them? And does the
   carry-sensitive `2p + 2` suffice for the audited geometric navigation
   ledger, `Σ_{r=1}^{2^i}(1 + v₂(r)) < 2^(i+1)`? Name any missing contract.

## Repository-side attestations (verify or challenge)

- **Elaboration.** `Build/Catalog` elaborates via `scripts/lean_check_tree.sh`,
  with exactly the five new `sorry` warnings. Everything downstream of
  Catalog replays with zero errors. Lint reports 0 FAIL.
- **Executed check.** The attached `audits/evidence/s12-framed/` harness
  evaluates the actual machines on concrete configurations with displaced
  heads, a nonblank outer frame and the boundary words. It compares the exact
  final configuration (both tapes over 30 cells, heads, input position and
  output), the no-earlier-exit clause and the trajectory bounds against each
  statement: 63 cases, all pass. A wrong-time negative control fails. This is
  evidence, not proof.

## Brief for the auditor

Audit the five statements, not tactic scripts. Hunt infidelity, vacuity, and
missing or excess hypotheses. Blind-restate each statement before reading its
docstring. Report in the standard findings table (blocker / major / minor /
note). Justify an empty table with your restatements and adversarial
instantiations.

# ===== ATTACHMENTS =====


## ===== audits/TEMPLATE.md =====

```
# External audit pack — TEMPLATE

Copy this file to `audits/phaseN-pack.md`, fill every `⟨…⟩`, and hand the result (plus
the listed attachments) to an external LLM from a different vendor, in a fresh context
with no access to this repository's development history. Record the findings in
`audits/phaseN-findings.md`. A phase's findings must be addressed (fixed, or explicitly
waived with a reason) before the next phase begins.

---

## Brief for the auditor

You are auditing the **trusted surface** of a Lean 4 formalization: definitions, theorem
statements, and remaining `sorry`s. The proofs that exist are machine-checked — do not
review tactic scripts for correctness. The failure modes you are hunting are:

1. **Infidelity** — a definition that does not mean what the cited source means.
2. **Trivialization** — a definition or statement satisfiable for degenerate reasons
   (vacuous hypotheses, a class that collapses, an encoding that makes a theorem empty).
3. **Unprovability** — a `sorry`d statement that is false as stated, or whose stated
   form is subtly weaker/stronger than intended (boundary cases: empty input, `n = 0`,
   `k = 0` tapes, constant absorption).
4. **Missing hypotheses** — especially finiteness, positivity, and well-formedness side
   conditions the informal source leaves implicit.
5. **Debt** — wholesale duplication of existing proved material (private copies of
   another file's declarations, re-derivations of registry routines), even when
   disclosed and mechanically forced by file ownership. Report it at **major** with
   the proposed fix "human acknowledgment required": it does not block the gate on
   soundness, but the gate must not close without the human maintainer explicitly
   accepting the debt and naming its scheduled resolution. Screen for it
   cumulatively — verify the pack's duplication ledger (per-file copied-material
   totals) rather than assessing each copy in isolation.

   **Accounting inside an acknowledged family is a minor.** Once the human
   maintainer has acknowledged a debt family and named its resolution, a later
   correction to that family's *accounting* is reported at **minor**, not major.
   Examples are a missed member, a miscounted span, or an imprecise description of
   the screen. Such a correction does not change what was approved. It is a
   **major** again only if it changes the approval itself: the correction pushes a
   further file past the one-fifth threshold, reveals copies outside the
   acknowledged family's named scope, or shows the named resolution cannot work.

For **every definition** in scope: restate it in your own mathematical English *without
looking at the docstring first*, then compare your restatement against the cited source
location, and report any daylight. For **every `sorry`d theorem**: argue in 2-5 sentences
why it is true as literally stated, or exhibit the problem (ideally a concrete
counterexample or degenerate instance). Attempt at least ⟨3⟩ *adversarial
instantiations* — concrete pathological objects plugged into the definitions to check
they behave as the theory intends. Propose any machine-checkable sanity theorems you
believe are missing.

Do not give a blanket approval. Your deliverable is the findings table; an empty table
must be accompanied by the per-definition restatements that justify it.

## Scope

| Item | Where |
|---|---|
| Lean files under audit | ⟨list of files, with line ranges if partial⟩ |
| Source text | ⟨book/paper, edition, page/theorem numbers — auditor must have it at hand⟩ |
| Plan/context documents | `AroraBarakChapter1Plan.md`, `policy.md` §2-3 ⟨adjust⟩ |
| Out of scope | tactic proofs; vendored files' upstream design ⟨adjust⟩ |

## Known deviations (declared by the authors — verify they are benign, flag any others)

⟨Bulleted list: every deviation the docstrings declare, one line each.⟩

## Specific questions for this phase

⟨Numbered list of the doubts the authors actually have. Be concrete.⟩

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide: **blocker** = a downstream phase would build on a wrong statement;
**major** = statement is fixable but materially misleading as is, **or** accumulated
debt (failure mode 5) that the gate may not close over without explicit human
acknowledgment (accounting corrections inside an already-acknowledged family are
minors; see failure mode 5); **minor** = edge case or naming/attribution defect; **note** =
observation, no change required.
```

## ===== machine-library-design.md =====

```
# Machine-construction library — design document

Status: **FROZEN 2026-10-03** — the open decisions in §9 were resolved by the
user (resolutions recorded inline there). No code exists yet; every Lean
snippet below is an interface *shape*, not a final signature — final
signatures are fixed at spec time and audited.

Evidence base: the epoch-2 checkpoint integration (decision-log row,
2026-10-03). All five open fill frontiers are concrete-machine construction;
147 private helpers were delivered in one epoch, dominated by re-built
copiers, scanners, counters, capture wrappers, and phase glue. The
capture/silence wrapper alone now has four private incarnations
(`universalCaptureTM`, `enumCaptureTM`, `acceptTM`, and the private engine
inside `Composition.lean`'s `exists_cond`).

Prior-art disposition (2026-10-03 discussion): Mathlib's TM2 framework is a
stack-machine model whose poly-time layer contains one machine (the identity)
and no composition theorem; its inter-model compilations are semantics-only.
Decision: build on our own `FinTM` multi-tape model, which owns all the
quantitative assets; adopt the *design idiom* of Mathlib's TM1 statement
language (labelled structured control) for how named machines are written,
import nothing.

## 1. Goals and non-goals

**Goal.** Make "build a finite machine with a proved polynomial time bound"
a library-call activity rather than a bespoke construction, at the
granularity the fill briefs actually need: parse, measure, evaluate a
polynomial, search, split, compare, copy, emit, run a subroutine silently,
branch, loop.

**Non-goals.**
- No deep-embedded language, no verified compiler, no cost-sound surface
  syntax. (Mature end state; not justified by the remaining campaign.)
- No model change, no Mathlib TM2 dependency, no space bounds (the design
  must not *obstruct* a later space story, but proves nothing about space).
- No retroactive migration of audited epoch-1/2 proofs (see §8).

## 2. Architecture

Three layers over the existing run calculus:

```
Layer 2  CONTROL      timed cond · loop · capture/silence · halt-redirect
Layer 1  PRIMITIVES   named machines with ComputesFunInTime specs, ABI-compliant
Layer 0  (exists)     run calculus · bufferedCompTM/computesFunInTime_comp ·
                      bufferTape/virtualMove relocation · DecidesInTime
Consumer EXISTENTIAL  PolyTimeComputable / ∈ P corollaries only
```

**Design rule (the bridge lesson).** Constructive layers export *named*
`def` machines plus spec theorems; existential packaging (`∃ M c, …`)
appears only at the consumer layer. Quantifier shape is where audits bite —
a consumer may never need to bound an existential witness.

**Composition stance.** The default sequencing mechanism is *whole-machine*
composition via the public `bufferedCompTM` (already proved, `c = 2`
overhead): chain function machines, don't hand-build phase transitions. The
epoch-2 agents could not do this only because (i) the component machines
didn't exist, (ii) branching has no timed combinator, (iii) loops have no
combinator at all. The library supplies exactly (i)–(iii) and otherwise
stops people from proving phase compositions by hand.

## 3. The calling convention (ABI)

The model already gives whole machines a clean boundary: read-only input
tape, `k` work tapes, write-only (append-only) output tape, start at
`initCfg` with blank work tapes. The ABI therefore governs the only places
where configurations cross a seam *inside* a construction: round boundaries
of the loop combinator and entry/exit of wrapped subroutines.

**Canonical configuration** (the single formal notion, defined once):

- designated *state tapes* hold the round data (specified contents, heads at
  origin);
- all *scratch tapes* are blank with heads at origin;
- the output is empty (nothing emitted yet);
- the control state is a designated live anchor.

Loop bodies and wrappers prove "canonical-in ⟹ canonical-out" lemmas; the
combinators own everything else (startup from `initCfg`, final emission,
fuel exhaustion). Proposed discipline for scratch: **the body restores its
own scratch to blank as part of its contract** (it knows its own footprint,
so the proof is its own invariant run backwards), supported by a generic
`clearTM` primitive that sweeps a length-`m` region in `2m + 2` steps.
Rationale: 2A's killer was a *generic* reset proof; a body-specific restore
is mechanical. The alternative (combinator-driven clearing bounded by the
visited-region lemma in `Sweep.lean`) is recorded as the fallback if
body-restore proves heavier than expected. **[Open decision 9.2]**

**Multi-argument functions.** The ABI for arity > 1 is the existing
`pairEncode` idiom; the codec machines (§4) make it mechanical. No tuple
tapes, no new conventions.

**Deciders.** A decider is a function machine emitting the singleton
indicator (`[true]`/`[false]`), i.e. `DecidesInTime` as it already exists.
The decision layer (§6) builds AND/OR/NOT/guard over that, so `∈ P` goals
decompose without touching configurations.

## 4. Layer 1 — the primitive catalog

Rule of admission: a primitive enters the catalog only with **two named
customers** among the open frontiers (2A controller, 2B `choiceVerifier` +
reverse direction, 2C two verifier memberships, 2D `D-MEM`/`D-WRAP`/`D-EMIT`)
and the E3/E4 briefs. Current cut — 12 entries:

| # | Primitive | Spec (shape) | Source | Customers |
|---|---|---|---|---|
| P1 | `copyTM` | id in `n + 1` | exists (`Composition.lean`) | everywhere |
| P2 | `constTM w` | `fun _ => w` in `\|w\| + 1` | exists | 2D D-EMIT, E4 |
| P3 | `prefixTM w` | `fun x => w ++ x` in `\|w\| + \|x\| + 1` | harvest 2C (promotion already requested) | 2C, 2D D-EMIT |
| P4 | `lengthTM` | `fun x => bits \|x\|` (binary length) | new (2D's counter composition is the engine) | 2B, 2C, 2D D-MEM |
| P5 | `polyEvalTM C c` | `fun x => bits (C·(\|x\|+1)^c)` and unary variant | harvest 2D (`polyUnaryTM` + counter) | 2A startup, 2B, 2C |
| P6 | `pairSplitTM` / `pairJoinTM` | the `pairEncode` codec, both directions | new over existing grammar lemmas (2C/2D parsers are drafts) | 2C, 2D D-MEM/D-WRAP, E4 |
| P7 | `replicateTM` | `fun x => List.replicate (f \|x\|) true` for emitted-count `f` | harvest 2D emission chains | 2D D-EMIT, E4 ledger |
| P8 | `compareTM` | equality / `≤` test of two encoded numbers, singleton verdict | new (small) | 2B, 2C bound re-check |
| P9 | `scanLastTM` | split at last `true` (strip discipline), failure verdict | harvest 2C (`stripCertificate` semantics are proved; machine is new) | 2C, 2B split search |
| P10 | `searchTM` | least `i ≤ n` with `p i`, for `p` decided by a supplied decider on encoded `i` | new (uses W1 + loop L) | 2B split, 2C split |
| P11 | `incrementTM` | fixed-width binary increment + overflow flag + rewind | harvest 2A (`enumCarryTM`) | 2A, E3 padding counters, ch3 |
| P12 | `clearTM` | blank a length-`m` region, `2m + 2` steps | new (trivial) | loop bodies, 2A reset |

Each entry ships as: named `def` + one `ComputesFunInTime`/`DecidesInTime`
spec + an ABI-compliance lemma (canonical-out where applicable). Internal
idiom: TM1-style labelled control (a small inductive of labelled phases with
a `step` match), which is what 2D's `PolyControl` was reaching for.

Harvesting means **reimplementation against the ABI with the original proof
as the template** — the audited originals stay untouched in place; see §8.

## 5. Layer 2 — control

**W1. `captureTM` (silence/capture wrapper).** Given machine `D`: run `D`
with every emission suppressed and recorded — core variant records the full
output on a dedicated capture tape; register corollary extracts the first
bit for deciders. Spec: configuration-preserving lockstep, emission on the
halting transition included (the trap every private build re-proved), return
within `T_D + 1` into a live dispatch state, physical output empty.
Consolidates all four private incarnations; the obligations are already
enumerated by the phase-1 and phase-4 audit tables. **[Open decision 9.3 on
variants]**

**W2. `haltRedirectTM`.** 2C's `acceptTM` pattern as a named transformation:
halt iff captured bit is `b`, else enter the one-state live loop (with its
two-line non-halting lemma). Customers: 2A overflow wiring, HALT-style
control modifications, ch3 diagonalization.

**W3. `condTM` (timed branch).** The timed version of `exists_cond`: given
decider `D` (time `T_D`) and machines `M₁, M₂` (times `T₁, T₂`), a named
machine computing `if p x then f₁ x else f₂ x` within
`c · (T_D + max T₁ T₂ + overhead)`. Engine: W1 + the existing private
capture machinery of `Composition.lean`, made public and timed. Customers:
2C/2D reject-on-malformed guards, every parser.

**L. `loopTM` (the centerpiece — bounded loop with tape-resident state).**
Interface factored from 2A's admitted `enumMachine_contracts`, which is the
validated draft:

```
-- SHAPE ONLY. Final quantifiers to be fixed at spec time, audited.
structure LoopSpec where
  (round data σ, encoded on the state tapes; canonical config family cfg : σ → Cfg)
  (body B; fuel R : ℕ → ℕ; per-round budget T : ℕ → ℕ)
  contract : ∀ s, canonical s →
    within T n, B either EMITS a final verdict and halts,
    or reaches canonical (next s)      -- accept-or-advance
  exhaustion : after R n rounds without emission, halted rejection

theorem loopTM_decides …  :
  (loop machine) decides/computes … within
    startup + R n · (T n + c) + c'
```

The combinator owns: startup from `initCfg` (via an init machine composed
with `bufferedCompTM`), the fuel countdown (P11 as the engine), the final
rejection, and the summation. The body owns: accept-or-advance and its own
scratch restore (§3). 2A's proved `enumLoop_run` is the summation lemma's
template; `enumMachine_contracts` then becomes a *library instantiation*
rather than a bespoke admission. Customers: 2A (directly), P10, 2B reverse
direction, E3 padding, E4 stage loops, ch3 clocked simulation.

**Explicitly deferred from layer 2:** a general tape-embedding transformation
(run a `k`-tape machine on a tape subset of a larger machine). The wrappers
and the loop internally preserve "retained tapes" the way 2A/2B already do;
if a third site needs the general form, it gets designed then — not
speculatively now.

## 6. Decision layer (consumer-facing)

Over `DecidesInTime`: negation, conjunction/disjunction (W1-composition),
`guard` (W3 with constant-reject branch), `decideOfFun` (function machine +
P8-style final test), and the `∈ P` glue through the existing
`mem_P_of_dtime_le`/`mem_P_iff`. Everything here is existential and cheap;
its purpose is that goals like `pairedVerifier C c V ∈ P` decompose into
catalog calls plus the semantic lemmas the agents already proved.

## 7. Placement, naming, policy

- New subdirectory `TCSlib/Complexity/TuringMachine/Build/` (precedent:
  `Robustness/`): `Convention.lean` (ABI notions + canonical-config lemmas),
  `Primitives.lean` (P1–P12; split if the 600-line target demands),
  `Wrappers.lean` (W1–W3), `Loop.lean` (L). Namespace `Turing.FinTM`
  throughout (no new namespace).
- Order list: insert after `Simulation`/`Composition`/`Sweep`, before
  `Encoding` — the library depends only on the run calculus and the public
  relocation/composition machinery; nothing Chapter-1-headline depends on it
  (no import cycles, Chapter-1 statements untouched).
- Attribution: standard constructions, tagged [AB09 §1.2–1.4] where the text
  has them (claim-by-claim as policy requires); module docstring records the
  TM1 statement-language idiom as a design reference (Mathlib) alongside the
  Asperti–Ricciotti and Forster–Kunze precedents.
- This is frozen Chapter-1 surface growth → it gets its own audit (§9.4 for
  the vehicle). Spec statements land sorried first (statement-phase
  discipline), the pack leads with the quantifier shapes (ABI, W1 lockstep,
  L's contract) since that is where this design can be wrong.

## 8. Harvest and migration policy

- Harvest = reimplement against the ABI using the original proof as
  template. Originals (2A/2B/2C/2D privates, audited epoch-1 material) stay
  byte-identical; no re-audit of closed work.
- Deduplication (retiring privates in favor of library calls) is an **E5
  closure task**, recorded in the backlog, not done opportunistically.
- 2C's pending shared-lemma requests (`prefixTM`/`fixedPair`) are subsumed
  by P3 + P6 and get their disposition in this design's audit round.

## 9. Decisions (resolved by the user, 2026-10-03)

1. **Primitive cut** (§4): P1–P12 confirmed as listed.
2. **Scratch discipline** (§3): body-restores-scratch, with
   combinator-driven clearing via the visited-region bound recorded as the
   fallback if body-restore proves heavier than expected.
3. **Capture variants** (§5 W1): tape-capture core + register corollary.
4. **Audit vehicle**: one shared infrastructure round carrying the library
   spec layer *and* the Chapter-1 bridge export.
5. **Build sequencing**: campaign structure — maintainer writes the spec
   layer serially (quantifier-sensitive), shared audit round, then fills
   dispatched as harvest-adaptation batches, the loop fill flagged for
   continuation budget.
6. **Naming**: `Build/` and the P/W/L working names stand; any rename
   happens before the spec audit (renames after it are drift).

## 9a. Spec-phase refinements (2026-10-03, recorded when the spec layer landed)

The spec layer (`TuringMachine/Build/{Convention,Wrappers,Loop,Primitives}.lean`)
realizes the catalog with these refinements against §4–§5, none touching the
frozen §9 decisions:

- **Seam notion**: `Cfg.ofWords` is a *constructor* (anchor state, input head
  at 1, word-per-tape from the origin via `bufferTape`, heads at origin,
  empty output) and seam contracts are `runFrom`-equations against it —
  rewrite-friendly, and `initCfg` is provably the empty-words seam.
- **Packaging**: contracts are existential in the house idiom of
  `Composition.lean`; fills implement named private machines and close them.
  The §2 named-machine rule is realized as quantifier discipline inside each
  statement (machine fixed after its parameters, before all inputs — the
  bridge lesson), not as global naming.
- **P6** is realized as `pairEncodeFixed` (provably an instance of P3 at the
  doubled-word-plus-separator prefix) plus threaded extractors
  `pairFst`/`pairSnd`/`pairValid`.
- **P7** is subsumed by P5's unary clause, whose instances are what the
  emission customers consume. **P8** is realized in threaded form
  (`pairLenCheck` on `pairEncode a b`, so the original input travels with
  the payload and the audited original-bound re-check is against it).
  **P12** has no standalone contract: clearing is intra-machine, part of the
  loop fill's toolkit.
- **W1** is host-parametric (`captureAction`/`captureCfg` transformers + one
  lockstep equation guarded by source liveness), so consumers embed the
  source into their own controller state type; the register corollary is
  derived at fill time. **W2** is the closed `redirectTM` with an
  `Option Bool` last-emission register (`none` = no emission yet; a source
  with empty output never halts the redirect).
- The lint-mandated construction sketches surfaced a real obligation worth
  recording: append-only output means every parser/extractor must **buffer
  until validity is known** — the output-silence discipline reappears at
  the primitive level (extractors, strip, increment's overflow detection).

## 9b. Round-2 repairs (2026-10-03, after `audits/ch1-infra-findings.md`)

The round-1 audit refuted `exists_loopTM` (blocker: a zero-step identity
"advance" made the hypotheses vacuous while the conclusion violated the
input-head information bound; major: quantifying rounds over *all* state
words at budget `T |x|` excluded the intended customers) and rejected
disposition D5 (missing dynamic assembly and result-bearing search). The
repairs, all in the spec layer:

**The loop contract, redesigned.** Rounds take positive time (`0 < t`);
rounds are required only on words satisfying an input-indexed
admissibility invariant `Inv x s`, established at `s0` and preserved by
the step; and `stepF`/`acceptF`/payload take the input explicitly (the
enumerator's acceptance runs the verifier on `x ++ s`). Two forms:
`exists_loopTM` (Boolean verdict) and the new `exists_loopFindTM` (first
accepting orbit point's payload; `[]` on exhaustion). The countdown sketch
debits from the **second** anchor entry, so `R = 0` still checks `s0 x`
(round-1 finding 4), and the amortized-borrow budget argument was
validated by the auditor.

**Instantiation tables** (the customer-coverage evidence round 1 asked
for; `m n := C·(n+1)^c` abbreviates the certificate-width polynomial):

| Parameter | Enumerator (2A's `enumMachine_contracts`) | Split search (P10) |
|---|---|---|
| `Inv x s` | `s.length = m x.length` | `s.length ≤ x.length + 1` |
| `s0 x` | `List.replicate (m x.length) false` | `[]` |
| `stepF x s` | `(incFixed s).getD s` (stall on overflow keeps the width) | `if s.length ≤ x.length then s ++ [true] else s` (stall keeps `Inv` step-closed) |
| `acceptF x s` | the captured verifier's verdict on `x ++ s` | `s.length + C·(s.length+1)^e = x.length` |
| payload | — (decision form) | `pairEncode (x.take s.length) (x.drop s.length)`, never `[]` |
| `R n` | `2^(m n) − 1` | `n` |
| fuel bits | `Nat.bits (2^(m n) − 1) = replicate (m n) true` — writable within `T` | `Nat.bits n` — writable within `T` |
| orbit, `i ≤ R n` | all `2^(m n)` width-`m` words, each once (`incFixed` enumeration; the stall is beyond fuel) | the candidates `0, …, n` in unary; `find?` = `solveSplit`'s least solution |
| conclusion shape | `[decide (∃ u, u.length = m n ∧ verifier accepts x ++ u)]` | exactly P10's stated function |

Both invariants bound the state-word length by the input, which is
precisely what dissolves the round-1 finding-2 obstruction (no body is
asked to transform words longer than its budget can traverse).

**Catalog additions** (finding 3): P13 `pairConcat`
(`pairEncode x u ↦ x ++ u`, the D-WRAP shape), P14 `pairDup`
(`x ↦ pairEncode x x`), and the combinator C1 `pairMapSnd` (transform a
pair's payload, retain its head; the data-retaining assembly sequential
composition cannot provide). D-EMIT's nested quadruple then factors as
`pairEncodeFixed α₀ ∘ pairMapSnd (unary-runs generator) ∘ pairDup`, and
D-MEM's parser chains through the extractors with `pairMapSnd` carrying
retained components. **P10 narrowing recorded**: the implemented search is
the fixed length-equation search, not the catalog's supplied-predicate
search; the general form is `exists_loopFindTM` itself.

## 9c. Round-3 repairs (2026-10-03, after `audits/ch1-infra-r2-findings.md`)

Round 2 passed the redesigned loops, P13/P14/C1, and the §9b tables, and
discharged both round-1 refutations; its one major (finding 1) showed the
loop's *final-answer* conclusion cannot discharge the frozen
`enumMachine_contracts`, which is a *configuration-level* contract — the
auditor's delay machine answers correctly yet violates every per-round
bound. Repairs:

**The configuration-level export.** `exists_loopCfgTM` (same hypotheses
as the decision form) concludes with the host's round-configuration
family: startup ≤ `c·(T+1)` reaching `cfg 0`, empty output at rounds
`0…R`, per-round accept-or-advance segments each within `c·(T+1)`, and
the halted `[false]` terminal at index `R+1`. The decision form becomes a
fill-time corollary through an already-halted-terminal summation lemma
plus monotonicity (R3-1: the frozen `loop_run` requires an empty-output
terminal, so it is not invoked directly on the exported family). **Index/budget
translation to `enumMachine_contracts`** (under the §9b enumerator
instantiation, `w := m n`): candidates `2^w = R n + 1`, so the terminal
index matches; the customer's uniform bound `b·(n + w + 1)^e` dominates
`c·(T n + 1)` once `T` is chosen as a polynomial in `n + w` and `b, e`
absorb `c` and its degree; the per-round indicator matches via the fill's
orbit bridge `(stepF x)^[i] (s0 x) = enumWord w i` (little-endian rank
enumeration, `incFixed` = `enumInc` per the round-2 vocabulary note).

**Vocabulary coefficient shift (round-2 note 5, adopted).** The proved
equalities are `splitAtLastTrue = stripCertificate`, `incFixed = enumInc`,
and `solveSplit (C+1) c = certificateSplit C c` — the split-search
equality is false without the shift (R3-3 corrected this pointer). Consequently the padded-verifier pipeline uses P10 at
`(C + 1, c)` while P8 keeps `(C, c)` for the original witness bound.

**General pairing assembly (round-2 item 10's derivation, adopted
verbatim as the canonical recipe).** For computed `f, g`:
`H x := pairEncode (f x) []` (P14 + C1 at the constant-empty function);
`s x := pairEncode x (H x)`; `t x := pairEncode (s x) (g x)` (P14 + C1,
the second with `g ∘ pairFst`); then
`pairSnd (pairConcat (t x)) = pairEncode (f x) (g x)` — the
self-delimiting grammar makes concatenation-into-payload well-formed at
every stage. A C1 call on `pairEncode a b` computes `g b` only; any
cross-component operation goes through this retained-whole-request
pattern, never through C1 directly (round-2 item 10's D-MEM caveat).

**D5 scope (round-2 items 6/10).** The disposition is re-issued for the
epoch-2 frontiers and P10 only; the E3/E4 rows are component-level
plausibility and their full coverage check is deferred to those epochs'
brief audits, where the six-stage/boundary/ledger tables are in scope.

## 10. Cost and sequencing (estimate, campaign points)

| Work | Est. | Note |
|---|---|---|
| Spec layer (all signatures + ABI) | 8 | maintainer, serial; the design-sensitive part |
| Spec audit round | — | rides with bridge export per 9.4 |
| P1–P12 fills | 14 | mostly harvest-adaptation; parallelizable |
| W1–W3 fills | 9 | W1 obligations already tabulated by past audits |
| L fill | 13 | the real risk concentration; continuation budget anticipated |
| **Total** | **≈ 44** | one mid-size batch equivalent |

Sequencing: freeze this design → spec statements + bridge export → shared
audit round → fills → **then** E2 continuation briefs, which cite the
library instead of re-deriving machines. E2 continuations, E3, E4, and the
ch3 skeleton are the customers that pay this back; the loop combinator is
the piece to watch for slippage.

## 11. The emitter increment (proposed 2026-10-05, post-E3 integration)

**Evidence.** E3's outcome maps the library boundary exactly: everything
recognizer-shaped closed in one round through the catalog (3B's memberships
via `computesFunInTime_splitSolve 1 1` + capture + the audited wrappers; 3D
via P10 + capture + composition), while both stalls sit on the producer
side — 3B at a streaming transducer (`satRedTM` states 9–34, defined,
unproved), 3A at a loop body that must internally run an evaluator and emit
a payload, over a width family the catalog's split instance doesn't cover.
The loop contracts deliberately require **empty output through every round**
(round-2/3 audit repairs), and composition offers only input-pipelining —
there is no output-append mode anywhere in the library. E4's summit
(`SAT_NPHard`, 15 pts, continuation certain) is an emitter of exactly this
shape: a per-index loop appending clause groups under the six-stage
output-silence contract with an exact serialization-length ledger.

**Rule of admission check** (§4): every item below has at least two named
customers among 3B-cont, 4A, 4B, and 3A-cont.

### E1. `emitLoop` — the emitting loop (control layer)

The loop engine's output clause generalized: rounds append exact per-round
emissions instead of staying silent. Shape (final quantifiers at spec time,
audited):

```
-- SHAPE ONLY. Sibling of exists_loopCfgTM, sharing its host machinery.
Inv, s0, stepF as in the decision loop; additionally
  emitF : input → σ → List Bool        -- the exact chunk of round i
contract: startup ≤ c(T+1); per-round segments ≤ c(T+1); positive
  first-return; for every i ≤ R:
    (cfg i).output = (List.range i).flatMap (fun j => emitF x (stepF^[j] s0))
  terminal: halted, output = the full concatenation (no verdict bit — the
  machine COMPUTES the concatenation; a deciding variant is NOT included).
```

Body obligations unchanged (accept-or-advance becomes advance-and-emit;
scratch restore per §3/9.2). The summation lemma is `loop_run`'s template
with the output clause threaded. **Customers:** 4A (the per-snapshot clause
emitter — the design driver), 3B-cont (`satRedTM`'s streaming core as an
instantiation), 4B (dual reduction emitter).

### E2. `emitPhase` — the forwarding wrapper (control layer)

The dual of W1: run an embedded transducer `T` (a `ComputesFunInTime`
contract) inside a host, with `T`'s emissions landing on the **host's**
output tape, source tapes isolated, halt redirected to a live return state;
lockstep lemma in `capture_run`'s mold with "physical output = host prefix
++ T's output so far". This is what lets a catalog transducer serve as one
emission stage of a larger machine — today's only option is whole-machine
input-pipelining. **Customers:** E1's per-round chunk calls (4A emits each
clause group through a sub-transducer), 3B-cont (fresh-literal chain
emission), 3A-cont marginally (the success payload `pairEncode` emission).

### E3′. Stream primitives (catalog rows P16–P18)

| # | Primitive | Spec (shape) | Source | Customers |
|---|---|---|---|---|
| P16 | `tokenStepTM` | consume one self-delimiting token (unary index / marker) from the input head, land head after it, expose the token in control | harvest: 3B's proved `satScanTM`/`satSyntaxStep`, 3D's six-state scan, 2D's parsers (fourth re-derivation otherwise) | 3B-cont, 4A, 4B |
| P17 | `chunkEmitTM w` / parametric | append a control-determined word to output, `\|w\|` steps, no tape movement | new (trivial); the per-token emission atom | E1 bodies, 4A |
| P18 | `unaryAccTM` | dedicated-tape unary accumulator: append one, read-length-in-binary via P4 composition, rewind | harvest: 3B's proved counter stages (`satRedCounter_write`, `satRed_maxOnes`, startup to state 9) | 3B-cont, 4A fresh indices |

### E4′. `splitSolveWith` — width-parametric split search (control layer)

Generalize P15's split search from the hardwired polynomial family to a
hypothesis-supplied width evaluator: given a machine `E` with a captured
`ComputesFunInTime (fun s => bits (f s.length)) T_E` contract and
monotonicity of `n ↦ n + f n`, a machine solving `n + f n = m` (first
success payload `pairEncode (take n) (drop n)`, exhaustion verdict) within
the loopFind envelope over `T_E`. **Harvest source:** 3A-cont's bespoke
body, whose contracts are already displayed in its REPORT — build the
parametric form against that template once it lands (or directly, if this
increment executes first). **Customers:** 3A-cont's equation (plug the
proved `e3_exp_bits_timed`), every future padding argument (ch3+ time
hierarchy pads the same way).

### Placement, cost, open decisions

- **Placement:** E1 extends `Loop.lean` **in-file** to reuse the audited
  `loopHost` privates (a separate `Build/Emit.lean` cannot see them — the
  D7 cross-file-privates qualification; re-deriving the host would be a
  second 2,500-line proof). `Loop.lean`'s size exception grows and the D7
  split trails as already recorded. E2 joins `Wrappers.lean`; P16–P18 join
  `Primitives.lean`; E4′ joins `Loop.lean` beside P15's engine.
- **Non-goals:** no deciding variant of the emitting loop (compose E1 with
  the existing decision layer instead); no general transducer algebra; no
  speculative tape-embedding (unchanged from §5's deferral).
- **Cost estimate:** spec layer 4; one shared-infra audit round (the ch1
  pattern, expected lighter — one host extension, not a new host); fills:
  E1 8, E2 4, P16–P18 5, E4′ 6 — **≈ 27 points**, roughly the L batch.
- **Sequencing:** freeze this section → spec statements → audit round →
  fills → 3B-cont consumes E1/E2/P16–P18; 4A's brief cites the layer
  instead of a bespoke emitter. **3A-cont dispatches in parallel, bespoke**
  (disjoint ownership; its body becomes E4′'s harvest template; later
  dedup is a recorded E5-style maintainer task, never the fill's).
- **Open decisions (user):** (11.1) approve the increment and this scope;
  (11.2) E1 as a sibling contract beside `exists_loopCfgTM` (recommended)
  vs a generalization replacing it (touches audited statements — not
  recommended); (11.3) whether 4A's brief waits for this gate to close
  (recommended) or anticipates it.

## 11a. Spec-phase refinements (2026-10-05, recorded when the emitter spec landed)

Decisions 11.1–11.3 resolved by the user (2026-10-05): increment approved;
E1 is a **sibling** contract beside `exists_loopCfgTM` (no audited statement
is generalized or touched); 4A's brief **waits** for this gate.

Refinements against §11 as drafted, all narrowing:

1. **P17 is subsumed** (no new statement): a constant chunk emission is
   `emitPhase` (E2) applied to the existing P2 `constTM` — recorded here
   the way D4 recorded the prefix/fixed-pair subsumptions.
   *[Superseded by §11b item 6 and §11c: the discharging rule is body
   finite control for fixed words, or `exists_emitCallTM` for computed
   chunks — never the private `constTM` (round-2 audit, finding 3).]*
2. **P18 narrowed to `computesFunInTime_appendBit`**: the drafted
   accumulator row conflated the append atom with cross-phase persistence,
   and persistence is already the loop engine's state-word mechanism; the
   catalog takes only the atom.
3. **E4′ lives in `Primitives.lean`**, not `Loop.lean`: its conclusion
   speaks `pairEncode`, which `Loop.lean` does not import, and P15's own
   public contract already lives there — the engine/contract split follows
   P15 exactly. Its pure vocabulary `solveSplitWith` joins `Convention.lean`
   beside `solveSplit`, which it definitionally generalizes.
4. **E1 is function-level only** (`exists_emitLoopTM` concluding a
   `ComputesFunInTime` of the chunk concatenation): all three named
   customers deliver `PolyTimeComputable` reductions, i.e. function-level
   contracts, and in-host composition of an emitter is E2's job, which
   takes function-level transducers. The round-2 lesson (final-answer vs
   configuration gap) was checked against each customer before choosing
   this form; a configuration-level export would follow the round-3
   precedent if a consumer ever surfaces.
5. **No emission-size hypothesis on E1**: the round seam equality itself
   bounds each chunk by the round's duration (output grows by at most one
   symbol per step), so the statement carries no redundant bound to drift.

Spec surface: **five sorried contracts** (`Turing.emit_run`,
`Turing.FinTM.exists_emitLoopTM`,
`Turing.FinTM.computesFunInTime_splitSolveWith`,
`Turing.FinTM.computesFunInTime_unaryToken`,
`Turing.FinTM.computesFunInTime_appendBit`), two real transformers
(`emitAction`, `emitCfg`), two pure vocabulary definitions
(`solveSplitWith`, `unaryTokenSplit`). Convention's module-docstring
vocabulary bullets extend at fill time (append-only).

## 11b. Round-2 repairs (2026-10-05, after `audits/emitter-infra-findings.md`)

Round 1: **0 blockers, 2 majors, 3 minors** — no false statement among
the five contracts; both majors are adequacy obligations, repaired here.

1. **The clean-call bridge (finding 1, major).** A function-level
   contract cannot deliver the loop seam: a witness may dirty scratch or
   leave heads displaced on its final transition and still compute `f`
   within `T`. Two new sorried bridge contracts supply the
   prepared-input/clean-return interface, both with canonical
   `Cfg.ofWords`/`stateWord` entry **and** exit seams, first-positive-
   visit discipline, and envelopes charged to `T + |arg| + |f arg| + 1`:
   `Turing.FinTM.exists_installCallTM` (result installed as the
   tape-resident word, nothing emitted) and
   `Turing.FinTM.exists_emitCallTM` (argument preserved, the computed
   chunk forwarded to physical output). Both live in `Loop.lean` beside
   the seams they serve (`stateWord` is defined there). Fill route: the
   A-continuation's proved log/undo pattern around the capture wrapper,
   with virtual-input preparation from the tape-resident argument.
   `emitCfg`'s docstring now states explicitly that it does not
   normalize terminal configurations — the bridges do.
2. **The 3B normalization mapping (finding 1, required resolution).**
   The reported `satRedTM` is **not** the promised instantiation as it
   stands (its permanent position-−1 marker contradicts the blank
   `ofWords` seam; its raw head positions cannot cross seams). The
   committed instantiation plan: loop state word encodes
   `(cursor, consumed-prefix length, phase tag)` via the audited pairing
   vocabulary — the raw streaming position is re-derived each round by
   advancing past the consumed prefix, and **the permanent marker is
   eliminated** (round-local buffering restores its tape by round end).
   Per round: decode the state word; `exists_installCallTM` over
   `computesFunInTime_unaryToken` reads the next token of the remaining
   serialization; finite control classifies marker/polarity bits; the
   emitted clause fragment goes out through `exists_emitCallTM` (chunks
   are of token-bounded length) or directly by finite control for
   fixed fragments; the fresh-variable counter updates through
   `computesFunInTime_appendBit` + install. Rounds have positive
   duration and input-length-only budget; `R` = the serialized input
   length (each round consumes at least one input position); once the
   formula terminator is consumed, an **absorbing finished phase emits
   empty chunks** for all remaining rounds. Token output is decoded by
   `pairDecode`-side vocabulary (proved); append output becomes the
   next state word by the install call. The banked `satReduction_*`
   semantics close the function identity; `satRed_start`'s proved
   maximum-pass survives as the `s0` computation.
3. **The 4A stage mapping (finding 2, required resolution — recorded
   here, certified against the attached phase-4 records in round 2).**
   All-string validation runs **before any irreversible emission**: the
   validation stages run as a decision prefix (the audited conditional
   W3 over the parser/boundary checks); only the valid branch enters
   the emitting loop, and the invalid branch emits the fixed fallback
   through finite control. Logical round count: `R` = the
   snapshot-index bound of the six-stage contract (an input-length-only
   polynomial), one clause group per round through `exists_emitCallTM`;
   the exact serialization-length ledger is the sum of the per-round
   chunk lengths — never constant-per-clause, exactly as the phase-4
   ledger demands. Serialization terminators: the final terminator is
   the last round's chunk tail (or a post-loop constant emission by
   finite control); both options keep the concatenation exact.
4. **Host routing correction (finding 3, minor).**
   `exists_emitLoopTM`'s construction sketch now specifies the
   **forwarding host variant** (body dispatched through `emitAction`;
   fuel/countdown machinery reused; contracts proved over
   arbitrary-accumulated-output configurations; a **new**
   prefix-summation lemma modeled on `loop_run`) — the unchanged
   find-mode host is refuted by the auditor's one-state witness, since
   `captureAction` suppresses the body's physical output.
5. **Token conventions (finding 4, minor).** `unaryTokenSplit`'s
   docstring now states it consumes unary tokens only, with the
   auditor's separating example; standalone markers and polarity bits
   are scanner grammar states.
6. **P17's actual rule (finding 1's visibility note).** Fixed
   finite-control chunks are emitted directly by body control (no
   primitive, no appeal to the private `constTM`); unbounded
   tape-dependent chunks go through `exists_emitCallTM`. §11a item 1 is
   corrected accordingly: the subsumption's discharging rule is body
   finite control, or the emit call, never the private constant
   machine.
7. **Documentation (finding 5, minor).** The four definitions now carry
   customers and construction notes; attestation 4's "every new
   declaration" claim is restated in the round-2 pack as exactly what
   each class of declaration carries.

Spec surface after round 2: **seven sorried contracts** (round 1's five
plus the two bridges), two transformers, two vocabulary definitions.

## 11c. Round-3 repairs (2026-10-05, after `audits/emitter-infra-r2-findings.md`)

Round 2: **0 blockers, 2 majors, 1 minor** — round-1 findings 3–5 closed;
the bridge construction and the 3B normalization validated (r2 findings
4–5, including a 5,908-case finite corroboration of the normalized
schedule); the two cumulative majors repaired here.

1. **Positive tape count on both bridges (r2 finding 1, major).** At
   `C.k = 0`, `stateWord 0 a = stateWord 0 b` by empty domain, so the
   install conclusion was satisfiable by a two-state zero-tape machine
   for an arbitrary — even noncomputable — `f`: vacuous as a data
   interface. Both conclusions now carry `0 < C.k`, making the seam
   equality yield the genuine `bufferTape` content at index zero. The
   auditor's r2 finding 4 confirms the log/undo construction delivers
   the strengthened interface at the stated envelope.
2. **The 4A mapping rewritten (r2 finding 2, major) — this supersedes
   §11b item 3 in full.** §11b item 3 wrongly substituted parser
   validation for Cook–Levin's silent preparation stages: the 4A source
   is an arbitrary `NP` language, every binary word is a legitimate
   instance, and there is no CNF well-formedness condition on `x` (the
   auditor's empty-language witness: validation-plus-fallback would
   emit the satisfiable `serialize [] = [false]` for a no-instance).
   Parse-before-emission belongs to the 3B/4B decode-based transducers
   only. The corrected stage-to-seam mapping:
   - **Silent preparation (inherited stages s1–s5).** A silent startup
     phase computes and packs the preparation records into `s0 x`:
     exact `Q(n)`, `m = n + Q(n)`, and the horizon `T` (s1, exact
     arithmetic, certificate length never enlarged); the virtual
     reference input `false^m` with clamped virtual head, source
     writes/moves executed on the halting transition, source output
     suppressed and halt internalized (s2–s3, through the capture and
     install-call interfaces at positive tape count); the inclusive
     trajectory records for **all** times `0..T` with administrative
     transitions outside simulated time and frozen positions after an
     early halt (s4); greatest-strictly-earlier-visit records with
     sequential comparison costs (s5). All of s1–s5 end with empty
     physical output and the packed records as the clean persistent
     word — the emitting loop's `s0`.
   - **Ordered emission (s6).** One **family member per round**, the
     cursor walking the fixed family order of the phase-4 contract.
     With `T + 1` snapshot times and `k` work tapes, the six families
     have `n, 1, T, T+1, k(T+1), T` members; the round count is their
     sum: `R = n + (k+3)·T + k + 1` (an input-length-only polynomial).
     Rounds with empty template output still take positive time. The
     single final formula terminator is appended to the last round's
     chunk. The serialization-length ledger is the exact sum
     `1 + 2·#clauses + Σ (v+3)` over literal occurrences — total
     output `O_M(T²)`, never constant-per-clause.
   - The alternative `R = T` time-major grouping is **not** adopted:
     it would need a separate proof that its interleaving reserializes
     to the fixed family order.
   Certification of this mapping against the phase-4 round-2
   boundary-check table is round 3's business — that table
   (`audits/ch2-phase4-reaudit-findings.md`) rides in the r3 bundle,
   and the 4A brief inherits it verbatim per the standing rule.
3. **P17 cross-reference (r2 finding 3, minor).** §11a item 1 now
   carries an explicit supersession marker pointing at §11b item 6;
   the historical text is preserved as history.
4. **Provenance upgrades for round 3.** The log/undo fill route now has
   fresh in-repo provenance beyond the epoch-2 enumerator: the
   A-continuation checkpoint (integrated 2026-10-05) banked exactly the
   track/clear/compare phase family the r2 finding-4 construction
   describes (`e3cTrackTM`/`e3c_track_run`/`e3cClearTM`/`e3c_clear_run`
   — logged simulation over a visited interval with origin markers,
   exact single-triple cleanup at `6T+7`, positive first returns), as
   proved privates in `Nondeterminism.lean`; its REPORT and source ride
   in the r3 bundle.

Spec surface after round 3: unchanged in count — **seven sorried
contracts** (the two bridges now carrying `0 < C.k`), two transformers,
two vocabulary definitions.

## 11d. Gate close (2026-10-05, after `audits/emitter-infra-r3-findings.md`)

Round 3: **0 blockers, 0 majors, 1 minor, 4 notes — GATE CLOSED**
(`audits/emitter-infra-resolutions.md`). Both cumulative majors
discharged: the positive-tape bridges export the data interface (the
auditor's projection-table derivation), and §11c's 4A mapping is
certified against the inherited boundary table, including the exact
per-member chunk rule. The minor — swept in the closing commit — was an
attribution error of §11b item 1/§11c item 4 and the install-call
sketch: the A-continuation's delivered provenance is
**visited-interval tracking and clearing** (`e3cTrackTM`/`e3cClearTM`),
not an overwritten-symbol history/undo implementation; at a clean
entry seam, clearing is restoring, so the track/clear route fills the
bridges directly, and history/undo stands only as the independently
derived alternative (r2 finding 4). Two clarifications from r3
finding 3 bind the 4A brief: `R = n+(k+3)T+k+1` is the last round
index (member count `R + 1`), and the chunk rule emits per-member
flatMaps with the single terminator on the last chunk only. Fill
batches proceed under the resolutions' binding section, partitioned
Loop / Primitives / Wrappers.

## 12. The routine layer (proposed 2026-10-08, pre-ch3/4 campaign)

**Mandate** (user decisions 2026-10-06 and 2026-10-08, recorded in `backlog.md` §2
and `AroraBarakChapters3-4Plan.md` §4a/§8): built after the Chapter-2 closure and
**before the chapter-3/4 fill epochs**, in parallel with their statement phases;
scoped to **amply support the chapter-1/2 retrofit**, not merely the new
consumers; and — superseding §1's "no space bounds" non-goal for this increment —
**every item below carries a space clause alongside its time cost**, so that the
chapter-4 campaign and the P4.x statements consume the layer without a second
pass. The space measure is the house one: `Turing.MultiTapeTM.spaceUsed`
(work-tape cells visited; input and output tapes excluded).

**Evidence.** The 4A chain is the measurement: roughly half of the A2/A3
deliveries' 202 native privates are hand-rebuilt bank/relocation/dispatch
routines; the `emitterBank*`/`emitterP2*` relocation family was privately
re-harvested three times; and A3's proved costs (`3|w| + 3` copy, `2|w| + 2`
clear) match the external prior art's `3w + 2`/`2w + 2` to within one step —
independent convergence on the same catalog, discovered in the 2026-10-06
survey. The emitter round-1 finding stands: *function-level* contracts cannot
deliver clean-return seams, so the gap is configuration-level. §5 deferred the
general tape-embedding transformation "until a third site needs it"; the third,
fourth, and fifth sites have now arrived (the retrofit families, the
Hennie-Stearns conversion, the two-work-tape universal machine).

**What already exists and is consumed, not duplicated** (colleague modules,
Hydroxyi/Jason Dong, on `main` since `f70c57c2`): the *function-level half* —
`TuringMachine/CounterProg{,Run}.lean` (goto programs over unary registers
compiled once into `FinTM`, `t` abstract steps within `t(2t+3)` machine steps,
FP bridge via `ClassNP/CounterProgPolyTime.lean`), `ClassNP/Transducer.lean`,
`ClassNP/{PolyTimePairing,PClosure}.lean`, `TuringMachine/UnaryTape.lean`; and,
on the space side, `SpaceComplexity/Machines/` (the `LogProg` register-program
compiler with `compile_space`/`arm_decides`). §12 supplies the
configuration-level half those layers sit on.

### R1. Bank embedding (the §5 deferral, promoted)

A verified routine on its own `m`-tape set runs on any injectively selected
subset of a `k`-tape host's work tapes, cost unchanged, everything else framed.
Spec shape (final quantifiers fixed at spec time, audited): for an embedding
`ι : Fin m ↪ Fin k`, transported actions and configurations with

* **lockstep** — transported `runFrom` commutes with the source `runFrom`;
* **frame** — tapes outside `range ι` are byte-identical before and after, their
  heads unmoved; input position tracks the source; emission policy is a
  parameter (suppressed or forwarded — the W1/E2 pair fixes the two modes;
  whether this is one transformer with a mode or two transformers is open
  decision 12.4);
* **time** — step count preserved exactly;
* **space** — cells visited on host tape `ι i` equal cells visited on source
  tape `i`; unselected tapes visit nothing new.

Generic form of: `emitterBank*`, the `emitterP2*` relocation family,
`clBank*`/`clSlot*` (4A chain), and their chapter-1 analogues in
`Build/Primitives.lean`/`Build/Loop.lean` internals.

### R2. Seam composition

Sequential composition of two controllers at a canonical `Turing.Cfg.ofWords`
seam (Convention.lean's ABI notion): if `M₁` carries seam `c₀` to seam `c₁`
within `T₁` under a first-return cut, and `M₂` carries `c₁` to `c₂` within
`T₂`, the dispatch-glued machine carries `c₀` to `c₂` within `T₁ + T₂ + O(1)`,
with the glue state-sum and dispatch lemmas owned by the combinator. Space
clause: visited sets union, so per-tape space is bounded by the sum of the
parts' per-tape spaces (whether the spec states the sharper per-tape `max` for
disjointly-owned tapes is open decision 12.1). Generic form of the per-batch
dispatch gluing re-proved in every A-chain and emitter batch.

### R3. Catalog promotion, with space costs

Promotion of the remaining audited A-chain privates as public machines with
exact time *and* space costs: transfer (word from tape `i` to tape `j`,
`3|w| + 3`), copy (`3|w| + 3`), clear (`2m + 2`, = P12's engine), compare, and
increment — D6-style promotion, not new proof work, seeded from the named
private families. Additionally, the existing catalog rows (P1-P12, P16-P18)
and the W/L/E combinators are **retro-annotated with space theorems** — new
`spaceUsed` lemmas beside the existing specs, no signature changes, so the
audited statement surface is untouched (additive growth; open decision 12.3 on
doing this here versus lazily per consumer — the amply-support mandate argues
for here).

### Consumers (rule-of-admission check, §4: two named customers per item)

| Consumer | Uses |
|---|---|
| Chapter-1/2 retrofit (backlog §2) | R1 for the bank/relocation families; R2 for the dispatch families; R3 for `clCopy*`/`clCmp*`/`clRead*`/`clCount*` and the `Build/` harvest families |
| Hennie-Stearns `k`→2 conversion ([AB09] §1.7; ch3-4 plan §2.1) | zones as banks (R1), shifts as R3 transfers, seam discipline (R2); the amortization is mathematics on top |
| Two-work-tape universal machine (ch3-4 plan §2.1, §4a) | R1 + R2 throughout; the retrofit pilot; candidate space-bounded variant feeding Thm 4.8 / Ex 4.1 |
| Chapter-4 ARM extensions (ch3-4 plan §2.5: nondeterministic and polynomial-width variants of `LogProg`) | R1/R2 at their `FinTM` compilation boundary; R3 space rows |

### Placement, sequencing, cost

* New files `Build/Embed.lean` (R1) and `Build/Seam.lean` (R2); R3's new rows in
  a new `Build/Catalog.lean` (`Primitives.lean` is already over the size policy;
  final name is open decision 12.2, settled before the spec audit per §9.6).
  Namespace `Turing.FinTM`; order list after `Build/Loop`.
* Process per `workflow.md`: maintainer-serial spec layer (quantifier-sensitive,
  as §10), statement gate, fills as harvest-adaptation batches, fill audit. The
  gate must close before the first chapter-3/4 fill epoch (plan §4a); statement
  phases of chapters 3-4 run in parallel.
* Estimate (campaign points): R1 spec+fill ≈ 10 (the lockstep is the risk
  concentration, L-style), R2 ≈ 8, R3 promotions + space retro-annotation ≈ 12,
  serial spec layer ≈ 6. Total ≈ 36, one mid-size batch equivalent.

### Open decisions (human review; audit verifies, never disposes)

* **12.1** R2 space accounting — **answered (user, 2026-10-08): the sharper
  form.** The spec states per-tape bounds, with the max for disjointly-owned
  tapes (sharpest available; downstream applications may depend on the
  sharpness).
* **12.2** R3's file layout — **answered (user, 2026-10-08): option (a)**, a
  new `Build/Catalog.lean` holding the new rows and the space lemmas for the
  old rows, keeping `Primitives.lean` byte-identical; a backlog item records
  the later refactor toward the symmetrical per-theme layout (option (c)),
  via the D7 split window.
* **12.3** Space retro-annotation — **answered (user, 2026-10-08): the refined
  now-option**: the primitives as realized (P1-P15), wrappers (W1-W3) and the
  loop (L) get `spaceUsed` theorems in this increment; the emitter combinators
  (E1-E4′) stay lazy until a space consumer appears, **and the E3′ stream rows
  P16-P18 ride with that lazy scope** (their only consumers are the emitters —
  scope clarification recorded at skeleton time, 2026-10-08, flagged to the
  §12 statement-gate audit and reversible there if the gate reads the
  original "P1-P18" wording as binding).
* **12.4** R1 emission policy — **answered (user, 2026-10-08): two named
  transformers** (suppressing and forwarding) over a shared private core, so
  each spec stays crisp and downstream applications cite whichever fits.

### Citations (policy.md §2, *Design adaptation*)

The configuration-level design is adapted from — with nothing transcribed —
**Édouard Bonnet's `classical-complexity`** (Lax Archive lax-434930), module
`proofs/Lax434930Proofs/InclusionAux/TimeCompiler/`: `StackProgram`'s
`compile_correct`, `StackRename`'s `rename_executes`/`executes_in_sum` (the
bank-embedding and seam-composition shapes), and the
transfer/clear/copy/for/repeat routine catalog; commit
`0c0840319318215fd7b36a9a822b81ce55cf6941`, Apache-2.0; examined 2026-10-05,
different toolchain (Lean 4.33 vs our 4.25) and machine model (TM2-style keyed
stacks vs `FinTM` tapes with heads). Suggested tag: `[Bon26]`. The R-modules'
docstrings and their blueprint entries must carry this citation, alongside the
existing `[Balbach22]` (AFP `Cook_Levin`) for the composition architecture and
the in-repo credits to the colleague modules named above.

### 12.5 Round-1 audit repairs (2026-10-09)

The §12 statement-gate round 1 (`audits/routine-infra-findings.md`: 0
blockers, 4 majors) drove four repairs, landed with the round-2 pack:

* **R1 → the returning embeddings** `embedSilentRetTM`/`embedEmitRetTM`
  (states `S ⊕ Unit`): the closed transformers lose a final halting
  emission to either the halt or a premature seam dispatch — the audit's
  formal trace. The returning flavors execute every source action through
  the halting transition and land in the live anchor `Sum.inr ()`.
* **R2 → general-configuration seam composition**
  (`seamCompTM_run_ofCfg` + first-return and visited forms): the canonical
  `Cfg.ofWords` theorems cannot consume arbitrary frames, displaced
  inactive heads, or accumulated output; the general form starts phase two
  from phase one's returned configuration with only the control state
  replaced.
* **R3 → the fresh-entry/release adapter** `seamReleaseTM`: positive
  calls returning to their own anchor are now seam-consumable (the entry
  action executes unconditionally from a fresh start state).
* **R4 → the threaded-map witness** is re-commissioned as a forwarding
  controller (validate/buffer, emit prefix, forward payload output);
  the received captured-payload machine is refuted as a witness for the
  linear-administration bound.

Scope notes R9 (physical-tape selection is not zone multiplexing) and R10
(loop sibling contracts not exported) are recorded at their definition
sites.

### 12.6 Framed catalog contracts (2026-10-10, after ZF-A2's escalation)

**The gap.** The R3 rows (`transferTM`, `copyTM`, `clearTM`, `compareTM`,
`incrementTM`) are stated only from `Cfg.ofWords`: every head at the origin,
every tape a globally buffered word. The zone shift machines (`Build/Zone.lean`,
`exists_zoneShiftInTM`/`OutTM`) have **exactly two tapes**. One is the zoned data
tape; the other is a scratch tape that starts and ends as the unary level word.
Their staging, cleanup and binary navigation counter therefore all run at
**displaced heads beside unrelated data**, where no canonical contract applies.

ZF-A2 (`audits/zone-agent-reports/f1-A2-REPORT.md`) showed the gap concretely,
with a kernel-checked regression. On a valid three-level carrier, a bare transfer
from a displaced head reads past the word's end and erases a cell that belongs
to the next zone. The cure is a delimited word: blanks at relative positions
`-1` and `|w|`, installed by the consumer, which saves the overwritten cells in
finite control and restores them afterwards. Correspondingly, the contract must
quantify over an arbitrary surrounding frame.

**Decision (user, 2026-10-10).** A small §12 extension: maintainer-drafted
statements, a short statement gate, then a fill batch; ZF-A3 follows. The
routines are local, since each step reads only the scanned cells of the touched
tapes, so a framed contract is the faithful generalization. No new machine is
defined.

**The five statements** (`Build/Catalog.lean`, after the R3 rows, sorried):

| Contract | Exact time | Effect on the touched tapes |
|---|---|---|
| `transferTM_run_ofCfg` | `2·|w| + 2` | source interval blank; destination interval `w` (old destination contents arbitrary) |
| `copyTM_run_ofCfg` | `2·|w| + 2` | destination interval `w`; source intact |
| `clearTM_run_ofCfg` | `2·|w| + 2` | the word interval blank |
| `incrementTM_run_succ_ofCfg` | `2·p + 2`, where `p = (w.takeWhile id).length` | the word interval holds `v`, where `incFixed w = some v` |
| `incrementTM_run_overflow_ofCfg` | `2·|w| + 2` | the word interval all `false` |

In every case the routine reaches its `done` anchor exactly at the stated time
and not earlier. Every cell outside the word intervals, every head, the native
input position and the output are unchanged. Up to the exit the touched heads
stay within `[pos − 1, pos + |w|]` (for a successful increment, `[pos − 1,
pos + p]`) and all other heads are fixed. Space bounds follow from the
trajectory clause through `MultiTapeTM.spaceUsedByTape_le_card_Icc`.
`incrementTM`'s carry-sensitive `2p + 2` is the per-step cost that makes the zone
machines' anchored binary countdown sum geometrically, the audited `O(2^i)`
navigation ledger. The canonical `2|w| + 2` public bound is too loose for that,
as ZF-A2 flagged.

**Specialization and dedup.** With the origin heads and globally buffered words
of `Cfg.ofWords`, each framed contract specializes to its canonical R3 row. The
fill batch therefore proves the framed form and **re-derives each canonical row
from it**, through a sanctioned proof-body swap with the public statement
unchanged. That generalizes the private trace lemmas rather than duplicating
them. `compareTM` is not framed here, since no current consumer needs it; it
follows the same pattern on request.

**Pre-ship execution check (mandatory practice).** Every statement was executed
on concrete configurations with displaced heads, a nonblank outer frame and the
edge cases (`w = []`, `p = 0`, all-`true` overflow). The exact final
configuration, the no-earlier-exit clause and the trajectory were compared:
63 cases, all pass, and a wrong-time negative control fails
(`audits/evidence/s12-framed/`).

## 13. The zone and virtual-input layer (proposed 2026-10-09, post-§12 close)

**Mandate** (user direction 2026-10-09, at the §12 fill-campaign close —
track A of the two parallel tracks, the other being the chapter-1/2
retrofit): the §12 scope note **R9 promoted**. R9 drew the line at
physical-tape selection — `ι` relocates whole tapes and "the Hennie-Stearns
and universal-machine consumers get their zone/virtual-input representation
layers separately" (`Build/Embed.lean` header). This increment is that
separate layer. It gates the two stage-1 builds (the Hennie-Stearns `k`→2
conversion and the two-work-tape universal machine, plan §2.1/§4b) and is
scoped, like §12, beyond its first consumers: the virtual-input half serves
the `NP^EXPCOM ⊆ EXP` summit and the 12.2c dedup, and the zone half is
shaped so the chapter-1 Robustness conversions can gain **space theorems
additively** (plan §2.7's fallback route to Ex 4.1/Thm 4.8). §12's space
mandate continues: **every item carries a space clause alongside its time
cost** (`Turing.MultiTapeTM.spaceUsed`, work tapes only).

**Evidence.** The virtual-input pattern has now been hand-built four times
over the proved corpus: the A2 forwarding controller's
`a2_mapVirtual`/`a2_mapVirtual_step`/`a2_mapVirtual_run` lockstep (15 of
its 45 privates; both boundary clamps, empty-word case, halt absorption —
all proved), F2A's `f2_splitCountAction`/`f2_splitCount_run`
(virtual *empty* input over preinstalled banks), the universal
interpreter's prefix-input discipline, and the oblivious candidate's
`obliviousVisit` virtual-tape transduction. All four sit on the same public
primitive — `virtualMove`/`VirtualTag`/`virtualNextTag` and
`bufferTape_inputSymbol` (`Simulation.lean`) — and each rebuilt the hosting
and lockstep privately. On the zone side, the in-repo precedents are the
`SingleTape.lean` multiplexing encoding (`SweepCell`/`tapeRow`) and
`ObliviousSetup.lean`'s guide-zone layout with its two-directional run
identities; what does not exist anywhere is a *reusable* zoned carrier with
shift routines. The F2 epoch audit's three optional regression corollaries
(zero-time startup, both virtual-input clamps, setup followed by an
emitting halting step) are adopted here as permanent lemmas of Z1.

**What already exists and is consumed, not duplicated**: the §12 layer
itself (R1/R2 and the catalog rows are the assembly language of every
construction below); `virtualMove`/`VirtualTag` (`Simulation.lean`);
`Turing.actionBits₂` and the `CodeNDTM` two-work-tape serialization
(`NDCodes.lean`, statement-frozen under the closed P3.3 gate) — Z3 builds
the deterministic sibling against the same record format, never a second
serialization; `UnaryTape.lean`; the harvest policy of §8 (reimplement
against the ABI with the original proof as template; audited originals stay
in place until the separately-tracked retrofit/12.2c dedup).

### Z1. Virtual-input hosting (the `a2_mapVirtual` pattern, promoted)

A transformer hosting a machine whose input is a **designated buffered
word** rather than the native input: given a host with an injective tape
selection (R1's `ι`) plus one buffer tape holding `y`, the hosted machine
runs with `y` as its virtual input, buffer head at
`source.inputPos - 1` under a `VirtualTag` boundary discipline. Spec shape:

* **lockstep** — one host step per source step, transported `runFrom`
  identity (the A2 `a2_mapVirtual_run` shape, generalized from its
  two-buffer controller to the R1 selection);
* **clamps** — both boundary clamps hold with **no nonempty-`y` premise**
  (empty `y`: position `0` is the right boundary, `-1` the left; outward
  moves stay, inward moves cross) — the binding A2/F2 audit contract;
* **halt absorption** — the source's halting action executes before the
  host control dies; later times are fixed;
* **emission policy** — suppressed or forwarded, mirroring R1's two modes
  (open decision 12.4 resolves both at once);
* **time** — exact; **space** — coefficient-one containment: each selected
  tape's host visited set is contained in the source's visited set on `y`
  at the same horizon (the R4 ledger shape, proved in `a2_map_space`).

Permanent regression lemmas (audit-adopted): the zero-time startup
instance, the two empty-`y` clamp instances, and the setup-then-emitting-
halt seam. Generic form of: `a2_mapVirtual*` (A2), `f2_splitCount*` (F2A,
the `y = []` specialization), the universal interpreter's input phase, and
the query simulation every oracle-summit machine will need.

**Z1 rider — the R1 selected-tape exports (decision D-R1, user
2026-10-09, from the retrofit inventories, plan §4d).** The three retrofit
inventories independently identified the same R1 API gap: `Embed.lean`
exports no selected-tape field lemmas (`embedSlot_selected`/`_unselected`
are private) and no agreeing-host lockstep, so no old-code R1 consumer can
be proved from the public surface. This statement phase adds, **additively
in `Embed.lean`** (shared-file mechanism, audited under this gate): public
selected-tape projections of `embedSilentCfg`/`embedEmitCfg` (contents and
head of tape `ι i`), and an `ofWords` transport form. Unlocks the blocked
Hardness families (M/N/AM/U, Z/AB/AG — ≈ 300-350 lines) at the next
retrofit window.

### Z5. Machine-agreement transfer (decision D-R3, user 2026-10-09)

A general lockstep-transfer lemma, the `hagree` genre of
`capture_run`/`emit_run` made standalone: two machines over the same tape
count and state type whose transition tables **agree on a set of states**
run identically, configuration for configuration, from agreeing starts for
as long as the run stays inside the agreement set; a guarded variant takes
the agreement hypothesis per reachable state. Natural home:
`Simulation.lean` beside the existing lockstep gadgets (placement open
decision 13.5: Simulation versus a `Build/` module). Customers (rule of
admission): the Loop forwarding host (H3's 14 verbatim re-proved phase
lemmas, ≈ 550 lines, collapse to one transfer — `emLoopHost` agrees with
`loopHost` on every non-body state); the 13 guarded `clSlot_run` agreement
sites in `CookLevin/Hardness.lean`; every future mode-variant host (the
§12 loop hosts' decision/find/emit triplet is exactly this pattern).
Estimate: ≈ 4 points spec + fill; the risk is quantifier placement on the
agreement set, not proof content.

### Z2. Zoned tape carrier (the Hennie-Stearns representation)

The representation of `m` virtual work tapes on **one** physical tape with
amortizable locality: a `ZoneLayout` (level count `ℓ`; per-level zones
`L_i`/`R_i` of capacity `2^i` around a home origin, [AB09] §1.7) and a
carrier predicate `ZoneCfg` relating one physical word to `m` virtual words
plus per-zone fullness states (empty / half / full). The layer owns:

* **the carrier** — `ZoneCfg` well-formedness, read/write-at-home
  contracts (the virtual heads always sit at the physical origin), and the
  cell-encoding convention (open decision 13.2: how `Option Bool` virtual
  cells embed into binary physical cells — paired-cell presence/data
  tracks, with `SingleTape.lean`'s `SweepCell` encoding as the precedent);
* **the shift routines** — per-level `shiftIn`/`shiftOut` rebalancing
  rows with **exact** costs `O(2^i)`, assembled from R3
  transfer/copy/clear via R2 seams, each with its space row (visited cells
  within the touched zones);
* **the cardinality lemmas** — visited-set bookkeeping for multiplexed
  tapes: physical space bounded by the sum of touched zone extents, the
  piece the Robustness space annotation (Z4) consumes.

Explicitly **on top, not inside**: the `2^i`-fullness invariant across a
run, the amortized `O(T log T)` charge, and the simulation theorem itself —
those are the Hennie-Stearns consumer's mathematics (plan §2.1), as the
§12 precedent kept the loop ledgers out of the loop host. Scope note:
Z2 is sized for the H-S discipline (one zoned tape + one scratch tape);
a general `k`→`k'` conversion is not in scope.

### Z3. Two-work-tape codes (the deterministic `actionBits₂` sibling)

The deterministic code layer currently covers only the one-work-tape
binary normal form (`EffectiveMachineCode`/`UniformMachineCode`,
`Encoding.lean`), which is why Thm 3.1 arrives at `f²` (plan §2.1). Z3
extends it: a deterministic two-work-tape code scheme over the
**same `actionBits₂` record format** as `CodeNDTM` (one branch instead of
two), with the `CodeParser` extension and the `UniformMachineCode`-style
uniform-decoding clause (the P3.2 lesson: variable-code consumers need the
uniformly-timed form). The two-work-tape **universal machine itself** is
the stage-1 consumer build, not part of this layer; Z3 ships the codes it
reads. Space rows on the parser rows from the start.

### Z4. Space annotation for the Robustness conversions (consumer-driven)

Additive `spaceUsed` theorems for the chapter-1 conversions
(`one_work_tape`, the alphabet reduction) via Z2's cardinality lemmas — no
signature changes, the audited surface untouched (the R3 retro-annotation
precedent). This is plan §2.7's fallback route to the space-efficient
universal (Ex 4.1, Thm 4.8). **Design-time obligation, recorded here**: at
the Z1-Z3 spec phase, assess whether the two-work-tape universal carrying
Z1/Z2 space rows yields Ex 4.1 directly; the answer (and hence whether Z4
is needed at all, and at which strength) is recorded before the statement
gate, so the chapter-4 risk register (§6 summit 1) is settled either way.

### Consumers (rule-of-admission check, §4: two named customers per item)

| Item | Customers |
|---|---|
| Z1 virtual-input hosting | the two-work-tape universal (stage 1); the `NP^EXPCOM ⊆ EXP` summit's query simulation; the 12.2c dedup of `a2_mapVirtual*`/`f2_splitCount*`; the P3.3 universal-NDTM fill's code/input discipline |
| Z2 zoned carrier + shifts | the Hennie-Stearns `k`→2 conversion (plan §2.1); the Robustness space annotation (Z4); the Ex 1.6 oblivious sharpening (recorded stretch goal, `Robustness/Oblivious.lean`) |
| Z3 two-work-tape codes | the two-work-tape universal; the Thm 3.1 re-derivation at `f log f` (Hydroxyi's diagonal argument over the new codes) |
| Z4 space annotation | Thm 4.8/Ex 4.1 fallback (plan §2.7); `L ⊊ PSPACE`/space-hierarchy fills (P4.3) if the universal route stalls |

### Placement, sequencing, cost

* New files `Build/VirtualInput.lean` (Z1) and `Build/Zone.lean` (Z2),
  namespace `Turing.FinTM`, order list after `Build/Catalog`; Z3 as a new
  `TuringMachine/Codes2.lean` beside `Encoding.lean` (placement open
  decision 13.3: a new file versus extending `Encoding.lean` — the frozen
  audited surface of `Encoding.lean` argues for the new file); Z4 lands
  additively in the `Robustness/` files through the shared-file mechanism,
  flagged for its own audit.
* Process per `workflow.md`, the §12 precedent verbatim: maintainer-serial
  spec layer (quantifier-sensitive), statement gate by external audit,
  fills as briefed batches with exclusive ownership, epoch-boundary fill
  audit. The gate must close before the H-S/two-tape-universal builds
  start; chapter-3/4 fill briefs written while this layer is open simply
  do not cite it (the EXPCOM brief prefers Z1 only if Z1 is closed).
* Estimate (campaign points): Z1 ≈ 8 (harvest-grade — the lockstep is
  proved four times over; the risk is quantifier hygiene, not proof
  content), Z2 ≈ 14 (genuinely new; the carrier predicate is the risk
  concentration, L-style), Z3 ≈ 6 (format fixed by `actionBits₂`), Z4 ≈ 6
  (retro-annotation against Z2's lemmas). Total ≈ 34, between the §12
  statement layer and one fill epoch.
* **Citation duty** (binding, the 2026-10-06 guideline and the 2026-10-08
  citation-audit row): the design adapts [AB09] §1.7 (Hennie-Stearns) and
  Exercise 1.5/1.6; the §12 duty extends here — Édouard Bonnet's
  lax-434930 `classical-complexity` (Apache-2.0, commit `0c084031…`) is
  cited in this addendum, the module docstrings, and the blueprint entries
  wherever its stack-machine routine catalog informed a row's shape; no
  external code is imported or transcribed.

### Open decisions (13.x, for the user at spec time)

1. **13.1 Zone discipline**: zones-with-fullness (the [AB09] §1.7 layout,
   proposed) versus plain interleaving (simpler carrier, no amortized
   locality — insufficient for H-S alone, but cheaper if Z2's only
   customer were Z4). Proposed: zones; interleaving is not built.
2. **13.2 Cell encoding**: how `Option Bool` virtual cells embed in binary
   physical cells (paired presence/data cells proposed; `SweepCell` as
   precedent).
3. **13.3 Z3 placement**: new `Codes2.lean` (proposed) versus extending
   the frozen `Encoding.lean`.
4. **13.4 Z1 mode shape**: one transformer with an emission-mode parameter
   versus two transformers — inherits open decision 12.4's resolution.
5. **13.5 Z5 placement**: the agreement-transfer lemma in `Simulation.lean`
   beside the lockstep gadgets (proposed) versus a `Build/` module.

### 13a. Decisions resolved; epoch structure (user, 2026-10-09)

All five open decisions resolved as proposed, with one rename:
**13.1** zones-with-fullness (interleaving is not built); **13.2** paired
presence/data cells (`SweepCell` precedent); **13.3** a new file, renamed
**`TuringMachine/Codes2Tape.lean`** so the "2" reads as *two-tape*;
**13.4** Z1 inherits 12.4's resolution (a silent/emit transformer pair over
one shared core); **13.5** Z5 lands in `Simulation.lean`.

**The statement phase runs in two tranches, each with its own gate:**

* **A-S1 — the virtual-input half**: Z5 (the agreement transfer,
  `Simulation.lean`, additive), Z1 (`Build/VirtualInput.lean`, new), and
  the Z1 rider (the R1 selected-tape exports, `Embed.lean`, additive via
  the shared-file mechanism). Rationale: harvest-grade risk (the lockstep
  is proved four times over; the rider's facts are proved privately), and
  its consumers are the *near-term* ones — the blocked retrofit R1
  families, the 12.2c dedup, the Loop H3 collapse, the EXPCOM summit.
* **A-S2 — the zone half**: Z2 (`Build/Zone.lean`), Z3
  (`Codes2Tape.lean`), Z4 (the Robustness space annotation). Rationale:
  Z2's carrier predicate is the genuine design risk and deserves an
  undiluted gate; its consumers (Hennie-Stearns, the two-tape universal)
  sit one stage later. The Z4 design-time obligation (does the two-tape
  universal's space bonus yield Ex 4.1?) is discharged in the A-S2 pack.

The canonical Z1 shape (spec-time refinement, recorded before drafting):
the transformer is defined on exactly `1 + M.k` work tapes — the buffer
first, the payload bank after it — and **relocation is not baked in**:
a consumer needing the buffer or bank elsewhere composes with R1. One
shared hosting core; `silent`/`emit` flavors per 12.4; the tag lives in
the transported control state (the `a2_MapState.run q tag` precedent).

### 13b. A-S1 gate close (2026-10-09, after `audits/vhost-infra-findings.md`)

Round-1 **PASS, 0 blockers / 0 majors / 2 minors**; loop summary
`audits/vhost-infra-resolutions.md`. Minor sweep recorded here per the
audit's proposed fix (A-S1-2): the Z1 rider's promised **`ofWords`
transport form is supplied by specialization** of the four delivered
selected-tape projections (instantiate `c := Cfg.ofWords …`); no
separately named specialization is exported now — if a consumer wants the
whole-configuration identity (with its frame, capture, head, and output
parameters spelled out), it is commissioned on need at the 12.2c window.
A-S1-1 (the pack under-counted the definitions: eight with
`MultiTapeTM.AgreeOn`, 23 audited declarations) is acknowledged as a pack
erratum; shipped packs stay verbatim. The audit's four recommended sanity
exports (initial-tag validity + `q₀`-independence, fixed-parameter
transport injectivity, native-head constancy for arbitrary host
configurations, named boundary/seam specializations) are **adopted as
optional permanent lemmas of the A-S1 fill brief** — offered, not
required. The audit's Z5 composition-of-responsibilities reading is
affirmed and binding on retrofit consumers: Z5 equates runs on one
carrier; heterogeneous `clSlot_run`-style sites first transport
(R1 + state renaming), then agree — a public guarded
configuration-transport theorem is a possible later export, not promised.

### 13c. A-S2 round-1 repairs (2026-10-09, after `audits/zone-infra-findings.md`)

The A-S2 statement gate returned **FAIL: 1 blocker, 1 major, 2 minors**;
repairs landed with the round-2 pack:

* **A-S2-1 (blocker) → the inward room premise removed and the wrappers
  split.** The spec had one shared room hypothesis on both shift
  directions; inward shifts *remove* donor cells, so a full donor — the
  exact classical case — was illegal, and the audit's full-chain family
  showed the delivered interface forcing `Ω(T²)` behavior. Repair:
  `zoneShiftInW` carries no room condition; `zoneShiftOutW`'s receiving
  room moved **inside its guard**; the contents wrappers are the
  hypothesis-free `zoneShiftIn`/`zoneShiftOut`; the head steps gain the
  guarded-total `zoneMove`; and the audit's required gate material landed —
  the full-donor regression (`zoneShiftInW_full_donor`) and the cascade
  statements (`zoneCascadeRight` with its represented-word, length, and
  geometric-cost lemmas), whose proofs adopt the audit's schedule analysis
  as the binding route. The rows now realize the **total guarded
  operation, identity branch included**.
* **A-S2-2 (major) → the Z4 one-tape sketch replaced.** The received
  `sweepTM` grows its window unconditionally (the audit's stationary-head
  scanner refutes it as a witness); the statement stands, and the binding
  route is now a **demand-grown** sweep witness with the audit's
  union-of-origin-intervals bound, interleaving factor, and the
  all-`Γ'`-inputs retraction (empty-alphabet and zero-tape cases named).
* **A-S2-5 (note, adopted) → the Ex 4.1 assessment stands as a
  *design-level* verdict, not an implementation discharge**: the stage-1
  universal must specify a space-accounted input interface (native/suffix
  access or an accounted buffer — a materialized input copy costs
  `Ω(|x|)` work cells, absent from the sketched ledger) and a parser with
  its own space ledger; the uniform scheme (Z3), not an arbitrary
  effective scheme, is what a space-accounted canonizer route would use.
* Minors: the pack's definition count corrected (22, not 25; inventory in
  the findings); the module's export list and the guard semantics
  docstrings corrected in place (A-S2-4).
```

## ===== audits/zone-agent-reports/f1-A2-REPORT.md =====

```
# ZF-A2 — partial delivery and shared-interface escalation

**0/2 machine rows completed. The file remains at 18/20 original targets proved. This is not a zero-sorry delivery and does not close the fill gate.** The inward row was investigated first. Both target proofs remain byte-identical admissions; no statement, existing proof, or attribution was weakened or edited.

This delivery adds the three sanctioned imports and seven proved/private staging declarations (one definition and six lemmas). It stops at the continuation brief's explicit shared-lemma escalation: the public catalog transfer contract does not cover a delimited word at displaced heads inside a larger tape. The exact requested shared contract and a kernel-checked regression are supplied below and in the accompanying Lean evidence files. This is an interface/ownership escalation, **not a counterexample to either existential zone-shift theorem**, and not a claim that the new shared lemma alone would finish a row.

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Received branch: `complexity/arora-barak-ch3-4`.
- Working branch: `fill/zone-f1-A2`.
- Recorded base: `42627f368fef1fbdc5f0c8af777498d26be124bd`.
- Brief's issued base: `f171767f32e573c345f3fa9b6e9fb87e14b84ddf`.
- The received `Zone.lean` is byte-identical at these two bases. The intervening changes issue the continuation briefs and their plan/evidence records.
- No rebase, push, or PR was performed. Final commit: `18c85b42d750b433bf5b00d5408bd8414c211269` (metadata in `commits.log`).

Read: `AGENTS.md`, `policy.md`, `workflow.md`, the complete A2 and A briefs, `audits/zone-agent-reports/f1-A-REPORT.md`, all three zone statement-gate findings files, their resolutions, and the relevant §12 registry and source contracts.

## Changes and freeze

**Sanctioned imports added, explicitly flagged:**

```lean
import TCSlib.Complexity.TuringMachine.Build.Embed
import TCSlib.Complexity.TuringMachine.Build.Seam
import TCSlib.Complexity.TuringMachine.Build.Catalog
```

No other import changes. There are no public docstring/sketch appendices and no optional public exports.

| New private declaration | Role |
|---|---|
| `zoneStageWord` | Encode a zone word in physical order away from home: presence/data on the right, data/presence on the left. |
| `zoneStageWord_length` | The staging word has exactly twice the virtual word's length. |
| `zoneStageWord_getElem` | Identify each staging bit by quotient/remainder of its physical offset. |
| `zoneStageSlot` | Specialize `zoneIndex_eq_iff` to an offset inside a named zone and read its virtual word. |
| `zoneStage_rightWindow` | Relate the right physical window to the staging word, including its blank suffix inside capacity. |
| `zoneStage_leftWindow` | The corresponding negative-coordinate window equation, with the correct reversed bit roles. |
| `zoneStage_window_bounds` | Both oriented windows, including adjacent delimiter cells, fit the target's allowed data interval. |

All seven are complete; no new private admission. The left-window equation is an address/readout fact, not a claimed reflected-machine simulation. An ascending physical transfer on the left would read the reversed staging word and still needs its controller proof.

`freeze.log` establishes a stronger check than signature comparison: remove exactly the three new import lines and the contiguous new private block, and the **entire file equals the recorded base byte-for-byte**. Thus all eighteen proved targets, all nine old private lemmas, both unfinished rows, every public statement, and all old documentation remain unchanged. The only changed tracked path is `TCSlib/Complexity/TuringMachine/Build/Zone.lean`.

## Why canonical transfer is insufficient

The missing premise is not solved by the newly authorized imports:

1. `transferTM_run`, `copyTM_run`, and `clearTM_run` start from `Cfg.ofWords`: heads at zero, native input position 1, and globally canonical `bufferTape` contents on every tape. The transfer/copy rows additionally assume a blank destination word.
2. `embedEmitCfg` and `embedSilentCfg` transplant an entire selected tape unchanged. Their frame clauses protect **unselected tapes**, not the outer cells of a selected tape. At two tapes, the suppressing embedding also has no third capture tape available when both source tapes are selected.
3. `seamCompTM_run_ofCfg` correctly composes arbitrary configurations, but its `h₁` and `h₂` hypotheses already require the constituent framed runs. It does not provide those runs from the canonical catalog theorem.
4. `runFrom_eq_of_agreeOn` compares transition tables on the **same initial configuration**. It supplies neither a change of tape origin nor an initial tape frame.

This is a missing public specialization, not a theorem that no generic simulation argument could ever derive. Building another private catalog trace here would violate the brief's ban on copying/re-deriving that layer. The requested shared theorem should be proved in its shared home by generalizing the existing transfer invariants, once.

The boundary conditions matter even with an enabled inward guard. `BoundaryRegression.lean` constructs a valid three-level carrier with right lengths `(0,4,1)` and a nonempty left level zero. At inward level 1:

- The donor starts at physical cell 6 and occupies eight bits.
- Physical cell 14 belongs to the next outer zone and contains `some true`; it is not a terminating blank.
- Starting bare `transferTM 2 0 1` at data head 6 and a blank scratch head 0 consumes **ten** bits, reaches `done` at time **22**, and erases cell 14.
- The required `zoneShiftIn true 1` preserves cell 14 as `some true`.
- The original data tape cannot equal any `bufferTape w`, because its cell -2 is occupied.

The regression uses exact kernel reduction, not `native_decide`, and does not claim to refute the zone row. It shows why boundary preparation and a framed run proof are necessary. The proposed route saves the boundary symbols in finite control, installs blank delimiters, calls the shared transfer, and restores the symbols. The new window lemmas establish the physical interior and allowable delimiter locations; no preparation controller is claimed complete.

## Requested shared lemmas

**Exactly one request:** add and prove `Turing.transferTM_run_ofCfg` in `Build/Catalog.lean`.

`RequestedSharedLemma.lean` contains the complete proposed type as `requested_transferTM_run_ofCfg : Prop`. It is a **typechecked specification only**, not a theorem or a proof; it contains no `sorry` and adds no axiom. The public theorem should inhabit that proposition (the proposed helper definition need not itself be exported).

Inputs and obligations:

- Distinct source/destination tapes; arbitrary native input, input position, output prefix, inactive tapes, and displaced heads.
- Initial control `some SweepPhase.sweep`.
- A source word agreeing with `bufferTape w` at the source head's relative coordinates from **-1 through `w.length`, inclusive**. Thus both boundary cells really are blank. The destination's old contents are unrestricted because the controller never tests that read component.
- At exactly `2*w.length+2`, control is `some SweepPhase.done`, both touched heads return to their initial coordinates, native position and output are unchanged, the source word interval is erased, the destination word interval is overwritten by `w`, and every cell outside those intervals is unchanged.
- No earlier visit to `done`.
- Through that time each touched head lies in its translated interval `[-1,w.length]`; every other head stays fixed.

The exact final configuration and the two trajectory clauses are included in the supplied type. The translated interval bound yields the per-tape `w.length+2` space bound by the existing interval-cardinality export. The original canonical contract is a specialization with zero heads and globally buffered words; the destination-blank restriction can be reinstated at that specialization.

Mathematical proof route for the shared owner: generalize the existing forward/rewind transfer invariants over the fixed outer frame and starting head coordinates. The forward pass copies the prefix without changing the source; the source's right delimiter turns the heads; the rewind erases only the source interior; the left delimiter supplies the final return step. There are `w.length` forward steps, one turn, `w.length` erase steps, and one entry step. These are proof obligations for the shared owner, not a claimed new Lean proof in this delivery.

## Remaining inward frontier

The requested shared lemma removes the **first staging-interface gap**. It does not supply the rest of the witness:

1. A single finite controller must preserve the unary level while constructing and using the anchored binary navigation counter, with the audited geometric carry/borrow sum. No level may be compiled into control.
2. Locate the windows, evaluate the inward guard, save/blank/restore boundary symbols, stage and rewrite the prefix/suffix, and prove the identity branch including arbitrary outer contents.
3. Compose the proved phase runs by `seamCompTM_run_ofCfg`, transport their cuts and visited sets, restore scratch to the exact unary buffer, and return both heads.
4. End with an explicitly halting phase, derive the first-halt cut, and choose one coefficient for time and scratch space.

Two source-level cautions for that continuation:

- `incrementTM_run_succ` exposes the loose `2*width+2` bound. Its docstring describes the sharper carry-sensitive cost, but the public theorem does not state it. Repeating the loose bound alone would give a width factor and does not prove the audited geometric navigation ledger. No additional shared theorem is requested in this delivery; that cost proof remains an explicit obligation.
- The continuation table's phrase “release to genuine halt” is not what `seamReleaseTM` does. It executes the original anchor action from a fresh entry state and subsequently runs the original machine. `seamReleaseTM_firstReturn` returns to a **live** anchor. A terminal halt must be supplied explicitly; the table was guidance, so no statement was altered to match it.

The outward row was not started, respecting the inward-first priority.

## Duplication ledger and citations

new copies: none

There is no local catalog controller, trace, transfer proof, embedding proof, seam proof, loop host, or primitive copy. The additions are zone-specific codec/address facts. Public declaration count remains 38; private count rises from 9 to 16. No completed machine phase is claimed to consume §12 contracts.

| Intended phase | Exact shared citations and present status |
|---|---|
| Delimited staging | `transferTM_run` / `transferTM_spaceUsedByTape`: inspected, canonical forms insufficient; first request is `transferTM_run_ofCfg`. |
| Additional copy/cleanup if selected | `copyTM_run`, `copyTM_spaceUsedByTape`, `clearTM_run`, `clearTM_spaceUsedByTape`: inspected; their framed applicability must likewise be established, not presumed. The current request does not claim to resolve all such future choices. |
| Host tape selection | `embedEmitTM_runFrom`, `embedEmitTM_frame`, `embedEmitTM_visitedByTapeHead`; returning variant `embedEmitRetTM_run` / `embedEmitRetTM_visitedByTapeHead` only for genuinely halting source phases. No spatial-frame conclusion is attributed to them. |
| General sequencing | `seamCompTM_run_ofCfg`, `seamCompTM_firstReturn_ofCfg`, `seamCompTM_visitedByTapeHead_ofCfg`: applicable after phase contracts exist. |
| Fresh-entry positive-return control | `seamReleaseTM_firstReturn`, `seamReleaseTM_visitedByTapeHead`: available for their actual live-return purpose, not as an implicit halting adapter. |

## Verification and archive

Verification results are finalized in `verification-summary.txt`. All Lean checks use the unmodified `scripts/lean_check_tree.sh`; no `lake build` was run. `lake exe cache get` succeeded with the manifest-pinned dependencies. A fresh, dependency-ordered sweep covers the standard order list and the five prescribed Build modules; additional actual import prerequisites are included rather than assumed present.

The twenty target axiom prints are in `axioms.log`. The eighteen integrated targets remain within `[propext, Classical.choice, Quot.sound]`; the two unfilled rows deliberately still carry `sorryAx`. All seven new staging declarations and all five boundary regression facts are checked separately and use only the standard triple. No proof of the requested shared specification is included or claimed.

Style: `style_lint: 0 FAIL, 4 WARN over 11 files`. The `Zone.lean` size warning (now 1,191 lines) is covered by the plan decision-log entry “A-S2 fill epoch: ZF-A and ZF-C partials INTEGRATED; ZF-B received and HELD”: this single owned audited surface remains together until the 12.2c split window. The other three size warnings are received files.

The archive contains the full `Zone.lean`, report, patch series against the recorded base, incremental git bundle, final sweep and axiom logs, freeze and integration evidence, the two Lean escalation evidence files, and `SHA256SUMS`. Only `Zone.lean` is changed by the patch; evidence files are not repository contributions. No compatibility shim, toolchain executable, dependency cache, or build output is delivered.

Notation: `w` is the proposed transfer's finite Boolean word; `d` its arbitrary starting configuration; `p` a relative integer cell offset; `T = 2*w.length+2` its proposed exact phase time. Other names are existing source identifiers or listed private additions.
```

## ===== audits/evidence/zone-f1-A2/RequestedSharedLemma.lean.txt =====

```
import TCSlib.Complexity.TuringMachine.Build.Catalog

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Turing

/-- Proposed shared theorem type, deliberately a Prop-valued definition.
This file checks the interface, not its truth; no proof is claimed.
The requested home is Build/Catalog.lean, name transferTM_run_ofCfg. -/
def requested_transferTM_run_ofCfg : Prop :=
  ∀ {k : ℕ} {x : List Bool} (src dst : Fin k), src ≠ dst →
  ∀ (w : List Bool) (d : Cfg k Bool SweepPhase x),
    d.state = some SweepPhase.sweep →
    (∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      d.workTapes src (d.workTapePos src + p) = FinTM.bufferTape w p) →
    let T := 2 * w.length + 2
    let finish : Cfg k Bool SweepPhase x :=
      { d with
        state := some SweepPhase.done
        workTapes := fun j p =>
          if j = src then
            if d.workTapePos j ≤ p ∧ p < d.workTapePos j + (w.length : ℤ)
              then none else d.workTapes j p
          else if j = dst then
            if d.workTapePos j ≤ p ∧ p < d.workTapePos j + (w.length : ℤ)
              then FinTM.bufferTape w (p - d.workTapePos j)
              else d.workTapes j p
          else d.workTapes j p }
    (transferTM k src dst).runFrom d T = finish ∧
    (∀ t < T, ((transferTM k src dst).runFrom d t).state ≠
      some SweepPhase.done) ∧
    (∀ (j : Fin k) (t : ℕ), t ≤ T →
      if j = src ∨ j = dst then
        ((transferTM k src dst).runFrom d t).workTapePos j ∈
          Finset.Icc (d.workTapePos j - 1) (d.workTapePos j + (w.length : ℤ))
      else ((transferTM k src dst).runFrom d t).workTapePos j = d.workTapePos j)

#check requested_transferTM_run_ofCfg
#print axioms requested_transferTM_run_ofCfg

end Turing
```

## ===== audits/evidence/zone-f1-A2/BoundaryRegression.lean.txt =====

```
import TCSlib.Complexity.TuringMachine.Build.Zone

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace ZFA2BoundaryRegression
open Turing

/-- Valid level-1 inward input: empty lower right zone, full donor,
occupied outer zone. The nonempty left zone also prevents a canonical
bufferTape representation of the whole data tape. -/
def z : ZoneContents 3 where
  home := none
  left := fun j => if j.val = 0 then [some true] else []
  right := fun j => if j.val = 1 then List.replicate 4 none
    else if j.val = 2 then [some true] else []
  left_le := of_decide_eq_true rfl
  right_le := of_decide_eq_true rfl

/-- The legitimate inward operation has an enabled guard. -/
theorem inward_guard : z.right 0 = [] ∧ (z.right 1).length = zoneCapacity 1 :=
  of_decide_eq_true rfl

/-- The full donor starts at 6, occupies eight bits, and is followed by
occupied outer data at 14. A bare transfer has no delimiter there. -/
theorem donor_boundary :
    2 * zoneBase 1 + 2 = 6 ∧ zoneTape z 14 = some true :=
  of_decide_eq_true rfl

/-- A displaced transfer with no boundary preparation. -/
def start : Cfg 2 Bool SweepPhase ([] : List Bool) :=
  ⟨some .sweep, 1,
    (fun j => if j.val = 0 then zoneTape z else FinTM.bufferTape []),
    (fun j => if j.val = 0 then 6 else 0), []⟩

/-- The unprepared transfer consumes ten bits, including the outer pair;
it returns at time 22 and has erased the outer presence cell. -/
theorem unprepared_transfer :
    ((transferTM 2 0 1).runFrom start 22).state = some .done ∧
    ((transferTM 2 0 1).runFrom start 22).workTapePos 0 = 6 ∧
    ((transferTM 2 0 1).runFrom start 22).workTapePos 1 = 0 ∧
    ((transferTM 2 0 1).runFrom start 22).workTapes 0 14 = none :=
  of_decide_eq_true rfl

/-- The required inward operation preserves that outer cell. -/
theorem required_outer_frame :
    zoneTape (zoneShiftIn true 1 z) 14 = some true :=
  of_decide_eq_true rfl

/-- No canonical word can equal this whole data tape: cell -2 is occupied. -/
theorem not_canonical (w : List Bool) : zoneTape z ≠ FinTM.bufferTape w := by
  intro h
  have hc := congrFun h (-2)
  have hz : zoneTape z (-2) = some true := of_decide_eq_true rfl
  rw [hz] at hc
  simpa [FinTM.bufferTape] using hc

#print axioms inward_guard
#print axioms donor_boundary
#print axioms unprepared_transfer
#print axioms required_outer_frame
#print axioms not_canonical

end ZFA2BoundaryRegression
```

## ===== audits/evidence/s12-framed/FramedSanity.lean.txt =====

```
import TCSlib.Complexity.TuringMachine.Build.Catalog
open Turing

def frameCfg {S : Type} (q : S) (w : List Bool) (h0 h1 : ℤ) : Cfg 2 Bool S [true, false] :=
  { Cfg.ofWords (input := [true, false]) q (fun (_ : Fin 2) => ([] : List Bool)) with
    workTapes := fun j p =>
      if j.val = 0 then
        (if h0 - 1 ≤ p ∧ p ≤ h0 + w.length then FinTM.bufferTape w (p - h0) else some true)
      else (if p % 3 = 0 then some false else if p % 3 = 1 then some true else none)
    workTapePos := fun j => if j.val = 0 then h0 else h1 }

def cells {S : Type} (c : Cfg 2 Bool S [true, false]) : List (List (Option Bool)) :=
  [ (List.range 30).map (fun n => c.workTapes 0 ((n : ℤ) - 10)),
    (List.range 30).map (fun n => c.workTapes 1 ((n : ℤ) - 10)) ]

def finCopy (d : Cfg 2 Bool SweepPhase [true,false]) (w : List Bool) : Cfg 2 Bool SweepPhase [true,false] :=
  { d with state := some SweepPhase.done,
           workTapes := fun j q =>
            if j = 1 ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ)
              then FinTM.bufferTape w (q - d.workTapePos j) else d.workTapes j q }
def finClear (d : Cfg 2 Bool SweepPhase [true,false]) (w : List Bool) : Cfg 2 Bool SweepPhase [true,false] :=
  { d with state := some SweepPhase.done,
           workTapes := fun j q =>
            if j = 0 ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ)
              then none else d.workTapes j q }
def finInc (d : Cfg 2 Bool FlagPhase [true,false]) (flag : Bool) (len : ℕ) (v : List Bool) : Cfg 2 Bool FlagPhase [true,false] :=
  { d with state := some (FlagPhase.done flag),
           workTapes := fun j q =>
            if j = 0 ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (len : ℤ)
              then FinTM.bufferTape v (q - d.workTapePos j) else d.workTapes j q }

def sweepOK {S : Type} [DecidableEq S] (M : MultiTapeTM 2 Bool S) (d f : Cfg 2 Bool S [true,false])
    (T : ℕ) (bad : Option S → Bool) (lo0 hi0 lo1 hi1 : ℤ) : Bool :=
  let r := M.runFrom d T
  decide (r.state = f.state) && decide (cells r = cells f) && decide (r.workTapePos 0 = f.workTapePos 0)
    && decide (r.workTapePos 1 = f.workTapePos 1) && decide (r.inputPos = f.inputPos) && decide (r.output = f.output)
    && (List.range T).all (fun t => !bad (M.runFrom d t).state)
    && (List.range (T+1)).all (fun t => let c := M.runFrom d t
          decide (lo0 ≤ c.workTapePos 0 ∧ c.workTapePos 0 ≤ hi0 ∧ lo1 ≤ c.workTapePos 1 ∧ c.workTapePos 1 ≤ hi1))

def checkCopy (w : List Bool) (h0 h1 : ℤ) : Bool :=
  let d := frameCfg SweepPhase.sweep w h0 h1
  sweepOK (copyTM 2 0 1) d (finCopy d w) (2 * w.length + 2) (fun s => decide (s = some SweepPhase.done))
    (h0 - 1) (h0 + w.length) (h1 - 1) (h1 + w.length)
def checkClear (w : List Bool) (h0 h1 : ℤ) : Bool :=
  let d := frameCfg SweepPhase.sweep w h0 h1
  sweepOK (clearTM 2 0) d (finClear d w) (2 * w.length + 2) (fun s => decide (s = some SweepPhase.done))
    (h0 - 1) (h0 + w.length) h1 h1
def doneAny (s : Option FlagPhase) : Bool := decide (s = some (FlagPhase.done true)) || decide (s = some (FlagPhase.done false))
def checkInc (w : List Bool) (h0 h1 : ℤ) : Bool :=
  let d := frameCfg FlagPhase.run w h0 h1
  match incFixed w with
  | some v => let p := (w.takeWhile id).length
      sweepOK (incrementTM 2 0) d (finInc d true w.length v) (2 * p + 2) doneAny (h0 - 1) (h0 + p) h1 h1
  | none => sweepOK (incrementTM 2 0) d (finInc d false w.length (List.replicate w.length false))
      (2 * w.length + 2) doneAny (h0 - 1) (h0 + w.length) h1 h1


def finTransfer (d : Cfg 2 Bool SweepPhase [true,false]) (w : List Bool) : Cfg 2 Bool SweepPhase [true,false] :=
  { d with state := some SweepPhase.done,
           workTapes := fun j q =>
            if j = 0 ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ) then none
            else if j = 1 ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ)
              then FinTM.bufferTape w (q - d.workTapePos j)
            else d.workTapes j q }
def checkTransfer (w : List Bool) (h0 h1 : ℤ) : Bool :=
  let d := frameCfg SweepPhase.sweep w h0 h1
  sweepOK (transferTM 2 0 1) d (finTransfer d w) (2 * w.length + 2) (fun s => decide (s = some SweepPhase.done))
    (h0 - 1) (h0 + w.length) (h1 - 1) (h1 + w.length)

def words : List (List Bool) := [[], [true], [false], [true,false,true], [true,true,true], [false,true,true,false], [true,true,false,true]]
#eval (words.map (fun w => checkTransfer w 3 (-2) && checkTransfer w (-4) 5)).all id
#eval (words.map (fun w => checkCopy w 3 (-2) && checkCopy w 0 0 && checkCopy w (-4) 6)).all id
#eval (words.map (fun w => checkClear w 3 (-2) && checkClear w (-5) 7)).all id
#eval (words.map (fun w => checkInc w 3 (-2) && checkInc w (-3) 4)).all id
-- negative control: the harness must reject a wrong time
#eval (let w := [true,false,true]; let d := frameCfg SweepPhase.sweep w 3 (-2)
       sweepOK (copyTM 2 0 1) d (finCopy d w) (2 * w.length + 1) (fun s => decide (s = some SweepPhase.done)) 2 6 (-3) 1)
```

## ===== audits/evidence/s12-framed/results.txt =====

```
# Execution check of the five framed contracts (design §12.6): the statements are sorried; the machines are evaluated.
# Run: LEAN_PATH=<scratch oleans + packages> lean FramedSanity.lean  (file stored with a .txt suffix so it is never built)
# Output, in order: transfer, copy, clear, increment, negative control
true
true
true
true
false
# transfer 14/14, copy 21/21, clear 14/14, increment 14/14 (success and overflow branches); the negative control (copy at time 2|w|+1) is correctly rejected.
```

## ===== TCSlib/Complexity/TuringMachine/Configuration.lean =====

```
/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Aviv Bar Natan

Vendored from cslib (https://github.com/leanprover/cslib), file
`Cslib/Computability/Machines/Turing/MultiTape/Configuration.lean`,
at commit a374775894efb9b7196cccf11235c60a97086dc1 (2026-09-14).
Local modifications (see policy.md §2, vendored code):
* removed the Lean module-system syntax (`module`, `public import`, `@[expose] public section`)
  for compatibility with our v4.25.0 toolchain;
* remapped `Mathlib.Basic.Sign.Defs` to its location at our mathlib pin,
  `Mathlib.Data.Sign.Defs`; dropped the cslib-internal `Cslib.Init` import;
* added the repository-standard `set_option` header.
The mathematical content is unchanged.
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Finset.Max
import Mathlib.Data.Int.Interval
import Mathlib.Data.Sign.Defs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Configurations of Multi-Tape Turing Machines

Configurations of a multi-tape Turing machine with a read-only input tape, `k` work tapes and one
write-only output tape, together with what a single transition does to one and the space measure
read off a list of them.

## Design

Nothing here mentions a machine. A step is described in two parts: an `Action`, recording
which way the input head moves, what is written and where the work heads move, which symbol is
emitted and which state follows; and `Action.apply`, which carries it out on a
configuration.

The output tape is part of the configuration, so the string emitted along a run can be read off
the configuration the run ends in.

## Main definitions

* `Cfg`: the configuration: the internal state, the tape contents and head positions, and the
    output tape
* `Action`: what a machine does in one step
* `Action.apply`: the effect of one action on a configuration
* `Cfg.Halted`, `Cfg.init`: halting, and the configuration a machine starts in
* `spaceUsedOfCfgs`: work tape cells touched along a list of configurations

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2: the k-tape Turing machine.)
* [Pap94] C. Papadimitriou, *Computational Complexity*, Addison-Wesley, 1994.
  (§2.3, §2.5: the machine model and the space measure.)
-/

namespace Turing

variable {k : ℕ} {State Symbol : Type*} {input : List Symbol}

/-- What a machine does in one step. -/
structure Action (k : ℕ) (Symbol State : Type*) where
  /-- The movement (attempt) of the input head. -/
  inputTape : SignType
  /-- Actions on the work tapes: optionally a symbol to write and the head movement. -/
  workTapes : Fin k → (Option (Option Symbol)) × SignType
  /-- An optional symbol to output. -/
  output : Option Symbol
  /-- The successor state or none to halt. -/
  state : Option State

/--
The configurations of a Turing machine is relative to the input of the machine and consist of:
- an `Option`al state (or none for the halting state),
- the position of the input head (shifted by one),
- the contents of the work tape,
- the positions of the work tape heads,
- the contents of the write-only output tape
-/
@[ext]
structure Cfg (k : ℕ) (Symbol State : Type*) (input : List Symbol) where
  /-- the state of the TM (or none for the halting state) -/
  state : Option State
  /-- the position of the input head, shifted by one -/
  inputPos : Fin (input.length + 2)
  /-- the work tapes -/
  workTapes : Fin k → ℤ → Option Symbol
  /-- the positions of the heads on the work tapes -/
  workTapePos : Fin k → ℤ
  /-- the contents of the write-only output tape -/
  output : List Symbol
deriving Inhabited

/-- Two configurations of a machine without work tapes are equal if their states, input head
positions and outputs are equal. -/
lemma Cfg.ext_zero_tapes {Symbol State : Type*} {input : List Symbol}
    {cfg₁ cfg₂ : Cfg 0 Symbol State input} (state : cfg₁.state = cfg₂.state)
    (inputPos : cfg₁.inputPos = cfg₂.inputPos) (output : cfg₁.output = cfg₂.output) :
    cfg₁ = cfg₂ :=
  Cfg.ext state inputPos (funext fun i => i.elim0) (funext fun i => i.elim0) output

/-- Attempt to move the input tape head.
The machine can only read one empty cell outside of the input,
any attempted movement beyond that results in no movement.

The addition is performed in `ℤ` before clamping. Performing it in `Fin (n + 2)` would wrap an
outward boundary move to the opposite end of the input. -/
@[scoped grind =]
def moveInputPos {n : ℕ} (pos : Fin (n + 2)) (m : SignType) : Fin (n + 2) :=
  let p := ((pos.val : ℤ) + (m.cast : ℤ)).toNat
  if h : p < n + 2 then ⟨p, h⟩ else ⟨n + 1, by omega⟩

@[simp]
lemma moveInputPos_zero {n : ℕ} (pos : Fin (n + 2)) :
    moveInputPos pos 0 = pos := by
  apply Fin.ext
  simp [moveInputPos, pos.isLt]

@[simp]
lemma moveInputPos_leftBoundary {n : ℕ} :
    moveInputPos (0 : Fin (n + 2)) (-1) = 0 := by
  apply Fin.ext
  simp [moveInputPos]

@[simp]
lemma moveInputPos_rightBoundary {n : ℕ} :
    moveInputPos (⟨n + 1, by omega⟩ : Fin (n + 2)) 1 = ⟨n + 1, by omega⟩ := by
  -- ported proof: `dite_eq_right` does not exist at our mathlib pin
  apply Fin.ext
  simp only [moveInputPos, SignType.coe_one]
  split <;> simp <;> omega

/-- A left move away from the left input boundary decrements the native input position. -/
lemma moveInputPos_neg_of_ne_left {n : ℕ} (p : Fin (n + 2)) (h : p ≠ 0) :
    moveInputPos p .neg = ⟨p.val - 1, by have := p.isLt; omega⟩ := by
  -- ported proof: `dite_eq_left` does not exist at our mathlib pin
  have hlt := p.isLt
  apply Fin.ext
  simp only [moveInputPos, SignType.neg_eq_neg_one, SignType.coe_neg_one]
  split <;> simp <;> omega

/-- A right move away from the right input boundary increments the native input position. -/
lemma moveInputPos_pos_of_ne_right {n : ℕ} (p : Fin (n + 2)) (h : p.val ≠ n + 1) :
    moveInputPos p .pos = ⟨p.val + 1, by have := p.isLt; omega⟩ := by
  -- ported proof: `dite_eq_left` does not exist at our mathlib pin
  have hlt := p.isLt
  apply Fin.ext
  simp only [moveInputPos, SignType.pos_eq_one, SignType.coe_one]
  split <;> simp <;> omega

/-- The symbol currently under the input tape head. -/
def Cfg.inputSymbol (cfg : Cfg k Symbol State input) : Option Symbol :=
  if h₁ : cfg.inputPos = 0 then none
  else if h₂ : cfg.inputPos = input.length + 1 then none
  else input[cfg.inputPos.val - 1]'(by
    -- ported proof: `grind` at our pin does not bridge the `Fin` equality with `.val`
    have h0 : (cfg.inputPos : ℕ) ≠ 0 := fun hv => h₁ (Fin.val_eq_zero_iff.mp hv)
    have hlt := cfg.inputPos.isLt
    omega)

@[simp]
lemma inputSymbolInner {cfg : Cfg k Symbol State input} (p : ℕ)
    (h₁ : cfg.inputPos.val = 1 + p)
    (h₂ : p < input.length) :
    cfg.inputSymbol = some input[p] := by
  -- ported proof: `grind` at our pin does not bridge the `Fin` equality with `.val`
  have h0 : ¬cfg.inputPos = 0 := fun hz => by
    rw [hz] at h₁
    simp at h₁
    omega
  have hL : ¬(cfg.inputPos : ℕ) = input.length + 1 := by omega
  simp only [Cfg.inputSymbol, dif_neg h0, dif_neg hL]
  simp only [show (cfg.inputPos : ℕ) - 1 = p from by omega]

/-- The symbol read by work tape `i`. -/
def Cfg.workTapeSymbols (cfg : Cfg k Symbol State input) (i : Fin k) : Option Symbol :=
  cfg.workTapes i (cfg.workTapePos i)

/-- A configuration is halted when it has no state to continue from. -/
abbrev Cfg.Halted (cfg : Cfg k Symbol State input) : Prop := cfg.state = none

/-- The initial configuration for a starting state and an input string. -/
@[simp]
def Cfg.init (q₀ : State) (input : List Symbol) : Cfg k Symbol State input :=
  ⟨some q₀, 1, fun _ _ => none, fun _ => 0, []⟩

/--
The effect of an action on a configuration: move the input head, write and move on the work tapes,
append the emitted symbol to the output tape, and go to the successor state. This is the part of a
step that does not depend on how the action was chosen.
-/
@[simp]
def Action.apply (action : Action k Symbol State) (cfg : Cfg k Symbol State input) :
    Cfg k Symbol State input where
  state := action.state
  inputPos := moveInputPos cfg.inputPos action.inputTape
  workTapes i := match (action.workTapes i).1 with
    | none => cfg.workTapes i
    | some s => Function.update (cfg.workTapes i) (cfg.workTapePos i) s
  workTapePos i := cfg.workTapePos i + (action.workTapes i).2
  output := cfg.output ++ action.output.toList

/-- A work tape head moves by at most one cell when an action is applied. -/
lemma workTapePos_apply_le (action : Action k Symbol State)
    (cfg : Cfg k Symbol State input) (i : Fin k) :
    |(action.apply cfg).workTapePos i - cfg.workTapePos i| ≤ 1 := by
  simp only [Action.apply, add_sub_cancel_left, abs_le, SignType.cast]
  grind

/-- The work tape cells visited by the head of tape `i` along a list of configurations. -/
def visitedOfCfgs (cfgs : List (Cfg k Symbol State input)) (i : Fin k) : Finset ℤ :=
  (cfgs.map (·.workTapePos i)).toFinset

/-- The number of work tape cells touched by the heads along a list of configurations. -/
def spaceUsedOfCfgs (cfgs : List (Cfg k Symbol State input)) : ℕ :=
  ∑ i, (visitedOfCfgs cfgs i).card

end Turing
```

## ===== TCSlib/Complexity/TuringMachine/Deterministic.lean =====

```
/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger

Vendored from cslib (https://github.com/leanprover/cslib), file
`Cslib/Computability/Machines/Turing/MultiTape/Deterministic.lean`,
at commit a374775894efb9b7196cccf11235c60a97086dc1 (2026-09-14).
Local modifications (see policy.md §2, vendored code):
* removed the Lean module-system syntax (`module`, `public import`, `@[expose] public section`)
  for compatibility with our v4.25.0 toolchain;
* remapped `Mathlib.Basic.Sign.Defs` to `Mathlib.Data.Sign.Defs` (its location at our mathlib
  pin); dropped the cslib-internal `Cslib.Init` import; added
  `Mathlib.Logic.Embedding.Basic` explicitly (upstream receives it transitively);
* dropped the relational semantics (`TransitionRelation`,
  `relatesInSteps_iff_runFrom_eq`) because it depends on the cslib-internal
  `Cslib.Foundations.Data.RelatesInSteps`; the iterated-step semantics `runFrom` is
  self-contained and suffices for the Chapter 1 development. Re-add it (or migrate to
  upstream cslib) when the step-indexed relational view is needed, e.g. for
  nondeterministic machines;
* added the repository-standard `set_option` header;
* corrected the module docstring's attribution of the non-blank space measure
  ([AB09, Def 4.1] counts visited cells for `SPACE`, non-blank cells only for
  `NSPACE`); comments only, no code change (2026-10-08).
The remaining mathematical content is unchanged.
-/
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Sign.Defs
import Mathlib.Logic.Embedding.Basic
import TCSlib.Complexity.TuringMachine.Configuration

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Deterministic Multi-Tape Turing Machines

Defines deterministic Turing machines with a read-only input tape, `k` work tapes and one
write-only output tape.
The tapes contain symbols from `Option Symbol` for a finite alphabet `Symbol` (where `none` is the
blank symbol).

## Design

The multi-tape Turing machine uses a read-only input tape, `k` work tapes and a write-only output
tape.
The input head can move freely on the input, but any move attempt beyond one cell outside the input
results in no movement.
The transition function can optionally output one symbol, which models the write-only output tape.
Because of these restrictions, we ignore the input and output tapes for space usage of the machine.
The space usage is defined as the total number of cells the work tape heads visited during
execution.

Restricting the movement of the input head is not essential, but useful because it allows
us to easily bound the number of possible configurations of a space-bounded machine. Most textbooks
have this restriction.

Instead of considering the cells _visited_ by the work tape heads, some textbooks
only consider the number of cells that contain a non-blank symbol at some point in the
execution or the number of cells written to. ([AB09] itself splits: Definition 4.1 counts
_visited_ work-tape locations for `SPACE` — the measure used here — but _nonblank_
locations for `NSPACE`.) This allows
work tape heads to freely move at no cost as long as they do not write. It is
important to note that this causes `DSPACE(1)` to include `DSPACE(log log n)`, a class that
contains e.g. the non-regular language `{0^n 1^n | n ∈ ℕ}` (it is accepted by a TM that writes a
single marker on the work tape and then counts the number of symbols by work tape head movement
without writing).
Defining space usage via "cells visited" thus yields the more fine-grained "complexity world" in
which `DSPACE(1)` is exactly the class of regular languages.

This definition is adapted from the one in [Pap94], chapter 2.3 including
the sub-linear space modifications from chapter 2.5 with the following changes:
- We allow Turing machines to choose to not write on a tape. This is equivalent to
  writing the read symbol again but makes it easier to reason about the semantics.
- Our tapes are infinite in both directions instead of just to the right. This definition is
  equivalent (see [AB09], Claim 1.8). It saves us from having to add a "start marker" to
  the alphabet.
- We only have a single halting state. The different ways to halt (accepting, rejecting, etc) can
  be distinguished based on the output.
- The way to prevent the input head to move outside the input is enforced by the interpretation
  and not by a restriction on the transition function. The two definitions are equivalent, but
  not restricting the transition function makes it easier to define a universal machine.

## Main definitions

We define a number of structures and concepts related to multi-tape Turing machine computation:

* `MultiTapeTM`: the TM itself
* `MultiTapeTM.runFrom`: the configuration reached after a given number of execution steps
* `spaceUsed`: the number of work tape cells touched by the heads until a certain step,
    our main space measure
* `ComputesInTimeAndSpace`: a proof that a specific TM computes an output from an input in a certain
    number of steps and using a certain number of tape cells
* `ComputesFunInTimeAndSpace`: a machine computes a function between specified encodings,
    respecting time and space bounds on each actual input.
* `ComputableInTimeAndSpace`: such a machine exists with binary alphabet and finitely many states.
* `ComputableInTimeAndSpaceOfLength`: the specialization to bounds on encoded input length.
* `DecidableInTimeAndSpace`: a proof that a TM decides a language within a certain time
    and space bound.

## References

* [Pap94] C. Papadimitriou, *Computational Complexity*, Addison-Wesley, 1994.
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
* [Sip13] M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage, 2013.
-/

namespace Turing

variable {k : ℕ} {State Symbol : Type*}

/--
A multi-tape Turing machine with `k` work tapes over the alphabet of `Option Symbol` (where `none`
is the blank tape symbol). Note that it is not required that `Symbol` or `State` are finite
to keep the definition more general. The restriction will be introduced once we start talking about
computability by Turing machines in general.
-/
structure MultiTapeTM (k : ℕ) (Symbol State : Type*) where
  /-- initial state -/
  q₀ : State
  /-- transition function, mapping a state, the current input symbol and a tuple of work head
  symbols to a movement for the input head, actions on the work tape, optionally a symbol to output
  and the successor state -/
  tr (q : State) (input : Option Symbol) (work : Fin k → Option Symbol) :
    Action k Symbol State

namespace MultiTapeTM

variable {input : List Symbol} {tm : MultiTapeTM k Symbol State}

section Cfg

/-!
## Stepping a Turing Machine

This section defines the step function that lets the machine transition from one configuration to
the next, and the configuration reached after a number of steps. Configurations themselves are
defined in `TCSlib.Complexity.TuringMachine.Configuration`.
-/

/-- The step function corresponding to a `MultiTapeTM`. -/
def step (cfg : Cfg k Symbol State input) : Cfg k Symbol State input :=
  match cfg.state with
  -- in the halting state, we stay at the configuration
  | none => cfg
  | some q => (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).apply cfg

/-- The symbol (optionally) output when executing one step starting from configuration `cfg`. -/
def outputSymbol (cfg : Cfg k Symbol State input) : Option Symbol :=
  match cfg.state with
  | none => none
  | some q => (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).output

/-- The initial configuration corresponding to an input string. -/
@[simp]
def initCfg (input : List Symbol) : Cfg k Symbol State input := Cfg.init tm.q₀ input

@[simp]
lemma step_of_halt {cfg : Cfg k Symbol State input} (h : cfg.state = none) :
    tm.step cfg = cfg := by
  unfold step
  rw [h]

/-- The configuration reached by running the Turing machine for `t` steps from `cfg`.
If the Turing machine halts, it will stay at the halting configuration. -/
def runFrom (cfg : Cfg k Symbol State input) (t : ℕ) : Cfg k Symbol State input := tm.step^[t] cfg

@[simp]
lemma runFrom_zero {cfg : Cfg k Symbol State input} :
    tm.runFrom cfg 0 = cfg := by
  simp [runFrom]

lemma runFrom_succ_eq_step {cfg : Cfg k Symbol State input} {t : ℕ} :
    tm.runFrom cfg (t + 1) = tm.runFrom (tm.step cfg) t := by
  simp [runFrom, Function.iterate_succ_apply]

lemma runFrom_succ_eq_step' {cfg : Cfg k Symbol State input} {t : ℕ} :
    tm.runFrom cfg (t + 1) = tm.step (tm.runFrom cfg t) := by
  simp [runFrom, Function.iterate_succ_apply']

/-- Running `a + b` steps equals running `b` steps from the configuration reached after `a`. -/
lemma runFrom_add (cfg : Cfg k Symbol State input) (a b : ℕ) :
    tm.runFrom cfg (a + b) = tm.runFrom (tm.runFrom cfg a) b := by
  unfold runFrom
  rw [Nat.add_comm, Function.iterate_add_apply]

/-- The physical input head can move right by at most one cell per step.
**Proof sketch.** Clamping never increases a proposed position. Check the
three movements, then induct over the run, treating halted steps as stationary. -/
lemma timed_input_bound (cfg : Cfg k Symbol State input) (t : ℕ) :
    (tm.runFrom cfg t).inputPos.val ≤ cfg.inputPos.val + t := by
  have hm (p : Fin (input.length + 2)) (m : SignType) :
      (moveInputPos p m).val ≤ p.val + 1 := by
    dsimp only [moveInputPos]
    split <;> dsimp <;> cases m <;> simp_all [SignType.cast] <;> omega
  have hstep (d : Cfg k Symbol State input) :
      (tm.step d).inputPos.val ≤ d.inputPos.val + 1 := by
    cases hs : d.state with
    | none => simp only [MultiTapeTM.step, hs]; omega
    | some q =>
      simpa only [MultiTapeTM.step, hs, Action.apply] using
        hm d.inputPos (tm.tr q d.inputSymbol d.workTapeSymbols).inputTape
  induction t with
  | zero => simp
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step']
    exact (hstep _).trans (by omega)

/-- If a function `f` that maps the configurations of one TM to those of another one commutes with
their `step` function, then it also commutes with their `runFrom` function. -/
lemma runFrom_comm_of_step {k' : ℕ} {State' : Type*} {input input' : List Symbol}
    {tm : MultiTapeTM k Symbol State} {tm' : MultiTapeTM k' Symbol State'}
    (f : Cfg k Symbol State input → Cfg k' Symbol State' input')
    (hstep : ∀ cfg, tm'.step (f cfg) = f (tm.step cfg))
    (cfg : Cfg k Symbol State input) (n : ℕ) :
    tm'.runFrom (f cfg) n = f (tm.runFrom cfg n) :=
  (Function.Semiconj.iterate_right (fun c => (hstep c).symm) n cfg).symm

/-- Running from a halting configuration stays at that configuration. -/
@[simp]
lemma runFrom_of_halt (cfg : Cfg k Symbol State input) (h : cfg.state = none) {n : ℕ} :
    tm.runFrom cfg n = cfg :=
  Function.iterate_fixed (step_of_halt h) n

@[simp]
lemma outputSymbol_of_halt {cfg : Cfg k Symbol State input} (h_halt : cfg.state = none) :
    tm.outputSymbol cfg = none := by
  simp [outputSymbol, h_halt]

/-- The work-tape head moves by at most one cell in a single step. -/
lemma workTapePos_step_le (c : Cfg k Symbol State input) (i : Fin k) :
    |(tm.step c).workTapePos i - c.workTapePos i| ≤ 1 := by
  unfold step
  cases hstate : c.state with
  | none => simp
  | some q => exact workTapePos_apply_le _ c i

end Cfg

section Space
/-! Now we define space usage and add some helper lemmas. -/

/-- The set of positions visited by the head of work tape `i` in the computation starting from
configuration `cfg` up to step `t`. -/
def visitedByTapeHead (cfg : Cfg k Symbol State input) (t : ℕ) (i : Fin k) : Finset ℤ :=
  (Finset.range (t + 1)).image fun t' => (tm.runFrom cfg t').workTapePos i

/--
The number of work tape cells touched by the head of tape `i` in the computation starting from
configuration `cfg` up to step `t`.
-/
def spaceUsedByTape (cfg : Cfg k Symbol State input) (t : ℕ) (i : Fin k) : ℕ :=
  (tm.visitedByTapeHead cfg t i).card

/--
The number of work tape cells touched by a computation starting from configuration
`cfg` up to step `t`.
-/
def spaceUsed (cfg : Cfg k Symbol State input) (t : ℕ) : ℕ := ∑ i, tm.spaceUsedByTape cfg t i

/-- A zero-tape Turing machine uses zero space. -/
@[simp]
lemma spaceUsed_zero_tapes_eq_zero (cfg : Cfg k Symbol State input) (t : ℕ) (h_zero : k = 0) :
    tm.spaceUsed cfg t = 0 := by
  unfold spaceUsed
  subst h_zero
  simp

/-- Each tape's space usage is bounded by the total space used. -/
lemma spaceUsedByTape_le_spaceUsed (cfg : Cfg k Symbol State input) (t : ℕ) (i : Fin k) :
    tm.spaceUsedByTape cfg t i ≤ tm.spaceUsed cfg t :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

/-- The space used up to step `t` is the space touched by the configurations up to step `t`. -/
lemma spaceUsed_eq_spaceUsedOfCfgs (cfg : Cfg k Symbol State input) (t : ℕ) :
    tm.spaceUsed cfg t = spaceUsedOfCfgs ((List.range (t + 1)).map (tm.runFrom cfg)) := by
  unfold spaceUsed spaceUsedByTape spaceUsedOfCfgs
  refine Finset.sum_congr rfl fun i _ => congrArg Finset.card ?_
  ext z
  simp [visitedByTapeHead, visitedOfCfgs]

end Space

open Cfg

/-- One step appends the symbol (optionally) emitted by that step to the output tape. -/
@[simp]
lemma step_output (cfg : Cfg k Symbol State input) :
    (tm.step cfg).output = cfg.output ++ (tm.outputSymbol cfg).toList := by
  unfold step outputSymbol Action.apply
  cases cfg.state <;> simp

/-- The output does not change after the machine has halted. -/
lemma runFrom_output_eq_of_halt
    (tm : MultiTapeTM k Symbol State)
    (cfg : Cfg k Symbol State input) {τ t : ℕ} (hle : τ ≤ t)
    (hhalt : (tm.runFrom cfg τ).state = none) :
    (tm.runFrom cfg t).output = (tm.runFrom cfg τ).output := by
  conv_lhs => rw [← Nat.sub_add_cancel hle, Nat.add_comm]
  rw [runFrom_add, runFrom_of_halt _ hhalt]

/-- A proof that the Turing machine `tm` on input `input` outputs `output` in at most `t` steps
and uses exactly `s` space.
Note that this does not require the alphabet or state set to be finite. -/
def ComputesInTimeAndSpace
    (tm : MultiTapeTM k Symbol State)
    (input output : List Symbol)
    (t s : ℕ) : Prop :=
  (tm.runFrom (tm.initCfg input) t).state = none ∧
  (tm.runFrom (tm.initCfg input) t).output = output ∧
  tm.spaceUsed (tm.initCfg input) t = s

/-- A machine computes `f` between the supplied encodings, with bounds depending on the input.
The machine's alphabet and state type need not be finite. -/
def ComputesFunInTimeAndSpace {α β : Type*}
    (tm : MultiTapeTM k Symbol State)
    (encIn : α ↪ List Symbol) (encOut : β ↪ List Symbol)
    (f : α → β) (t s : α → ℕ) : Prop :=
  ∀ a, ∃ t' ≤ t a, ∃ s' ≤ s a,
    ComputesInTimeAndSpace tm (encIn a) (encOut (f a)) t' s'

/-- A function is computable within the input-indexed bounds by a machine with binary alphabet
and finitely many states. -/
def ComputableInTimeAndSpace {α β : Type*}
    (f : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool)
    (t s : α → ℕ) : Prop :=
  ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State),
    ComputesFunInTimeAndSpace tm encIn encOut f t s

/-- There exists a binary Turing machine with finitely many states that, for every input `a`,
computes `encOut (f a)` from `encIn a` in at most `t (encIn a).length` steps,
using at most `s (encIn a).length` work-tape cells. -/
abbrev ComputableInTimeAndSpaceOfLength {α β : Type*}
    (f : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool)
    (t s : ℕ → ℕ) : Prop :=
  ComputableInTimeAndSpace f encIn encOut
    (fun a => t (encIn a).length) (fun a => s (encIn a).length)

/-- Resource bounds can be weakened independently on every input. -/
theorem ComputesFunInTimeAndSpace.mono {α β : Type*}
    {tm : MultiTapeTM k Symbol State} {encIn : α ↪ List Symbol} {encOut : β ↪ List Symbol}
    {f : α → β} {t s t' s' : α → ℕ}
    (h : ComputesFunInTimeAndSpace tm encIn encOut f t s)
    (ht : ∀ a, t a ≤ t' a) (hs : ∀ a, s a ≤ s' a) :
    ComputesFunInTimeAndSpace tm encIn encOut f t' s' := fun a => by
  obtain ⟨u, hu, v, hv, hc⟩ := h a
  exact ⟨u, hu.trans (ht a), v, hv.trans (hs a), hc⟩

/-- Computability is monotone in the resource bounds. -/
theorem ComputableInTimeAndSpace.mono {α β : Type*}
    {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {t s t' s' : α → ℕ}
    (h : ComputableInTimeAndSpace f encIn encOut t s)
    (ht : ∀ a, t a ≤ t' a) (hs : ∀ a, s a ≤ s' a) :
    ComputableInTimeAndSpace f encIn encOut t' s' := by
  obtain ⟨k, State, hfinite, tm, htm⟩ := h
  exact ⟨k, State, hfinite, tm, htm.mono ht hs⟩

open Classical in
/-- The Boolean indicator function of a set. -/
noncomputable def indicator {α : Type*} (L : Set α) : α → Bool :=
  fun x => if x ∈ L then true else false

/-- A set is decidable within the given input-indexed bounds when its Boolean indicator is. -/
def DecidableInTimeAndSpace {α : Type*} (L : Set α) (enc : α ↪ List Bool)
    (t s : α → ℕ) : Prop :=
  ComputableInTimeAndSpace (indicator L) enc ⟨fun b => [b], by intro a b h; simpa using h⟩ t s

/-- The Turing machine `tm` halts after exactly `t` steps on input `input`
if its state is `none` at step `t` and non-none at step `t - 1`.
Note that every Turing machine hast to perform at least one step to halt. -/
def haltsAtStep (tm : MultiTapeTM k Symbol State) (input : List Symbol) (t : ℕ) : Bool :=
  (tm.runFrom (tm.initCfg input) t).state.isNone &&
  !(tm.runFrom (tm.initCfg input) (t - 1)).state.isNone

/-- If a Turing machine halts, the time step is uniquely determined. -/
lemma halting_step_unique
    {tm : MultiTapeTM k Symbol State}
    {input : List Symbol}
    {t₁ t₂ : ℕ}
    (h_halts₁ : tm.haltsAtStep input t₁)
    (h_halts₂ : tm.haltsAtStep input t₂) :
    t₁ = t₂ := by
  wlog h : t₁ ≤ t₂
  · exact (this h_halts₂ h_halts₁ (Nat.le_of_not_le h)).symm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  cases d with
  | zero => rfl
  | succ d =>
    have halts₁ : (tm.runFrom (tm.initCfg input) t₁).state = none := by
      simp [haltsAtStep] at h_halts₁
      exact h_halts₁.left
    have halts₂ : (tm.runFrom (tm.initCfg input) (d + t₁)).state ≠ none := by
      grind [haltsAtStep, runFrom]
    refine absurd ?_ halts₂
    rw [Nat.add_comm, runFrom_add, tm.runFrom_of_halt _ halts₁]
    exact halts₁

/-- If a deterministic machine repeats a non-halting configuration, it never halts,
because the sequence between the two configurations will loop forever.
Note that this can be applied to two arbitrary and different time steps `t` and `t + Δ`
using `tm.runFrom_add`. -/
lemma not_halts_of_repeat_nonhalt
    (cfg : Cfg k Symbol State input)
    (h_not_halt : cfg.state ≠ none)
    (t : ℕ)
    (heq : tm.runFrom cfg (t + 1) = cfg) :
    ∀ t', (tm.runFrom cfg t').state ≠ none := by
  intro t'
  -- The configuration will repeat every `t + 1` steps.
  have hloop : ∀ n, tm.runFrom cfg (n * (t + 1)) = cfg := by
    intro n
    unfold runFrom
    rw [Nat.mul_comm, Function.iterate_mul]
    exact Function.iterate_fixed heq n
  by_contra hnh
  -- Assuming the machine halts at step `t'`, it is also halted at step `t' * (t + 1)`
  have h₁ : (tm.runFrom cfg (t' * (t + 1))).state = none := by
    have hle : t' ≤ t' * (t + 1) := by grind
    obtain ⟨tΔ , htΔ⟩ := Nat.exists_eq_add_of_le hle
    rw [htΔ, tm.runFrom_add]
    simp [hnh]
  simp [hloop t', h_not_halt] at h₁

end MultiTapeTM

end Turing
```

## ===== TCSlib/Complexity/TuringMachine/Simulation.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option
import TCSlib.Complexity.TuringMachine.Finite

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Simulation gadgets

Generic building blocks for machine constructions, split out of
`TCSlib.Complexity.TuringMachine.Composition` at the epoch-1/epoch-2 boundary
(epoch-1 audit, findings 5 and 11, and the policy file-size standard): the
machines of the composition file, and the heavier constructions of later
epochs, are assembled from these. Everything here is public — it is shared
audited surface — and carries no finiteness assumptions beyond what each
gadget needs.

## Contents

* **Emission chains** (`Turing.FinTM.emitAction`, `emit_run`, `emit_halts`):
  states that write a fixed word to the output, one symbol per step, ignoring
  all reads, then halt.
* **Control actions** (`Turing.FinTM.controlAction`, `controlAction_apply`):
  transitions that only move the input head and change state.
* **Input-head positioning** (`Turing.FinTM.inputSymbol_at`,
  `moveInputPos_neg_val`, `rewind_scan`, `rewind_from_any`): reading at a
  position, the clamped left move, and the audited rewind-to-start procedure
  (one unconditional left move, left while reading a symbol, one right move).
* **Disjoint tape-block embeddings** (`Turing.FinTM.leftAction`/`rightAction`,
  `leftCfg`/`rightCfg`, their `apply`/`step`/`run` lemmas): run a machine on
  the left or right block of a `k + l`-tape machine, in lockstep, with the
  other block's tapes inactive. **Scope note** (epoch-1 audit, finding 11):
  these embeddings preserve the *native* input tape and pass emissions to the
  *real* output — they are not, by themselves, a buffered-composition
  simulator; buffering and virtual-input clamping need their own invariants on
  top.
* **Branch union** (`Turing.FinTM.branchTM`, `branchTM_computes`): two
  machines in disjoint tape and state blocks; the Boolean chooses only the
  initial state.
* **Optional-write normalization** (`Turing.Action.apply_workTapes`): the raw
  action-application identity for work tapes, promoted at the epoch-2/epoch-3
  boundary.
* **Buffered sequential simulator** (`Turing.FinTM.bufferedCompTM`): the
  three-block tape partition, contiguous buffer representation, virtual-input
  reads and clamping invariant, first- and second-phase run correspondence,
  and an exact `|y| + 2` rewind-and-dispatch ledger. These extend the scope of
  the native-input embeddings above without changing their statements.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2-§1.3; the "high-level description"
  convention on p. 14.)
-/

namespace Turing

/-- **Optional-write normalization** (promoted from the epoch-2 fill per the
epoch-2 audit, promotion recommendation 1): applying an action rewrites each
work tape at its head with the proposed write, defaulting to the existing read
when the action declines to write. An explicit `some none` write remains an
erase, while an outer `none` writes back the scanned symbol unchanged. Holds
for every alphabet, state type, action, configuration, and tape index — no
finiteness, liveness, or computation hypothesis. -/
lemma Action.apply_workTapes {k : ℕ} {Symbol State : Type*} {input : List Symbol}
    (a : Action k Symbol State) (c : Cfg k Symbol State input) (i : Fin k) :
    (a.apply c).workTapes i =
      Function.update (c.workTapes i) (c.workTapePos i)
        ((a.workTapes i).1.getD (c.workTapeSymbols i)) := by
  cases hw : (a.workTapes i).1 with
  | none => simp [Action.apply, hw, Cfg.workTapeSymbols]
  | some w => simp [Action.apply, hw]

end Turing

namespace Turing.FinTM

/-- One step of a fixed-word emission chain, with an arbitrary state embedding.
The input and all work tapes are left untouched. -/
def emitAction {k : ℕ} {S : Type} (w : List Bool)
    (e : Fin (w.length + 1) → S) (i : Fin (w.length + 1)) : Action k Bool S :=
  if h : i.val < w.length then
    ⟨0, fun _ => (none, 0), some w[i.val], some (e ⟨i.val + 1, by omega⟩)⟩
  else
    ⟨0, fun _ => (none, 0), none, none⟩

/-- After `t` emission steps the state is the `t`-th chain state and exactly the
first `t` symbols have been appended. The induction uses no tape invariant because
emission transitions ignore all reads. -/
lemma emit_run {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (w : List Bool) (e : Fin (w.length + 1) → S)
    (htr : ∀ i inp work, tm.tr (e i) inp work = emitAction w e i)
    (cfg : Cfg k Bool S x) (hs : cfg.state = some (e 0)) :
    ∀ t (ht : t ≤ w.length),
      (tm.runFrom cfg t).state = some (e ⟨t, by omega⟩) ∧
      (tm.runFrom cfg t).output = cfg.output ++ w.take t := by
  intro t
  induction t with
  | zero =>
    intro ht
    exact ⟨hs, by simp⟩
  | succ t ih =>
    intro ht
    obtain ⟨hstate, hout⟩ := ih (by omega)
    have hstep : tm.runFrom cfg (t + 1) =
        (emitAction w e ⟨t, by omega⟩).apply (tm.runFrom cfg t) := by
      rw [MultiTapeTM.runFrom_succ_eq_step']
      unfold MultiTapeTM.step
      rw [hstate]
      exact congrArg (fun a => a.apply (tm.runFrom cfg t)) (htr _ _ _)
    rw [hstep]
    simp only [emitAction, dif_pos (show t < w.length by omega), Action.apply]
    refine ⟨True.intro, ?_⟩
    rw [hout, List.take_succ, List.getElem?_eq_getElem (by omega)]
    simp [List.append_assoc]

/-- One further, nonemitting step halts the fixed-word emission chain. -/
lemma emit_halts {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (w : List Bool) (e : Fin (w.length + 1) → S)
    (htr : ∀ i inp work, tm.tr (e i) inp work = emitAction w e i)
    (cfg : Cfg k Bool S x) (hs : cfg.state = some (e 0)) :
    (tm.runFrom cfg (w.length + 1)).state = none ∧
      (tm.runFrom cfg (w.length + 1)).output = cfg.output ++ w := by
  obtain ⟨hstate, hout⟩ := emit_run tm w e htr cfg hs w.length (le_refl _)
  rw [MultiTapeTM.runFrom_succ_eq_step']
  unfold MultiTapeTM.step
  rw [hstate]
  dsimp only
  rw [htr]
  simp [emitAction, Action.apply, hout]


/-- An action that only moves the input head and changes the state. -/
def controlAction {k : ℕ} {S : Type} (m : SignType) (q : Option S) :
    Action k Bool S := ⟨m, fun _ => (none, 0), none, q⟩

/-- Read position `i + 1` as the optional `i`-th input symbol, including the
right boundary. -/
lemma inputSymbol_at {k : ℕ} {S : Type} {x : List Bool}
    (cfg : Cfg k Bool S x) (i : ℕ) (hi : i ≤ x.length)
    (hp : cfg.inputPos.val = i + 1) : cfg.inputSymbol = x[i]? := by
  by_cases h : i < x.length
  · rw [inputSymbolInner i (by omega) h, List.getElem?_eq_getElem h]
  · have he : i = x.length := by omega
    have hz : cfg.inputPos ≠ 0 := by
      intro hz
      rw [hz] at hp
      simp at hp
    simp only [Cfg.inputSymbol, dif_neg hz, dif_pos (show cfg.inputPos.val = x.length + 1 by omega)]
    simp [he]


/-- Extend an action to the left block of a disjoint tape sum and rename states. -/
def leftAction {k : ℕ} {S S' : Type} (l : ℕ) (f : S → S')
    (a : Action k Bool S) : Action (k + l) Bool S' where
  inputTape := a.inputTape
  workTapes := Fin.addCases a.workTapes (fun _ => (none, 0))
  output := a.output
  state := a.state.map f

/-- Extend an action to the right block, leaving the left block untouched. -/
def rightAction {l : ℕ} {S S' : Type} (k : ℕ) (f : S → S')
    (a : Action l Bool S) : Action (k + l) Bool S' where
  inputTape := a.inputTape
  workTapes := Fin.addCases (fun _ => (none, 0)) a.workTapes
  output := a.output
  state := a.state.map f

/-- Embed a configuration in the left tape block, retaining arbitrary inactive
right tapes and head positions. The state renaming preserves halting. -/
def leftCfg {k l : ℕ} {S S' : Type} {x : List Bool} (f : S → S')
    (c : Cfg k Bool S x) (tapes : Fin l → ℤ → Option Bool) (heads : Fin l → ℤ) :
    Cfg (k + l) Bool S' x where
  state := c.state.map f
  inputPos := c.inputPos
  workTapes := Fin.addCases c.workTapes tapes
  workTapePos := Fin.addCases c.workTapePos heads
  output := c.output

/-- Embed in the right block, retaining arbitrary inactive left tapes. This is also
used when the left block contains a completed controller's work. -/
def rightCfg {k l : ℕ} {S S' : Type} {x : List Bool} (f : S → S')
    (c : Cfg l Bool S x) (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ) :
    Cfg (k + l) Bool S' x where
  state := c.state.map f
  inputPos := c.inputPos
  workTapes := Fin.addCases tapes c.workTapes
  workTapePos := Fin.addCases heads c.workTapePos
  output := c.output

/-- Extending an action commutes with the left configuration embedding. -/
lemma leftCfg_apply {k l : ℕ} {S S' : Type} {x : List Bool} (f : S → S')
    (a : Action k Bool S) (c : Cfg k Bool S x)
    (tapes : Fin l → ℤ → Option Bool) (heads : Fin l → ℤ) :
    (leftAction l f a).apply (leftCfg f c tapes heads) =
      leftCfg f (a.apply c) tapes heads := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp [leftAction, leftCfg, Action.apply]
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp [leftAction, leftCfg, Action.apply]

/-- Extending an action commutes with the right configuration embedding. -/
lemma rightCfg_apply {k l : ℕ} {S S' : Type} {x : List Bool} (f : S → S')
    (a : Action l Bool S) (c : Cfg l Bool S x)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ) :
    (rightAction k f a).apply (rightCfg f c tapes heads) =
      rightCfg f (a.apply c) tapes heads := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp [rightAction, rightCfg, Action.apply]
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp [rightAction, rightCfg, Action.apply]

/-- A machine whose renamed transitions use only the left block simulates one
step exactly, including the absorbing halting configuration. -/
lemma leftCfg_step {k l : ℕ} {S S' : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (tm' : MultiTapeTM (k + l) Bool S') (f : S → S')
    (htr : ∀ q inp work, tm'.tr (f q) inp work =
      leftAction l f (tm.tr q inp (fun i => work (Fin.castAdd l i))))
    (c : Cfg k Bool S x) (tapes : Fin l → ℤ → Option Bool) (heads : Fin l → ℤ) :
    tm'.step (leftCfg f c tapes heads) = leftCfg f (tm.step c) tapes heads := by
  unfold MultiTapeTM.step
  cases hs : c.state with
  | none => simp [leftCfg, hs]
  | some q =>
    have hs' : (leftCfg f c tapes heads).state = some (f q) := by simp [leftCfg, hs]
    rw [hs']
    dsimp only
    rw [htr]
    have hr : (fun i => (leftCfg f c tapes heads).workTapeSymbols (Fin.castAdd l i)) =
        c.workTapeSymbols := by
      funext i
      simp [Cfg.workTapeSymbols, leftCfg]
    change (leftAction l f (tm.tr q c.inputSymbol _)).apply _ = _
    rw [hr]
    exact leftCfg_apply f _ c tapes heads

/-- The right-block version of the one-step correspondence; inactive tapes may
contain arbitrary data from an earlier phase. -/
lemma rightCfg_step {k l : ℕ} {S S' : Type} {x : List Bool}
    (tm : MultiTapeTM l Bool S) (tm' : MultiTapeTM (k + l) Bool S') (f : S → S')
    (htr : ∀ q inp work, tm'.tr (f q) inp work =
      rightAction k f (tm.tr q inp (fun i => work (Fin.natAdd k i))))
    (c : Cfg l Bool S x) (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ) :
    tm'.step (rightCfg f c tapes heads) = rightCfg f (tm.step c) tapes heads := by
  unfold MultiTapeTM.step
  cases hs : c.state with
  | none => simp [rightCfg, hs]
  | some q =>
    have hs' : (rightCfg f c tapes heads).state = some (f q) := by simp [rightCfg, hs]
    rw [hs']
    dsimp only
    rw [htr]
    have hr : (fun i => (rightCfg f c tapes heads).workTapeSymbols (Fin.natAdd k i)) =
        c.workTapeSymbols := by
      funext i
      simp [Cfg.workTapeSymbols, rightCfg]
    change (rightAction k f (tm.tr q c.inputSymbol _)).apply _ = _
    rw [hr]
    exact rightCfg_apply f _ c tapes heads

/-- Lift the left-block one-step correspondence to every finite run. -/
lemma leftCfg_run {k l : ℕ} {S S' : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (tm' : MultiTapeTM (k + l) Bool S') (f : S → S')
    (htr : ∀ q inp work, tm'.tr (f q) inp work =
      leftAction l f (tm.tr q inp (fun i => work (Fin.castAdd l i))))
    (c : Cfg k Bool S x) (tapes : Fin l → ℤ → Option Bool) (heads : Fin l → ℤ) (t : ℕ) :
    tm'.runFrom (leftCfg f c tapes heads) t = leftCfg f (tm.runFrom c t) tapes heads :=
  MultiTapeTM.runFrom_comm_of_step (fun c => leftCfg f c tapes heads)
    (fun c => leftCfg_step tm tm' f htr c tapes heads) c t

/-- Lift the right-block correspondence to every run, preserving arbitrary
inactive left tapes. This is the fresh-branch lockstep gadget. -/
lemma rightCfg_run {k l : ℕ} {S S' : Type} {x : List Bool}
    (tm : MultiTapeTM l Bool S) (tm' : MultiTapeTM (k + l) Bool S') (f : S → S')
    (htr : ∀ q inp work, tm'.tr (f q) inp work =
      rightAction k f (tm.tr q inp (fun i => work (Fin.natAdd k i))))
    (c : Cfg l Bool S x) (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ) (t : ℕ) :
    tm'.runFrom (rightCfg f c tapes heads) t = rightCfg f (tm.runFrom c t) tapes heads :=
  MultiTapeTM.runFrom_comm_of_step (fun c => rightCfg f c tapes heads)
    (fun c => rightCfg_step tm tm' f htr c tapes heads) c t

/-- Put two machines in disjoint tape and state blocks; the Boolean chooses only
the initial state, while the transition table is independent of that choice. -/
def branchTM (M₁ M₂ : FinTM Bool) (b : Bool) : FinTM Bool where
  k := M₁.k + M₂.k
  State := M₁.State ⊕ M₂.State
  tm :=
    { q₀ := cond b (.inl M₁.tm.q₀) (.inr M₂.tm.q₀)
      tr := fun q inp work => match q with
        | .inl q => leftAction M₂.k Sum.inl
            (M₁.tm.tr q inp (fun i => work (Fin.castAdd M₂.k i)))
        | .inr q => rightAction M₁.k Sum.inr
            (M₂.tm.tr q inp (fun i => work (Fin.natAdd M₁.k i))) }

/-- Each selected branch has exactly its original time and completed output.
The proof embeds its initial blank configuration, then uses lockstep. -/
lemma branchTM_computes (M₁ M₂ : FinTM Bool) (b : Bool) (x w : List Bool) (t : ℕ) :
    (branchTM M₁ M₂ b).ComputesInTime x w t ↔ (cond b M₁ M₂).ComputesInTime x w t := by
  cases b with
  | false =>
    have hi : (branchTM M₁ M₂ false).tm.initCfg x =
        rightCfg Sum.inr (M₂.tm.initCfg x) (fun (_ : Fin M₁.k) _ => none) (fun _ => 0) := by
      refine Cfg.ext rfl rfl ?_ ?_ rfl
      · funext i
        refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [rightCfg]
      · funext i
        refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [rightCfg]
    rw [computesInTime_iff, computesInTime_iff, hi,
      rightCfg_run M₂.tm (branchTM M₁ M₂ false).tm Sum.inr (fun _ _ _ => rfl)]
    simp only [rightCfg, Option.map_eq_none_iff]
  | true =>
    have hi : (branchTM M₁ M₂ true).tm.initCfg x =
        leftCfg Sum.inl (M₁.tm.initCfg x) (fun (_ : Fin M₂.k) _ => none) (fun _ => 0) := by
      refine Cfg.ext rfl rfl ?_ ?_ rfl
      · funext i
        refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [leftCfg]
      · funext i
        refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [leftCfg]
    rw [computesInTime_iff, computesInTime_iff, hi,
      leftCfg_run M₁.tm (branchTM M₁ M₂ true).tm Sum.inl (fun _ _ _ => rfl)]
    simp only [leftCfg, Option.map_eq_none_iff]

/-- A control action leaves all work tapes, work heads, and output unchanged. -/
lemma controlAction_apply {k : ℕ} {S : Type} {x : List Bool}
    (cfg : Cfg k Bool S x) (m : SignType) (q : Option S) :
    (controlAction m q).apply cfg =
      {cfg with state := q, inputPos := moveInputPos cfg.inputPos m} := by
  refine Cfg.ext rfl rfl rfl ?_ ?_
  · funext i
    simp [controlAction, Action.apply]
  · simp [controlAction, Action.apply]

/-- The clamped left move always subtracts one from the natural input position. -/
lemma moveInputPos_neg_val {n : ℕ} (pos : Fin (n + 2)) :
    (moveInputPos pos .neg).val = pos.val - 1 := by
  by_cases h : pos = 0
  · subst pos
    simp [SignType.neg_eq_neg_one]
  · rw [moveInputPos_neg_of_ne_left pos h]

/-- Starting at or to the left of the last input symbol, scan left to the left
blank, then move right and dispatch. All other configuration fields are preserved.

**Proof sketch.** Induct on the input-head position. At zero the scanned symbol is
blank, so one right move finishes. At a positive position the input symbol exists;
one left move reduces the position and the induction hypothesis finishes the run. -/
lemma rewind_scan {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (scan : S) (dest : Option S)
    (htr : ∀ inp work, tm.tr scan inp work =
      match inp with
      | some _ => controlAction .neg (some scan)
      | none => controlAction .pos dest) :
    ∀ (cfg : Cfg k Bool S x), cfg.state = some scan → cfg.inputPos.val ≤ x.length →
      tm.runFrom cfg (cfg.inputPos.val + 1) = {cfg with state := dest, inputPos := 1} := by
  have aux : ∀ (j : ℕ) (cfg : Cfg k Bool S x), cfg.state = some scan →
      cfg.inputPos.val = j → j ≤ x.length →
      tm.runFrom cfg (j + 1) = {cfg with state := dest, inputPos := 1} := by
    intro j
    induction j with
    | zero =>
      intro cfg hs hj _
      have hz : cfg.inputPos = 0 := Fin.ext hj
      have hsym : cfg.inputSymbol = none := by
        unfold Cfg.inputSymbol
        rw [dif_pos hz]
      change tm.step cfg = _
      unfold MultiTapeTM.step
      rw [hs]
      dsimp only
      rw [htr, hsym]
      dsimp only
      rw [controlAction_apply]
      have hm : moveInputPos cfg.inputPos .pos = 1 := by
        apply Fin.ext
        rw [hz, moveInputPos_pos_of_ne_right _ (by simp)]
        simp
      rw [hm]
    | succ j ih =>
      intro cfg hs hj hlen
      have hsym : cfg.inputSymbol = some (x[j]'(by omega)) :=
        inputSymbolInner j (by omega) (by omega)
      have hstep : tm.step cfg =
          {cfg with state := some scan, inputPos := moveInputPos cfg.inputPos .neg} := by
        unfold MultiTapeTM.step
        rw [hs]
        dsimp only
        rw [htr, hsym]
        dsimp only
        rw [controlAction_apply]
      have hp : (moveInputPos cfg.inputPos .neg).val = j := by
        rw [moveInputPos_neg_val]
        omega
      rw [MultiTapeTM.runFrom_succ_eq_step, hstep]
      exact ih _ rfl hp (by omega)
  intro cfg hs hp
  exact aux cfg.inputPos.val cfg hs rfl hp

/-- From any valid input position, take the mandatory first left move and then
scan left. This returns to position `1`, even for an empty input or a start at a
boundary. No work tape or output is changed. -/
lemma rewind_from_any {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (start scan : S) (dest : Option S)
    (hstart : ∀ inp work, tm.tr start inp work = controlAction .neg (some scan))
    (hscan : ∀ inp work, tm.tr scan inp work =
      match inp with
      | some _ => controlAction .neg (some scan)
      | none => controlAction .pos dest)
    (cfg : Cfg k Bool S x) (hs : cfg.state = some start) :
    ∃ t, tm.runFrom cfg t = {cfg with state := dest, inputPos := 1} := by
  have hstep : tm.step cfg =
      {cfg with state := some scan, inputPos := moveInputPos cfg.inputPos .neg} := by
    unfold MultiTapeTM.step
    rw [hs]
    dsimp only
    rw [hstart, controlAction_apply]
  let c := tm.step cfg
  have hc : c.state = some scan := by simp only [c, hstep]
  have hp : c.inputPos.val ≤ x.length := by
    simp only [c, hstep, moveInputPos_neg_val]
    have := cfg.inputPos.isLt
    omega
  refine ⟨1 + (c.inputPos.val + 1), ?_⟩
  rw [MultiTapeTM.runFrom_add]
  have hfirst : tm.runFrom cfg 1 = c := rfl
  rw [hfirst, rewind_scan tm scan dest hscan c hc hp]
  simp only [c, hstep]

/-- A quantitative refinement of `rewind_from_any`: its construction takes
at most the current input position plus two steps, preserving all work and output.
**Proof sketch.** The mandatory first left move puts the head at most at the
last input symbol. `rewind_scan` then takes exactly the new position plus one. -/
lemma timed_rewind {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (start scan : S) (dest : Option S)
    (hstart : ∀ inp work, tm.tr start inp work = controlAction .neg (some scan))
    (hscan : ∀ inp work, tm.tr scan inp work = match inp with
      | some _ => controlAction .neg (some scan)
      | none => controlAction .pos dest)
    (c : Cfg k Bool S x) (hs : c.state = some start) :
    ∃ r ≤ c.inputPos.val + 2,
      tm.runFrom c r = {c with state := dest, inputPos := 1} := by
  have hstep : tm.step c =
      {c with state := some scan, inputPos := moveInputPos c.inputPos .neg} := by
    unfold MultiTapeTM.step
    rw [hs]
    dsimp only
    rw [hstart, controlAction_apply]
  have hp : (moveInputPos c.inputPos .neg).val ≤ x.length := by
    rw [moveInputPos_neg_val]
    have := c.inputPos.isLt
    omega
  refine ⟨1 + ((moveInputPos c.inputPos .neg).val + 1), ?_, ?_⟩
  · rw [moveInputPos_neg_val]; omega
  · rw [MultiTapeTM.runFrom_add]
    change tm.runFrom (tm.step c) _ = _
    rw [hstep, rewind_scan tm scan dest hscan _ rfl hp]

/-- Assemble the left work block, one buffer tape, and the right work block.
All three projections use the same nested `Fin.addCases` partition. -/
def tapeBlocks {α : Type} {k l : ℕ} (left : Fin k → α) (buffer : α)
    (right : Fin l → α) : Fin (k + (1 + l)) → α :=
  Fin.addCases left (Fin.addCases (fun _ => buffer) right)

/-- The left projection of the three-block tape partition. -/
@[simp] lemma tapeBlocks_left {α : Type} {k l : ℕ} (a : Fin k → α) (b : α)
    (c : Fin l → α) (i : Fin k) :
    tapeBlocks a b c (Fin.castAdd (1 + l) i) = a i := by simp [tapeBlocks]

/-- The buffer projection of the three-block tape partition. -/
@[simp] lemma tapeBlocks_buffer {α : Type} {k l : ℕ} (a : Fin k → α) (b : α)
    (c : Fin l → α) (i : Fin 1) :
    tapeBlocks a b c (Fin.natAdd k (Fin.castAdd l i)) = b := by
  simp [tapeBlocks]

/-- The right projection of the three-block tape partition. -/
@[simp] lemma tapeBlocks_right {α : Type} {k l : ℕ} (a : Fin k → α) (b : α)
    (c : Fin l → α) (i : Fin l) :
    tapeBlocks a b c (Fin.natAdd k (Fin.natAdd 1 i)) = c i := by simp [tapeBlocks]

/-- A word stored contiguously from cell zero, blank at every other integer cell. -/
def bufferTape (w : List Bool) (z : ℤ) : Option Bool :=
  if 0 ≤ z then w[z.toNat]? else none

/-- An empty buffer is blank everywhere. -/
@[simp] lemma bufferTape_nil : bufferTape [] = fun _ => none := by
  funext z
  simp [bufferTape]

/-- The buffer cell at any nonnegative natural position reads the corresponding
optional word entry, so position `w.length` is the right blank. -/
@[simp] lemma bufferTape_nat (w : List Bool) (i : ℕ) :
    bufferTape w i = w[i]? := by simp [bufferTape]

/-- Cell minus one is the left blank, including for an empty word. -/
@[simp] lemma bufferTape_left (w : List Bool) : bufferTape w (-1) = none := by
  simp [bufferTape]

/-- Appending one emitted bit changes just the old right-blank cell.

**Proof sketch.** At that cell the appended singleton is read. At a smaller
nonnegative cell, list lookup stays in the old prefix. Larger cells and all
negative cells remain blank. -/
lemma bufferTape_append (w : List Bool) (b : Bool) :
    bufferTape (w ++ [b]) = Function.update (bufferTape w) (w.length : ℤ) (some b) := by
  funext z
  by_cases hz : z = (w.length : ℤ)
  · subst z
    simp [bufferTape]
  · rw [Function.update_of_ne hz]
    by_cases h0 : 0 ≤ z
    · have hne : z.toNat ≠ w.length := by omega
      simp only [bufferTape, if_pos h0, List.getElem?_append]
      split
      · rfl
      · have hgt : w.length < z.toNat := by omega
        rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]
    · simp [bufferTape, h0]

/-- A boundary tag constrains only boundary positions: false at the left blank,
true at the right blank. Interior positions admit either direction-of-arrival tag. -/
def VirtualTag {n : ℕ} (p : Fin (n + 2)) (b : Bool) : Prop :=
  (p.val = 0 → b = false) ∧ (p.val = n + 1 → b = true)

/-- Suppress an outward move at a blank whose boundary is identified by the tag.
The real buffer head otherwise takes the simulated input movement. -/
def virtualMove (b : Bool) (inp : Option Bool) (m : SignType) : SignType :=
  if inp = none ∧ ((b = false ∧ m = .neg) ∨ (b = true ∧ m = .pos)) then 0 else m

/-- Record the last nonstationary buffer movement. A stationary move preserves
its boundary tag, so repeated outward attempts remain clamped. -/
def virtualNextTag (b : Bool) (m : SignType) : Bool :=
  match m with
  | .neg => false
  | .zero => b
  | .pos => true

/-- Buffer reads at virtual position minus one equal native input reads. -/
lemma bufferTape_inputSymbol {k : ℕ} {S : Type} {w : List Bool}
    (c : Cfg k Bool S w) : bufferTape w ((c.inputPos.val : ℤ) - 1) = c.inputSymbol := by
  by_cases h0 : c.inputPos = 0
  · simp [Cfg.inputSymbol, h0]
  · have hp : 0 < c.inputPos.val := by
      have : c.inputPos.val ≠ 0 := fun h => h0 (Fin.ext h)
      omega
    have he : (c.inputPos.val : ℤ) - 1 = ((c.inputPos.val - 1 : ℕ) : ℤ) := by omega
    rw [he, bufferTape_nat]
    have h := inputSymbol_at c (c.inputPos.val - 1)
      (by have := c.inputPos.isLt; omega) (by omega)
    exact h.symm

/-- The virtual movement and arrival tag exactly implement native clamping.

**Proof sketch.** Split into left boundary, right boundary, and interior. The
buffer is blank exactly at the two boundaries in this range. The tag specifies
which outward direction to suppress. The three movement cases then give the
position equation and preserve the boundary-tag invariant, even on empty input. -/
lemma virtualMove_correct {k : ℕ} {S : Type} {w : List Bool}
    (c : Cfg k Bool S w) (b : Bool) (hb : VirtualTag c.inputPos b) (m : SignType) :
    (c.inputPos.val : ℤ) - 1 + (virtualMove b c.inputSymbol m : ℤ) =
      ((moveInputPos c.inputPos m).val : ℤ) - 1 ∧
    VirtualTag (moveInputPos c.inputPos m)
      (virtualNextTag b (virtualMove b c.inputSymbol m)) := by
  have hp := c.inputPos.isLt
  by_cases h0 : c.inputPos.val = 0
  · have he : c.inputPos = 0 := Fin.ext h0
    have hbf := hb.1 h0
    subst b
    cases m <;>
      simp [virtualMove, virtualNextTag, Cfg.inputSymbol, he, VirtualTag,
        moveInputPos, SignType.zero_eq_zero, SignType.neg_eq_neg_one,
        SignType.pos_eq_one]
  · have hne : c.inputPos ≠ 0 := fun h => h0 (congrArg Fin.val h)
    by_cases hr : c.inputPos.val = w.length + 1
    · have hbt := hb.2 hr
      subst b
      have he : c.inputPos = ⟨w.length + 1, by omega⟩ := Fin.ext hr
      have hs : c.inputSymbol = none := by simp [Cfg.inputSymbol, he]
      cases m with
      | zero =>
        simpa [virtualMove, virtualNextTag, hs, SignType.zero_eq_zero] using
          (And.intro (show (c.inputPos.val : ℤ) - 1 = (c.inputPos.val : ℤ) - 1 from rfl) hb)
      | pos =>
        simp [virtualMove, virtualNextTag, hs, he, VirtualTag, SignType.pos_eq_one]
      | neg =>
        rw [moveInputPos_neg_of_ne_left _ hne]
        simp [virtualMove, virtualNextTag, hs, VirtualTag, hr, SignType.neg_eq_neg_one]
        omega
    · have hs : c.inputSymbol = some (w[c.inputPos.val - 1]'(by omega)) :=
        inputSymbolInner _ (by omega) (by omega)
      cases m with
      | zero =>
        simpa [virtualMove, virtualNextTag, hs, SignType.zero_eq_zero] using
          (And.intro (show (c.inputPos.val : ℤ) - 1 = (c.inputPos.val : ℤ) - 1 from rfl) hb)
      | neg =>
        rw [moveInputPos_neg_of_ne_left _ hne]
        simp [virtualMove, virtualNextTag, hs, VirtualTag, SignType.neg_eq_neg_one]
        constructor <;> omega
      | pos =>
        rw [moveInputPos_pos_of_ne_right _ hr]
        simp [virtualMove, virtualNextTag, hs, VirtualTag, SignType.pos_eq_one]

/-- Run the first machine into the middle buffer, rewind it, then run the second
machine with virtual input. The first component's halting state and the rewind
state are live administrative states. Phase two alone can halt or emit output. -/
def bufferedCompTM (M₁ M₂ : FinTM Bool) : FinTM Bool where
  k := M₁.k + (1 + M₂.k)
  State := Option M₁.State ⊕ (Unit ⊕ (M₂.State × Bool))
  tm :=
    { q₀ := .inl (some M₁.tm.q₀)
      tr := fun q inp work => match q with
        | .inl (some q) =>
          let a := M₁.tm.tr q inp (fun i => work (Fin.castAdd (1 + M₂.k) i))
          ⟨a.inputTape, tapeBlocks a.workTapes
            (a.output.map some, if a.output = none then 0 else .pos)
            (fun _ => (none, 0)), none, some (.inl a.state)⟩
        | .inl none =>
          ⟨0, tapeBlocks (fun _ => (none, 0)) (none, .neg) (fun _ => (none, 0)),
            none, some (.inr (.inl ()))⟩
        | .inr (.inl ()) =>
          if work (Fin.natAdd M₁.k (Fin.castAdd M₂.k (0 : Fin 1))) = none then
            ⟨0, tapeBlocks (fun _ => (none, 0)) (none, .pos) (fun _ => (none, 0)),
              none, some (.inr (.inr (M₂.tm.q₀, true)))⟩
          else
            ⟨0, tapeBlocks (fun _ => (none, 0)) (none, .neg) (fun _ => (none, 0)),
              none, some (.inr (.inl ()))⟩
        | .inr (.inr (q, b)) =>
          let v := work (Fin.natAdd M₁.k (Fin.castAdd M₂.k (0 : Fin 1)))
          let a := M₂.tm.tr q v (fun i => work (Fin.natAdd M₁.k (Fin.natAdd 1 i)))
          let m := virtualMove b v a.inputTape
          ⟨0, tapeBlocks (fun _ => (none, 0)) (none, m) a.workTapes,
            a.output, a.state.map (fun q => .inr (.inr (q, virtualNextTag b m)))⟩ }

/-- Embed phase one with its exact emitted prefix on the buffer and the buffer
head on its right blank. The real output and the second work block are empty. -/
def bufferedFirstCfg (M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg M₁.k Bool M₁.State x) :
    Cfg (bufferedCompTM M₁ M₂).k Bool (bufferedCompTM M₁ M₂).State x where
  state := some (.inl c.state)
  inputPos := c.inputPos
  workTapes := tapeBlocks c.workTapes (bufferTape c.output) (fun _ _ => none)
  workTapePos := tapeBlocks c.workTapePos c.output.length (fun _ => 0)
  output := []

/-- The initialized composite is the embedded initialized first machine. -/
lemma bufferedFirstCfg_init (M₁ M₂ : FinTM Bool) (x : List Bool) :
    (bufferedCompTM M₁ M₂).tm.initCfg x = bufferedFirstCfg M₁ M₂ (M₁.tm.initCfg x) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [bufferedFirstCfg, tapeBlocks]
    · intro j
      refine Fin.addCases ?_ ?_ j <;> intro j <;> simp [bufferedFirstCfg, tapeBlocks]
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [bufferedFirstCfg, tapeBlocks]
    · intro j
      refine Fin.addCases ?_ ?_ j <;> intro j <;> simp [bufferedFirstCfg, tapeBlocks]

/-- One live first-phase transition preserves the complete buffer invariant,
including an emission on the simulated halting transition.

**Proof sketch.** The first work block and native input move in lockstep. A
nonemitting transition leaves the buffer fixed; an emission updates precisely its
right blank by `bufferTape_append` and moves that head one step. The second block
and real output stay empty, and a simulated halt remains an administrative state. -/
lemma bufferedFirstCfg_step (M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg M₁.k Bool M₁.State x) (hs : c.state ≠ none) :
    (bufferedCompTM M₁ M₂).tm.step (bufferedFirstCfg M₁ M₂ c) =
      bufferedFirstCfg M₁ M₂ (M₁.tm.step c) := by
  unfold MultiTapeTM.step
  cases hq : c.state with
  | none => exact False.elim (hs hq)
  | some q =>
    have hs' : (bufferedFirstCfg M₁ M₂ c).state = some (.inl (some q)) := by
      simp [bufferedFirstCfg, hq]
    rw [hs']
    dsimp only [bufferedCompTM]
    have hr : (fun i => (bufferedFirstCfg M₁ M₂ c).workTapeSymbols
        (Fin.castAdd (1 + M₂.k) i)) = c.workTapeSymbols := by
      funext i
      simp [bufferedFirstCfg, Cfg.workTapeSymbols]
    have hi : (bufferedFirstCfg M₁ M₂ c).inputSymbol = c.inputSymbol := rfl
    rw [hr, hi]
    let a := M₁.tm.tr q c.inputSymbol c.workTapeSymbols
    change (⟨a.inputTape, tapeBlocks a.workTapes
      (a.output.map some, if a.output = none then 0 else .pos)
      (fun _ => (none, 0)), none, some (.inl a.state)⟩ :
      Action (M₁.k + (1 + M₂.k)) Bool _).apply _ = bufferedFirstCfg M₁ M₂ (a.apply c)
    refine Cfg.ext rfl rfl ?_ ?_ ?_
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [bufferedFirstCfg, Action.apply]
      · intro j
        refine Fin.addCases ?_ ?_ j
        · intro j
          cases ho : a.output <;>
            simp [bufferedFirstCfg, Action.apply, ho, bufferTape_append]
        · intro j; simp [bufferedFirstCfg, Action.apply]
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [bufferedFirstCfg, Action.apply]
      · intro j
        refine Fin.addCases ?_ ?_ j
        · intro j
          cases ho : a.output <;> simp [bufferedFirstCfg, Action.apply, ho]
        · intro j; simp [bufferedFirstCfg, Action.apply]
    · simp [bufferedFirstCfg, Action.apply]

/-- First-phase lockstep holds up to and including the first halting transition.
The hypothesis deliberately excludes steps after the simulated halt. -/
lemma bufferedFirstCfg_run (M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg M₁.k Bool M₁.State x) (t : ℕ)
    (h : ∀ s, s < t → (M₁.tm.runFrom c s).state ≠ none) :
    (bufferedCompTM M₁ M₂).tm.runFrom (bufferedFirstCfg M₁ M₂ c) t =
      bufferedFirstCfg M₁ M₂ (M₁.tm.runFrom c t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (fun s hs => h s (by omega)),
      bufferedFirstCfg_step M₁ M₂ _ (h t (by omega)), MultiTapeTM.runFrom_succ_eq_step']

/-- Embed a configuration on virtual input `y` while the physical input remains
`x`. The buffer head represents virtual position minus one. The left block and
native input head retain arbitrary inactive contents from phase one. -/
def bufferedSecondCfg (M₁ M₂ : FinTM Bool) {x y : List Bool}
    (c : Cfg M₂.k Bool M₂.State y) (b : Bool) (p : Fin (x.length + 2))
    (tapes : Fin M₁.k → ℤ → Option Bool) (heads : Fin M₁.k → ℤ) :
    Cfg (bufferedCompTM M₁ M₂).k Bool (bufferedCompTM M₁ M₂).State x where
  state := c.state.map (fun q => .inr (.inr (q, b)))
  inputPos := p
  workTapes := tapeBlocks tapes (bufferTape y) c.workTapes
  workTapePos := tapeBlocks heads ((c.inputPos.val : ℤ) - 1) c.workTapePos
  output := c.output

/-- One second-phase step simulates one native step, with a valid new arrival
tag. The statement includes the absorbing halting case.

**Proof sketch.** Buffer reads agree with virtual input reads. The clamping lemma
proves the head equation and preserves the tag. All second-machine work actions
and emissions are unchanged, while the buffer and first block are read-only. -/
lemma bufferedSecondCfg_step (M₁ M₂ : FinTM Bool) {x y : List Bool}
    (c : Cfg M₂.k Bool M₂.State y) (b : Bool) (hb : VirtualTag c.inputPos b)
    (p : Fin (x.length + 2)) (tapes : Fin M₁.k → ℤ → Option Bool)
    (heads : Fin M₁.k → ℤ) :
    ∃ b', VirtualTag (M₂.tm.step c).inputPos b' ∧
      (bufferedCompTM M₁ M₂).tm.step (bufferedSecondCfg M₁ M₂ c b p tapes heads) =
        bufferedSecondCfg M₁ M₂ (M₂.tm.step c) b' p tapes heads := by
  cases hq : c.state with
  | none =>
    refine ⟨b, ?_, ?_⟩
    · simpa only [MultiTapeTM.step_of_halt hq] using hb
    · rw [MultiTapeTM.step_of_halt hq, MultiTapeTM.step_of_halt]
      simp [bufferedSecondCfg, hq]
  | some q =>
    let a := M₂.tm.tr q c.inputSymbol c.workTapeSymbols
    let m := virtualMove b c.inputSymbol a.inputTape
    have hm := virtualMove_correct c b hb a.inputTape
    have hc : M₂.tm.step c = a.apply c := by
      simp only [MultiTapeTM.step, hq, a]
    refine ⟨virtualNextTag b m, ?_, ?_⟩
    · simpa only [hc, Action.apply] using hm.2
    · have hs : (bufferedSecondCfg M₁ M₂ c b p tapes heads).state =
          some (.inr (.inr (q, b))) := by simp [bufferedSecondCfg, hq]
      have hv : (bufferedSecondCfg M₁ M₂ c b p tapes heads).workTapeSymbols
          (Fin.natAdd M₁.k (Fin.castAdd M₂.k (0 : Fin 1))) = c.inputSymbol := by
        simp [bufferedSecondCfg, Cfg.workTapeSymbols, bufferTape_inputSymbol]
      have hr : (fun i => (bufferedSecondCfg M₁ M₂ c b p tapes heads).workTapeSymbols
          (Fin.natAdd M₁.k (Fin.natAdd 1 i))) = c.workTapeSymbols := by
        funext i
        simp [bufferedSecondCfg, Cfg.workTapeSymbols]
      unfold MultiTapeTM.step
      rw [hs]
      dsimp only [bufferedCompTM]
      rw [hv, hr, hq]
      change (Action.apply _ _) = bufferedSecondCfg M₁ M₂ (a.apply c) _ p tapes heads
      refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
      · funext i
        refine Fin.addCases ?_ ?_ i
        · intro j; simp [bufferedSecondCfg, Action.apply, a]
        · intro j
          refine Fin.addCases ?_ ?_ j <;> intro j <;>
            simp [bufferedSecondCfg, Action.apply, a]
      · funext i
        refine Fin.addCases ?_ ?_ i
        · intro j; simp [bufferedSecondCfg, Action.apply, a]
        · intro j
          refine Fin.addCases ?_ ?_ j
          · intro j
            simpa only [bufferedSecondCfg, Action.apply, tapeBlocks_buffer] using hm.1
          · intro j; simp [bufferedSecondCfg, Action.apply, a]

/-- Every second-phase run has a matching virtual run at the same time and a
valid arrival tag. This preserves completed outputs and absorbing halting. -/
lemma bufferedSecondCfg_run (M₁ M₂ : FinTM Bool) {x y : List Bool}
    (c : Cfg M₂.k Bool M₂.State y) (b : Bool) (hb : VirtualTag c.inputPos b)
    (p : Fin (x.length + 2)) (tapes : Fin M₁.k → ℤ → Option Bool)
    (heads : Fin M₁.k → ℤ) (t : ℕ) :
    ∃ b', VirtualTag (M₂.tm.runFrom c t).inputPos b' ∧
      (bufferedCompTM M₁ M₂).tm.runFrom (bufferedSecondCfg M₁ M₂ c b p tapes heads) t =
        bufferedSecondCfg M₁ M₂ (M₂.tm.runFrom c t) b' p tapes heads := by
  induction t with
  | zero => exact ⟨b, hb, rfl⟩
  | succ t ih =>
    obtain ⟨b', hb', he⟩ := ih
    obtain ⟨b'', hb'', he'⟩ := bufferedSecondCfg_step M₁ M₂ _ b' hb' p tapes heads
    refine ⟨b'', ?_, ?_⟩
    · simpa only [MultiTapeTM.runFrom_succ_eq_step'] using hb''
    · rw [MultiTapeTM.runFrom_succ_eq_step', he, he', MultiTapeTM.runFrom_succ_eq_step']

/-- The rewind scan configuration, with buffer head at `j - 1` and all second
machine tapes still blank. The scan state is always live, including at `j = 0`. -/
def bufferedScanCfg (M₁ M₂ : FinTM Bool) {x : List Bool} (y : List Bool)
    (p : Fin (x.length + 2)) (tapes : Fin M₁.k → ℤ → Option Bool)
    (heads : Fin M₁.k → ℤ) (j : ℕ) :
    Cfg (bufferedCompTM M₁ M₂).k Bool (bufferedCompTM M₁ M₂).State x where
  state := some (.inr (.inl ()))
  inputPos := p
  workTapes := tapeBlocks tapes (bufferTape y) (fun _ _ => none)
  workTapePos := tapeBlocks heads ((j : ℤ) - 1) (fun _ => 0)
  output := []

/-- Scanning from virtual position `j ≤ |y|` takes exactly `j + 1` transitions
to reach the second machine's initialized configuration with arrival tag true.

**Proof sketch.** At zero the buffer head is at the left blank, so move right
and dispatch. At successor `j + 1`, cell `j` contains a symbol; one left move
reduces to `j`. For an empty word, dispatch reaches its right blank with the
correct true tag, and its left blank remains one inward move away. -/
lemma bufferedScanCfg_run (M₁ M₂ : FinTM Bool) {x : List Bool} (y : List Bool)
    (p : Fin (x.length + 2)) (tapes : Fin M₁.k → ℤ → Option Bool)
    (heads : Fin M₁.k → ℤ) : ∀ j, j ≤ y.length →
    (bufferedCompTM M₁ M₂).tm.runFrom (bufferedScanCfg M₁ M₂ y p tapes heads j) (j + 1) =
      bufferedSecondCfg M₁ M₂ (M₂.tm.initCfg y) true p tapes heads := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero]
    simp only [MultiTapeTM.step, bufferedScanCfg, bufferedCompTM, Cfg.workTapeSymbols,
      tapeBlocks_buffer, Nat.cast_zero, zero_sub, bufferTape_left]
    refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [bufferedSecondCfg, Action.apply]
      · intro j
        refine Fin.addCases ?_ ?_ j <;> intro j <;>
          simp [bufferedSecondCfg, Action.apply]
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [bufferedSecondCfg, Action.apply]
      · intro j
        refine Fin.addCases ?_ ?_ j <;> intro j <;>
          simp [bufferedSecondCfg, Action.apply]
  | succ j ih =>
    intro hj
    have hread : bufferTape y (((j + 1 : ℕ) : ℤ) - 1) = some y[j] := by
      rw [show (((j + 1 : ℕ) : ℤ) - 1) = (j : ℤ) by omega,
        bufferTape_nat, List.getElem?_eq_getElem (by omega)]
    have hstep : (bufferedCompTM M₁ M₂).tm.step (bufferedScanCfg M₁ M₂ y p tapes heads (j + 1)) =
        bufferedScanCfg M₁ M₂ y p tapes heads j := by
      simp only [MultiTapeTM.step, bufferedScanCfg, bufferedCompTM, Cfg.workTapeSymbols,
        tapeBlocks_buffer, hread, Option.some_ne_none, if_false]
      refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
      · funext i
        refine Fin.addCases ?_ ?_ i
        · intro j; simp [Action.apply]
        · intro j
          refine Fin.addCases ?_ ?_ j <;> intro j <;> simp [Action.apply]
      · funext i
        refine Fin.addCases ?_ ?_ i
        · intro j; simp [Action.apply]
        · intro z
          refine Fin.addCases ?_ ?_ z <;> intro z <;> simp [Action.apply, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hstep]
    exact ih (by omega)

/-- From a completed first-phase configuration, rewind and dispatch cost exactly
`|output| + 2` steps. The first move is unconditional from the right blank.

**Proof sketch.** That first left move reaches scan position `|output|`. Apply
the scan invariant for the remaining `|output| + 1` transitions. The real output
stays empty and the native input head and first work block stay fixed. -/
lemma bufferedFirstCfg_rewind (M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg M₁.k Bool M₁.State x) (hs : c.state = none) :
    (bufferedCompTM M₁ M₂).tm.runFrom (bufferedFirstCfg M₁ M₂ c) (c.output.length + 2) =
      bufferedSecondCfg M₁ M₂ (M₂.tm.initCfg c.output) true c.inputPos c.workTapes c.workTapePos := by
  have hstep : (bufferedCompTM M₁ M₂).tm.step (bufferedFirstCfg M₁ M₂ c) =
      bufferedScanCfg M₁ M₂ c.output c.inputPos c.workTapes c.workTapePos c.output.length := by
    simp only [MultiTapeTM.step, bufferedFirstCfg, hs, bufferedCompTM]
    refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [bufferedScanCfg, Action.apply]
      · intro j
        refine Fin.addCases ?_ ?_ j <;> intro j <;> simp [bufferedScanCfg, Action.apply]
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [bufferedScanCfg, Action.apply]
      · intro j
        refine Fin.addCases ?_ ?_ j <;> intro j <;> simp [bufferedScanCfg, Action.apply, sub_eq_add_neg]
  rw [show c.output.length + 2 = (c.output.length + 1) + 1 by omega,
    MultiTapeTM.runFrom_succ_eq_step, hstep]
  exact bufferedScanCfg_run M₁ M₂ c.output c.inputPos c.workTapes c.workTapePos _ (le_refl _)

/-- Any completed first computation reaches the second phase within
`t₁ + |y| + 2` steps, with a fresh second work block and virtual input `y`.

**Proof sketch.** Choose the first halting time, which is at most `t₁`.
First-phase lockstep reaches its completed configuration, and determinism
identifies the output with `y`. The exact rewind lemma supplies `|y| + 2` more
steps, retaining the first block and parked native input head. -/
lemma bufferedComp_start (M₁ M₂ : FinTM Bool) (x y : List Bool) (t₁ : ℕ)
    (h₁ : M₁.ComputesInTime x y t₁) :
    ∃ (a : ℕ) (p : Fin (x.length + 2)) (tapes : Fin M₁.k → ℤ → Option Bool)
      (heads : Fin M₁.k → ℤ), a ≤ t₁ + y.length + 2 ∧
      (bufferedCompTM M₁ M₂).tm.runFrom ((bufferedCompTM M₁ M₂).tm.initCfg x) a =
        bufferedSecondCfg M₁ M₂ (M₂.tm.initCfg y) true p tapes heads := by
  classical
  have hh : ∃ t, (M₁.tm.runFrom (M₁.tm.initCfg x) t).state = none :=
    ⟨t₁, ((computesInTime_iff M₁ x y t₁).mp h₁).1⟩
  let t := Nat.find hh
  let c := M₁.tm.runFrom (M₁.tm.initCfg x) t
  have hs : c.state = none := Nat.find_spec hh
  have ht : t ≤ t₁ := Nat.find_min' hh ((computesInTime_iff M₁ x y t₁).mp h₁).1
  have hc : M₁.ComputesInTime x c.output t :=
    (computesInTime_iff _ _ _ _).mpr ⟨hs, rfl⟩
  have ho : c.output = y := hc.output_unique h₁
  refine ⟨t + (y.length + 2), c.inputPos, c.workTapes, c.workTapePos, by omega, ?_⟩
  rw [MultiTapeTM.runFrom_add, bufferedFirstCfg_init,
    bufferedFirstCfg_run M₁ M₂ _ t (fun s hs => Nat.find_min hh hs)]
  have hf := bufferedFirstCfg_rewind M₁ M₂ c hs
  cases ho
  exact hf

end Turing.FinTM

/-! ### Machine-agreement transfer (§13, Z5)

Two machines over the same tape count and state type whose transition
tables agree on a set of control states run identically for as long as the
run's control stays inside that set. This is the `hagree` genre of
`Turing.capture_run`/`Turing.emit_run` made standalone: those lemmas carry
a per-state agreement hypothesis for one specific wrapper, re-proved ad hoc
at every host; the standalone form transfers whole runs between any two
agreeing tables (design `machine-library-design.md` §13, item Z5; decision
D-R3). First customers: the forwarding loop host of `Build/Loop.lean`
(whose fourteen phase lemmas are verbatim re-proofs of the capturing
host's, since the two tables agree on every non-body state) and the
guarded `clSlot_run` agreement sites of `CookLevin/Hardness.lean`. -/

namespace Turing.MultiTapeTM

/-- The two transition tables agree on every control state in `Q`: from any
such state, both machines take the identical action on identical reads.
Nothing is assumed about states outside `Q`, about `q₀`, or about
halting. -/
def AgreeOn {k : ℕ} {Symbol State : Type*} (M N : MultiTapeTM k Symbol State)
    (Q : Set State) : Prop :=
  ∀ q ∈ Q, ∀ inp work, M.tr q inp work = N.tr q inp work

/-- One step transfers across an agreement: if the configuration's control
state (when live) lies in the agreement set, both machines step it to the
same configuration. Halted configurations step to themselves on both sides.

**Proof sketch.** On `c.state = none` both steps are the identity. On
`c.state = some q` with `q ∈ Q`, unfold `step`: both sides apply the same
action `M.tr q c.inputSymbol c.workTapeSymbols = N.tr q …` to `c`. -/
theorem step_eq_of_agreeOn {k : ℕ} {Symbol State : Type*}
    {M N : MultiTapeTM k Symbol State} {Q : Set State}
    (h : M.AgreeOn N Q) {input : List Symbol} (c : Cfg k Symbol State input)
    (hq : ∀ q, c.state = some q → q ∈ Q) :
    N.step c = M.step c := by
  cases hs : c.state with
  | none => simp only [step_of_halt hs]
  | some q =>
    simp only [step, hs]
    rw [h q (hq q hs)]

/-- A whole run transfers across an agreement: if every control state the
`M`-run visits strictly before time `t` lies in the agreement set, the two
runs coincide at time `t` (and hence at every earlier time, by
instantiating `t`). The endpoint itself may leave the set or halt; no
liveness is assumed, and `t = 0` is the trivial case.

**Proof sketch.** Induct on `t`. The inductive hypothesis transfers the
run at `t`; the visit hypothesis at `u = t` puts its live control in `Q`,
so `step_eq_of_agreeOn` transfers the final step. Halted intermediate
configurations step identically on both sides without the hypothesis. -/
theorem runFrom_eq_of_agreeOn {k : ℕ} {Symbol State : Type*}
    {M N : MultiTapeTM k Symbol State} {Q : Set State}
    (h : M.AgreeOn N Q) {input : List Symbol} (c : Cfg k Symbol State input)
    (t : ℕ) (hq : ∀ u < t, ∀ q, (M.runFrom c u).state = some q → q ∈ Q) :
    N.runFrom c t = M.runFrom c t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [runFrom_succ_eq_step', ih (fun u hu => hq u (by omega)),
      runFrom_succ_eq_step']
    exact step_eq_of_agreeOn h _ (hq t (by omega))

end Turing.MultiTapeTM
```

## ===== TCSlib/Complexity/TuringMachine/Build/Convention.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Simulation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: the calling convention

The vocabulary module of the machine-construction library
(`machine-library-design.md`, design frozen 2026-10-03): the single seam
notion that the library's control combinators speak, plus the pure list/
arithmetic functions that the primitive contracts in
`TCSlib.Complexity.TuringMachine.Build.Primitives` are stated against.

**Status: proved.** This module is fully proved (definitions and two
glue lemmas), and the sibling `Build` modules' contracts stated against
it are now all proved as well (library fill batches and the emitter
increment; zero sorries). The `Build` surface was new Chapter-1 growth,
audited in the shared infrastructure and emitter rounds
(`audits/ch1-infra-*`, `audits/emitter-*`).

## The seam notion

The model already gives *whole* machines a clean boundary: read-only input,
blank work tapes, append-only output, start at `Turing.MultiTapeTM.initCfg`.
The library therefore needs a configuration discipline only where a
construction crosses an *internal* seam — the round boundary of the loop
combinator and the entry of a wrapped subroutine. `Turing.Cfg.ofWords` is
that discipline: control at a designated anchor, input head at its initial
position, every work tape holding one word from the origin
(`Turing.FinTM.bufferTape`) with its head at the origin, output empty. A
loop body's contract is "`ofWords` in, `ofWords` out", and — per the frozen
design decision — the body *restores its own scratch to blank* (its scratch
words are `[]` on both sides of the contract) rather than relying on a
generic clearing pass.

## Main definitions

* `Turing.Cfg.ofWords` — the canonical seam configuration: anchor state,
  input head at 1, work tape `i` holding word `w i` from the origin, heads
  at the origin, empty output.
* `Turing.splitAtLastTrue` — strip a marker suffix: the prefix before the
  last `true`, or `none` if the word is all `false` (the audited marker
  discipline of the Chapter-2 Exercise-2.1 construction).
* `Turing.solveSplit` — least solution `i ≤ n` of the padding length
  equation `i + C·(i+1)^e = n`, or `none` (the split-search discipline of
  the padding constructions).
* `Turing.incFixed` — little-endian fixed-width binary increment with
  explicit overflow (`none`), width preserved (the enumerator's counter
  discipline; width zero overflows immediately).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2: the k-tape machine model the
  seams are stated over.)
-/

namespace Turing

variable {k : ℕ} {State : Type*}

/-- The canonical seam configuration of the machine-construction library:
control at the anchor state `q`, input head at its initial position `1`,
work tape `i` holding the word `w i` written from the origin
(`Turing.FinTM.bufferTape`), every work head at the origin, and the output
empty. Loop-round and wrapper-entry contracts are stated as equations
between `runFrom` results and `ofWords` configurations; a body that owns
scratch tapes lists them with word `[]` on both sides of its contract
(body-restores-scratch, the frozen design decision 9.2). -/
def Cfg.ofWords {input : List Bool} (q : State) (w : Fin k → List Bool) :
    Cfg k Bool State input :=
  ⟨some q, 1, fun i => FinTM.bufferTape (w i), fun _ => 0, []⟩

/-- A machine's genuine initial configuration is the seam configuration at
its start state with every tape word empty: `Cfg.init` has blank tapes and
`Turing.FinTM.bufferTape [] = fun _ => none`. This is the lemma that lets a
combinator's startup phase begin from a seam rather than from a bespoke
initialization invariant. -/
lemma initCfg_ofWords (tm : MultiTapeTM k Bool State) (x : List Bool) :
    tm.initCfg x = Cfg.ofWords tm.q₀ (fun _ => []) := by
  simp only [MultiTapeTM.initCfg, Cfg.init, Cfg.ofWords, FinTM.bufferTape_nil]

/-- The seam words of a configuration are read back literally: at a seam,
work tape `i` holds exactly `w i` on cells `0, …, |w i| − 1` and blanks
elsewhere. Unfolds `Cfg.ofWords` for consumers that reason cell-wise. -/
lemma Cfg.ofWords_workTapes {input : List Bool} (q : State)
    (w : Fin k → List Bool) (i : Fin k) :
    (Cfg.ofWords (input := input) q w).workTapes i = FinTM.bufferTape (w i) :=
  rfl

/-- Strip a marker suffix: the prefix of `v` before its **last** `true`, or
`none` when `v` is all `false`. This is the Chapter-2 Exercise-2.1 marker
discipline (split at the last `true`; an all-`false` certificate region is
a rejection), stated once as a pure function so that machine contracts and
the chapter-side semantic lemmas name the same operation. -/
def splitAtLastTrue (v : List Bool) : Option (List Bool) :=
  match v.reverse.dropWhile (fun b => !b) with
  | true :: rest => some rest.reverse
  | _ => none

/-- Least index `i ≤ n` solving the padding length equation
`i + C·(i+1)^e = n`, or `none` when no solution exists. Strict monotonicity
of `i ↦ i + C·(i+1)^e` makes the solution unique; the machine contract
`Turing.FinTM.computesFunInTime_splitSolve` performs this bounded search. -/
def solveSplit (C e n : ℕ) : Option ℕ :=
  (List.range (n + 1)).find? fun i => i + C * (i + 1) ^ e == n

/-- Little-endian fixed-width binary increment with explicit overflow:
`incFixed w` is the successor word of the same length, or `none` when `w`
is all `true` (overflow) — in particular width zero overflows immediately,
matching the enumerator's audited counter discipline. -/
def incFixed : List Bool → Option (List Bool)
  | [] => none
  | false :: rest => some (true :: rest)
  | true :: rest => (incFixed rest).map (false :: ·)

/-- **Emitter-increment vocabulary** (design §11): least
solution `i ≤ n` of the width-parametric split equation `i + f i = n`, or
`none` — the generalization of `Turing.solveSplit` from the hardwired
polynomial family to an arbitrary width function. At
`f = fun i => C * (i + 1) ^ e` this definitionally recovers
`solveSplit C e n`. Customers: the 3A-continuation's exponential padding
equation (through `computesFunInTime_splitSolveWith`) and later padding
arguments. No machine content: `List.range` search, first match. -/
def solveSplitWith (f : ℕ → ℕ) (n : ℕ) : Option ℕ :=
  (List.range (n + 1)).find? fun i => i + f i == n

/-- **Emitter-increment vocabulary** (design §11): split off
the leading unary token — the maximal `true`-prefix together with its
terminating `false` delimiter — returning the token and the remainder. A
word with no delimiter yields the whole word as an unterminated token with
empty remainder; the empty word yields two empty words; a leading `false`
is the length-zero token `[false]`. This operation consumes **unary
tokens** — the shared atom of the serialization grammars (unary indices
with terminators). It does not consume standalone single-bit markers or
polarity bits: `unaryTokenSplit [true, false, true] =
([true, false], [true])`, a terminated unary-one token, not a lone
`true` marker — scanners handle markers and polarity by their own
grammar states (emitter-infra round-1 audit, finding 4). Customers: the
3B continuation's streaming scanner, the Cook-Levin emitter's index
reads (4A), 4B's dual scanner. No machine content: structural recursion
on the word. -/
def unaryTokenSplit : List Bool → List Bool × List Bool
  | [] => ([], [])
  | false :: rest => ([false], rest)
  | true :: rest =>
    let (tok, r) := unaryTokenSplit rest
    (true :: tok, r)

end Turing
```

## ===== TCSlib/Complexity/TuringMachine/Build/Catalog.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.DeriveFintype
import TCSlib.Complexity.TuringMachine.Build.Loop
import TCSlib.Complexity.TuringMachine.Encoding

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: catalog promotions and space annotations (R3)

The R3 increment of the machine-construction library
(`machine-library-design.md` §12): the remaining audited A-chain tape
routines promoted as public machines with exact time **and** space costs,
plus the space retro-annotation of the existing catalog and control
surface. Per frozen decision 12.2 this lives in a **new** file — the new
rows and the space lemmas for the old rows both — keeping
`Build/Primitives.lean` byte-identical; the later refactor toward a
per-theme layout is a recorded backlog item.

**Status: statement skeleton (§12 statement phase).** The five routine
machines and their two phase alphabets are real definitions (TM1-style
labelled control, the catalog's house idiom); every contract is sorried,
each with a proof sketch naming its fill obligations.

## Part 1 — new promotions (seam routines)

Configuration-level routines at the `Turing.Cfg.ofWords` seam of
`TCSlib.Complexity.TuringMachine.Build.Convention`, entering at their
start anchor with heads at the origin and exiting at a **live** anchor
(first-return cut included in each contract), so they compose under
`Turing.seamCompTM`. These are D6-style promotions of the audited 4A
privates — the A3 chain proved `3|w| + 3` copy and `2|w| + 2` clear,
matching the external prior art's catalog to within one step
(independent convergence, 2026-10-06 survey; [Bon26], the
transfer/clear/copy routine catalog):

* `Turing.transferTM` — move a word from tape `src` to tape `dst`
  (source erased), within `3|w| + 3`.
* `Turing.copyTM` — copy a word from tape `src` to tape `dst` (source
  kept), within `3|w| + 3`.
* `Turing.clearTM` — blank the word on one tape, within `2|w| + 2`.
* `Turing.compareTM` — word equality of two tapes, verdict in the exit
  anchor, tapes restored, within `2·min(|u|,|v|) + 2`.
* `Turing.incrementTM` — in-place little-endian fixed-width increment
  (`Turing.incFixed`), success/overflow in the exit anchor, within
  `2|w| + 2`; on overflow the word wraps to all-`false`.

Each routine carries per-tape space statements
(`Turing.MultiTapeTM.spaceUsedByTape`): the touched tapes visit at most
the word interval plus the two boundary blanks, and every other tape
stays at its origin singleton.

## Part 2 — space retro-annotation

Per frozen decision 12.3, the existing catalog rows (P1–P15 as realized)
and the control combinators W1–W3 and L receive `spaceUsed` theorems in
this increment, with no signature changes and no edits to the home files:
each annotation restates the audited row's existential contract joined
with a space clause on the same witness, so the audited statement surface
is untouched (additive growth). The emitter combinators (E1/E2/E3′/E4′ —
`exists_emitLoopTM`, `emit_run`/`exists_emitCallTM`, the stream rows
P16–P18, `splitSolveWith`) stay lazy until a space consumer appears.

## Main definitions

* `Turing.SweepPhase`, `Turing.FlagPhase` — the two phase alphabets.
* `Turing.transferTM`, `Turing.copyTM`, `Turing.clearTM`,
  `Turing.compareTM`, `Turing.incrementTM`.

## Main results

All sorried (statement phase): the five routines' run and per-tape space
contracts (`*_run`, `*_spaceUsedByTape`); the catalog space rows
`Turing.FinTM.computesFunInTime_*_spaceUsed` (P1–P15 as realized,
including the threaded-map row with its payload space hypothesis); and
the control-layer rows `Turing.capture_visitedByTapeHead` (W1),
`Turing.FinTM.redirectTM_spaceUsedByTape` (W2),
`Turing.FinTM.computesFunInTime_cond_spaceUsed` (W3), and
`Turing.FinTM.exists_loopTM_spaceUsed` (L).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2–§1.4: the routines are the
  folklore tape subroutines of the textbook's simulation arguments;
  Definition 4.1: the visited-cells space measure the annotations use.)
* [Bon26] É. Bonnet, *classical-complexity*, Lax Archive entry lax-434930,
  module `proofs/Lax434930Proofs/InclusionAux/TimeCompiler/`, commit
  `0c0840319318215fd7b36a9a822b81ce55cf6941`, Apache-2.0, examined
  2026-10-05. Design adaptation with nothing transcribed (different
  toolchain and machine model — TM2-style keyed stacks there, `FinTM`
  tapes with heads here): the transfer/clear/copy/compare routine catalog
  and its exact-cost discipline.
-/

namespace Turing

/-- Phase alphabet of the sweep-shaped routines (`Turing.transferTM`,
`Turing.copyTM`, `Turing.clearTM`): a forward pass over the stored word,
a return pass to the origin, and the live exit anchor. -/
inductive SweepPhase where
  /-- the forward pass over the stored word -/
  | sweep
  /-- the return pass back to the origin -/
  | rewind
  /-- the live exit anchor -/
  | done
deriving DecidableEq, Fintype

/-- Phase alphabet of the verdict-bearing routines (`Turing.compareTM`,
`Turing.incrementTM`): a forward working pass, a return pass carrying the
verdict, and a pair of live exit anchors indexed by the verdict. -/
inductive FlagPhase where
  /-- the forward working pass -/
  | run
  /-- the return pass, carrying the verdict -/
  | rewind (flag : Bool)
  /-- the live exit anchors, one per verdict -/
  | done (flag : Bool)
deriving DecidableEq, Fintype

variable {k : ℕ} {x : List Bool}

/-- **R3, transfer** (design §12; [Bon26]). Move the word stored on tape
`src` to tape `dst`: a forward pass copies cell by cell (both heads in
lockstep), the turn at the source's right blank starts the return pass,
which erases the source on the way back, and the overshoot to the left
blank steps right into the live `done` anchor with both heads at the
origin. -/
def transferTM (k : ℕ) (src dst : Fin k) : MultiTapeTM k Bool SweepPhase where
  q₀ := .sweep
  tr := fun q _ w =>
    match q with
    | .sweep =>
      match w src with
      | some b =>
        ⟨0, fun j => if j = dst then (some (some b), SignType.pos)
            else if j = src then (none, SignType.pos) else (none, 0),
          none, some .sweep⟩
      | none =>
        ⟨0, fun j => if j = src ∨ j = dst then (none, SignType.neg)
            else (none, 0), none, some .rewind⟩
    | .rewind =>
      match w src with
      | some _ =>
        ⟨0, fun j => if j = src then (some none, SignType.neg)
            else if j = dst then (none, SignType.neg) else (none, 0),
          none, some .rewind⟩
      | none =>
        ⟨0, fun j => if j = src ∨ j = dst then (none, SignType.pos)
            else (none, 0), none, some .done⟩
    | .done => ⟨0, fun _ => (none, 0), none, some .done⟩

/-- **R3, copy** (design §12; [Bon26]; the A3 chain's `3|w| + 3` row).
Copy the word stored on tape `src` onto tape `dst`, keeping the source:
the same two-pass sweep as `Turing.transferTM` without the erasure on the
return pass. -/
def copyTM (k : ℕ) (src dst : Fin k) : MultiTapeTM k Bool SweepPhase where
  q₀ := .sweep
  tr := fun q _ w =>
    match q with
    | .sweep =>
      match w src with
      | some b =>
        ⟨0, fun j => if j = dst then (some (some b), SignType.pos)
            else if j = src then (none, SignType.pos) else (none, 0),
          none, some .sweep⟩
      | none =>
        ⟨0, fun j => if j = src ∨ j = dst then (none, SignType.neg)
            else (none, 0), none, some .rewind⟩
    | .rewind =>
      match w src with
      | some _ =>
        ⟨0, fun j => if j = src ∨ j = dst then (none, SignType.neg)
            else (none, 0), none, some .rewind⟩
      | none =>
        ⟨0, fun j => if j = src ∨ j = dst then (none, SignType.pos)
            else (none, 0), none, some .done⟩
    | .done => ⟨0, fun _ => (none, 0), none, some .done⟩

/-- **R3, clear** (design §12; [Bon26]; P12's engine, the A3 chain's
`2|w| + 2` row, and the frozen §3 scratch discipline's supporting
primitive). Blank the word on tape `i`: a forward pass to the right blank,
then a return pass erasing each cell, with the left-blank overshoot
stepping right into the live `done` anchor at the origin. -/
def clearTM (k : ℕ) (i : Fin k) : MultiTapeTM k Bool SweepPhase where
  q₀ := .sweep
  tr := fun q _ w =>
    match q with
    | .sweep =>
      match w i with
      | some _ =>
        ⟨0, fun j => if j = i then (none, SignType.pos) else (none, 0),
          none, some .sweep⟩
      | none =>
        ⟨0, fun j => if j = i then (none, SignType.neg) else (none, 0),
          none, some .rewind⟩
    | .rewind =>
      match w i with
      | some _ =>
        ⟨0, fun j => if j = i then (some none, SignType.neg) else (none, 0),
          none, some .rewind⟩
      | none =>
        ⟨0, fun j => if j = i then (none, SignType.pos) else (none, 0),
          none, some .done⟩
    | .done => ⟨0, fun _ => (none, 0), none, some .done⟩

/-- **R3, compare** (design §12; [Bon26]; the 4A chain's `clCmp*` shape).
Test the words on tapes `fst` and `snd` for equality, read-only: a
lockstep forward scan compares cell by cell — the first mismatch (a
differing pair, or one word ending early) selects the `false` verdict, a
simultaneous double blank selects `true` — then a return pass guided by
`fst`'s intact content carries the verdict to the live `done` anchor with
both heads at the origin and both words untouched. -/
def compareTM (k : ℕ) (fst snd : Fin k) : MultiTapeTM k Bool FlagPhase where
  q₀ := .run
  tr := fun q _ w =>
    match q with
    | .run =>
      match w fst, w snd with
      | some a, some b =>
        if a = b then
          ⟨0, fun j => if j = fst ∨ j = snd then (none, SignType.pos)
              else (none, 0), none, some .run⟩
        else
          ⟨0, fun j => if j = fst ∨ j = snd then (none, SignType.neg)
              else (none, 0), none, some (.rewind false)⟩
      | none, none =>
        ⟨0, fun j => if j = fst ∨ j = snd then (none, SignType.neg)
            else (none, 0), none, some (.rewind true)⟩
      | _, _ =>
        ⟨0, fun j => if j = fst ∨ j = snd then (none, SignType.neg)
            else (none, 0), none, some (.rewind false)⟩
    | .rewind v =>
      match w fst with
      | some _ =>
        ⟨0, fun j => if j = fst ∨ j = snd then (none, SignType.neg)
            else (none, 0), none, some (.rewind v)⟩
      | none =>
        ⟨0, fun j => if j = fst ∨ j = snd then (none, SignType.pos)
            else (none, 0), none, some (.done v)⟩
    | .done v => ⟨0, fun _ => (none, 0), none, some (.done v)⟩

/-- **R3, increment** (design §12; [Bon26]; the enumerator's
`enumCarryTM` discipline in place, cf. the string-function row
`Turing.FinTM.computesFunInTime_incFixed`). In-place little-endian
fixed-width binary increment on tape `i`: the carry pass flips `true`
cells to `false` moving right; the first `false` flips to `true` and
selects the success verdict; running off the width (all `true`) selects
the overflow verdict, leaving the wrapped all-`false` word — the
enumerator's counter convention. The return pass carries the verdict to
the live `done` anchor at the origin. -/
def incrementTM (k : ℕ) (i : Fin k) : MultiTapeTM k Bool FlagPhase where
  q₀ := .run
  tr := fun q _ w =>
    match q with
    | .run =>
      match w i with
      | some true =>
        ⟨0, fun j => if j = i then (some (some false), SignType.pos)
            else (none, 0), none, some .run⟩
      | some false =>
        ⟨0, fun j => if j = i then (some (some true), SignType.neg)
            else (none, 0), none, some (.rewind true)⟩
      | none =>
        ⟨0, fun j => if j = i then (none, SignType.neg) else (none, 0),
          none, some (.rewind false)⟩
    | .rewind v =>
      match w i with
      | some _ =>
        ⟨0, fun j => if j = i then (none, SignType.neg) else (none, 0),
          none, some (.rewind v)⟩
      | none =>
        ⟨0, fun j => if j = i then (none, SignType.pos) else (none, 0),
          none, some (.done v)⟩
    | .done v => ⟨0, fun _ => (none, 0), none, some (.done v)⟩

/-- Configuration at a scan position, with explicit words and head positions. -/
private def catalogCfg {S : Type*} (q : S) (w : Fin k → List Bool)
    (heads : Fin k → ℤ) : Cfg k Bool S x :=
  { Cfg.ofWords q w with workTapePos := heads }

/-- The chronological trace of a forward scan, left turn, return, and entry.
The return index is the number of nonblank cells still to erase or cross. -/
private def catalogTrace {S : Type*} (F R : ℕ → Cfg k Bool S x)
    (D : Cfg k Bool S x) (L t : ℕ) : Cfg k Bool S x :=
  if t ≤ L then F t else if t ≤ 2 * L + 1 then R (2 * L + 1 - t) else D

/-- Local transition equations determine the complete trace, including all
stationary steps after the exit. **Proof sketch.** Induct on elapsed time;
split at the forward endpoint, return endpoint, and stationary tail. -/
private lemma catalog_trace_run {S : Type*} (M : MultiTapeTM k Bool S)
    (F R : ℕ → Cfg k Bool S x) (D : Cfg k Bool S x) (L : ℕ)
    (hF : ∀ r < L, M.step (F r) = F (r + 1))
    (hturn : M.step (F L) = R L)
    (hR : ∀ r < L, M.step (R (r + 1)) = R r)
    (hentry : M.step (R 0) = D) (hD : M.step D = D) (t : ℕ) :
    M.runFrom (F 0) t = catalogTrace F R D L t := by
  induction t with
  | zero => simp [catalogTrace]
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih]
    by_cases h₁ : t < L
    · simpa [catalogTrace, show t ≤ L by omega, show t + 1 ≤ L by omega]
        using hF t h₁
    · by_cases h₂ : t = L
      · subst t
        simpa [catalogTrace, show ¬L + 1 ≤ L by omega,
          show L + 1 ≤ 2 * L + 1 by omega, show 2 * L + 1 - (L + 1) = L by omega]
          using hturn
      · by_cases h₃ : t < 2 * L + 1
        · have he : 2 * L + 1 - t = (2 * L - t) + 1 := by omega
          simpa [catalogTrace, show ¬t ≤ L by omega, show ¬t + 1 ≤ L by omega,
            show t ≤ 2 * L + 1 by omega, show t + 1 ≤ 2 * L + 1 by omega,
            he, show 2 * L + 1 - (t + 1) = 2 * L - t by omega]
            using hR (2 * L - t) (by omega)
        · by_cases h₄ : t = 2 * L + 1
          · subst t
            simpa [catalogTrace, show ¬2 * L + 1 ≤ L by omega,
              show ¬2 * L + 1 + 1 ≤ L by omega] using hentry
          · simpa [catalogTrace, show ¬t ≤ L by omega,
              show ¬t + 1 ≤ L by omega, show ¬t ≤ 2 * L + 1 by omega,
              show ¬t + 1 ≤ 2 * L + 1 by omega] using hD

/-- A head confined to the inclusive interval from minus one to `L` visits
at most `L+2` cells. -/
private lemma catalog_space_bound {S : Type*} (M : MultiTapeTM k Bool S)
    (c : Cfg k Bool S x) (L t : ℕ) (i : Fin k)
    (h : ∀ u, -1 ≤ (M.runFrom c u).workTapePos i ∧
      (M.runFrom c u).workTapePos i ≤ (L : ℤ)) :
    M.spaceUsedByTape c t i ≤ L + 2 := by
  have hs : M.visitedByTapeHead c t i ⊆ Finset.Icc (-1 : ℤ) (L : ℤ) := by
    intro z hz
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_Icc.mpr (h u)
  exact (Finset.card_le_card hs).trans (by rw [Int.card_Icc]; omega)

/-- A head stationary at zero has exactly its origin singleton as visited set. -/
private lemma catalog_space_one {S : Type*} (M : MultiTapeTM k Bool S)
    (c : Cfg k Bool S x) (t : ℕ) (i : Fin k)
    (h : ∀ u, (M.runFrom c u).workTapePos i = 0) :
    M.spaceUsedByTape c t i = 1 := by
  simp only [MultiTapeTM.spaceUsedByTape, MultiTapeTM.visitedByTapeHead, h]
  rw [Finset.image_const Finset.nonempty_range_add_one]
  rfl

/-- Erasing the last cell of a prefix shortens that prefix by one.
**Proof sketch.** Read the last cell, earlier cells, and outside cells separately. -/
private lemma catalog_erase_take (w : List Bool) (r : ℕ) (hr : r < w.length) :
    Function.update (FinTM.bufferTape (w.take (r + 1))) (r : ℤ) none =
      FinTM.bufferTape (w.take r) := by
  funext z
  by_cases hz : z = (r : ℤ)
  · subst z
    simp [FinTM.bufferTape, List.getElem?_eq_none]
  · rw [Function.update_of_ne hz]
    by_cases h0 : 0 ≤ z
    · simp only [FinTM.bufferTape, if_pos h0]
      by_cases hzr : z.toNat < r
      · simp [List.getElem?_take, hzr, show z.toNat < r + 1 by omega]
      · have hzr' : r + 1 ≤ z.toNat := by omega
        rw [List.getElem?_eq_none (by simp; omega),
          List.getElem?_eq_none (by simp; omega)]
    · simp [FinTM.bufferTape, h0]

/-- Appending the next original bit extends a copied prefix by one. -/
private lemma catalog_write_take (w : List Bool) (r : ℕ) (hr : r < w.length) :
    Function.update (FinTM.bufferTape (w.take r)) (r : ℤ) (some w[r]) =
      FinTM.bufferTape (w.take (r + 1)) := by
  rw [List.take_succ_eq_append_getElem hr]
  simpa only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hr)] using
    (FinTM.bufferTape_append (w.take r) w[r]).symm

/-- Clear's forward phase has intact words; the return phase retains exactly
the unerased prefix below and at the head. -/
private def catalogClearF (i : Fin k) (w : Fin k → List Bool) (r : ℕ) :
    Cfg k Bool SweepPhase x :=
  catalogCfg .sweep w (fun j => if j = i then (r : ℤ) else 0)

/-- Clear's return index counts the remaining unerased cells. -/
private def catalogClearR (i : Fin k) (w : Fin k → List Bool) (r : ℕ) :
    Cfg k Bool SweepPhase x :=
  catalogCfg .rewind (Function.update w i ((w i).take r))
    (fun j => if j = i then (r : ℤ) - 1 else 0)

/-- Clear's exact phase invariant. **Proof sketch.** During the scan the
word is intact. The turn reads its right blank. Each return transition erases
just the last remaining cell; the final left blank makes the right-entry. -/
private lemma catalog_clear_trace (i : Fin k) (w : Fin k → List Bool) (t : ℕ) :
    (clearTM k i).runFrom (Cfg.ofWords (input := x) .sweep w) t =
      catalogTrace (catalogClearF i w) (catalogClearR i w)
        (Cfg.ofWords .done (Function.update w i [])) (w i).length t := by
  have h0 : catalogClearF (x := x) i w 0 = Cfg.ofWords .sweep w := by
    apply Cfg.ext <;> simp [catalogClearF, catalogCfg, Cfg.ofWords]
  rw [← h0]
  apply catalog_trace_run
  · intro r hr
    have hs : (catalogClearF (x := x) i w r).workTapeSymbols i = some (w i)[r] := by
      simp [catalogClearF, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols,
        FinTM.bufferTape_nat, List.getElem?_eq_getElem hr]
    change ((clearTM k i).tr .sweep _ _).apply _ = _
    simp only [clearTM, hs]
    apply Cfg.ext <;> simp [Action.apply, catalogClearF, catalogCfg, Cfg.ofWords]
    all_goals
      funext j
      split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg] <;> omega
  · have hs : (catalogClearF (x := x) i w (w i).length).workTapeSymbols i = none := by
      simp [catalogClearF, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols]
    change ((clearTM k i).tr .sweep _ _).apply _ = _
    simp only [clearTM, hs]
    apply Cfg.ext <;> simp [Action.apply, catalogClearF, catalogClearR, catalogCfg, Cfg.ofWords]
    · funext j
      by_cases hj : j = i <;> simp [hj]
    · funext j
      split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg]
  · intro r hr
    have hs : (catalogClearR (x := x) i w (r + 1)).workTapeSymbols i =
        some (w i)[r] := by
      simp [catalogClearR, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols,
        show (r + 1 : ℕ) - (1 : ℤ) = (r : ℤ) by omega,
        List.getElem?_take, List.getElem?_eq_getElem hr]
    change ((clearTM k i).tr .rewind _ _).apply _ = _
    simp only [clearTM, hs]
    apply Cfg.ext <;> simp [Action.apply, catalogClearF, catalogClearR, catalogCfg, Cfg.ofWords]
    · funext j
      by_cases hj : j = i
      · subst j
        simpa [show ((r + 1 : ℕ) : ℤ) - 1 = (r : ℤ) by omega] using
          catalog_erase_take (w i) r hr
      · simp [hj]
    · funext j
      split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg] <;> omega
  · apply Cfg.ext <;>
      simp [MultiTapeTM.step, clearTM, catalogClearR, catalogCfg, Cfg.ofWords,
        Cfg.workTapeSymbols, Action.apply]
    all_goals
      funext j
      split_ifs <;> simp_all [SignType.cast]
  · apply Cfg.ext <;>
      simp [MultiTapeTM.step, clearTM, Cfg.ofWords, Action.apply]

/-- Copy and transfer share the forward phase: the destination holds the copied
prefix and the source remains intact, with both heads at its end. -/
private def catalogCopyF (src dst : Fin k) (w : Fin k → List Bool) (r : ℕ) :
    Cfg k Bool SweepPhase x :=
  catalogCfg .sweep (Function.update w dst ((w src).take r))
    (fun j => if j = src ∨ j = dst then (r : ℤ) else 0)

/-- During copy's return the words are complete and unchanged. -/
private def catalogCopyR (src dst : Fin k) (w : Fin k → List Bool) (r : ℕ) :
    Cfg k Bool SweepPhase x :=
  catalogCfg .rewind (Function.update w dst (w src))
    (fun j => if j = src ∨ j = dst then (r : ℤ) - 1 else 0)

/-- During transfer's return the source retains exactly the unerased prefix. -/
private def catalogTransferR (src dst : Fin k) (w : Fin k → List Bool) (r : ℕ) :
    Cfg k Bool SweepPhase x :=
  catalogCfg .rewind (Function.update (Function.update w src ((w src).take r)) dst (w src))
    (fun j => if j = src ∨ j = dst then (r : ℤ) - 1 else 0)

/-- The common forward transition copies exactly the next source bit. -/
private lemma catalog_copy_forward (src dst : Fin k) (hne : src ≠ dst)
    (w : Fin k → List Bool) (r : ℕ) (hr : r < (w src).length) :
    (copyTM k src dst).step (catalogCopyF (x := x) src dst w r) =
      catalogCopyF src dst w (r + 1) := by
  have hs : (catalogCopyF (x := x) src dst w r).workTapeSymbols src =
      some (w src)[r] := by
    simp [catalogCopyF, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols, hne,
      List.getElem?_eq_getElem hr]
  change ((copyTM k src dst).tr .sweep _ _).apply _ = _
  simp only [copyTM, hs]
  apply Cfg.ext <;> simp [Action.apply, catalogCopyF, catalogCfg, Cfg.ofWords]
  · funext j
    by_cases hj : j = dst
    · subst j
      simpa using catalog_write_take (w src) r hr
    · by_cases hs : j = src <;> simp [hj, hs, hne, Ne.symm hne]
  · funext j
    by_cases hd : j = dst <;> by_cases hs : j = src <;>
      simp [hd, hs, hne, SignType.cast] <;> omega

/-- Copy's exact phase invariant, including the stationary exit. -/
private lemma catalog_copy_trace (src dst : Fin k) (hne : src ≠ dst)
    (w : Fin k → List Bool) (hdst : w dst = []) (t : ℕ) :
    (copyTM k src dst).runFrom (Cfg.ofWords (input := x) .sweep w) t =
      catalogTrace (catalogCopyF src dst w) (catalogCopyR src dst w)
        (Cfg.ofWords .done (Function.update w dst (w src))) (w src).length t := by
  have h0 : catalogCopyF (x := x) src dst w 0 = Cfg.ofWords .sweep w := by
    apply Cfg.ext <;> simp [catalogCopyF, catalogCfg, Cfg.ofWords]
    funext j
    by_cases hj : j = dst
    · subst j; simp [hdst]
    · simp [hj]
  rw [← h0]
  apply catalog_trace_run
  · exact catalog_copy_forward src dst hne w
  · have hs : (catalogCopyF (x := x) src dst w (w src).length).workTapeSymbols src =
        none := by
      simp [catalogCopyF, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols, hne]
    change ((copyTM k src dst).tr .sweep _ _).apply _ = _
    simp only [copyTM, hs]
    apply Cfg.ext <;> simp [Action.apply, catalogCopyF, catalogCopyR, catalogCfg, Cfg.ofWords]
    all_goals
      funext j
      split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg]
  · intro r hr
    have hs : (catalogCopyR (x := x) src dst w (r + 1)).workTapeSymbols src =
        some (w src)[r] := by
      simp [catalogCopyR, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols, hne,
        show ((r + 1 : ℕ) : ℤ) - 1 = (r : ℤ) by omega,
        List.getElem?_eq_getElem hr]
    change ((copyTM k src dst).tr .rewind _ _).apply _ = _
    simp only [copyTM, hs]
    apply Cfg.ext <;> simp [Action.apply, catalogCopyR, catalogCfg, Cfg.ofWords]
    all_goals
      funext j
      split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg] <;> omega
  · apply Cfg.ext <;>
      simp [MultiTapeTM.step, copyTM, catalogCopyR, catalogCfg, Cfg.ofWords,
        Cfg.workTapeSymbols, hne, Action.apply]
    all_goals
      funext j
      split_ifs <;> simp_all [SignType.cast]
  · apply Cfg.ext <;>
      simp [MultiTapeTM.step, copyTM, Cfg.ofWords, Action.apply]

/-- Transfer's exact phase invariant. The forward transitions are copy's;
on return, erasure is behind the head, leaving every cell still to read intact. -/
private lemma catalog_transfer_trace (src dst : Fin k) (hne : src ≠ dst)
    (w : Fin k → List Bool) (hdst : w dst = []) (t : ℕ) :
    (transferTM k src dst).runFrom (Cfg.ofWords (input := x) .sweep w) t =
      catalogTrace (catalogCopyF src dst w) (catalogTransferR src dst w)
        (Cfg.ofWords .done (Function.update (Function.update w src []) dst (w src)))
        (w src).length t := by
  have h0 : catalogCopyF (x := x) src dst w 0 = Cfg.ofWords .sweep w := by
    apply Cfg.ext <;> simp [catalogCopyF, catalogCfg, Cfg.ofWords]
    funext j
    by_cases hj : j = dst
    · subst j; simp [hdst]
    · simp [hj]
  rw [← h0]
  apply catalog_trace_run
  · intro r hr
    exact catalog_copy_forward src dst hne w r hr
  · have hs : (catalogCopyF (x := x) src dst w (w src).length).workTapeSymbols src =
        none := by
      simp [catalogCopyF, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols, hne]
    change ((transferTM k src dst).tr .sweep _ _).apply _ = _
    simp only [transferTM, hs]
    apply Cfg.ext <;>
      simp [Action.apply, catalogCopyF, catalogTransferR, catalogCfg, Cfg.ofWords]
    · funext j
      by_cases hd : j = dst <;> by_cases hs : j = src <;> simp [hd, hs]
    · funext j
      split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg]
  · intro r hr
    have hs : (catalogTransferR (x := x) src dst w (r + 1)).workTapeSymbols src =
        some (w src)[r] := by
      simp [catalogTransferR, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols, hne,
        show ((r + 1 : ℕ) : ℤ) - 1 = (r : ℤ) by omega,
        List.getElem?_take, List.getElem?_eq_getElem hr]
    change ((transferTM k src dst).tr .rewind _ _).apply _ = _
    simp only [transferTM, hs]
    apply Cfg.ext <;> simp [Action.apply, catalogTransferR, catalogCfg, Cfg.ofWords]
    · funext j
      by_cases hs : j = src
      · subst j
        simpa [hne, show ((r + 1 : ℕ) : ℤ) - 1 = (r : ℤ) by omega] using
          catalog_erase_take (w src) r hr
      · by_cases hd : j = dst
        · subst j; simp [hne, Ne.symm hne]
        · simp [hs, hd]
    · funext j
      by_cases hs : j = src <;> by_cases hd : j = dst <;>
        simp [hs, hd, hne, Ne.symm hne, SignType.cast] <;> omega
  · apply Cfg.ext <;>
      simp [MultiTapeTM.step, transferTM, catalogTransferR, catalogCfg, Cfg.ofWords,
        Cfg.workTapeSymbols, hne, Action.apply]
    all_goals
      funext j
      split_ifs <;> simp_all [SignType.cast]
  · apply Cfg.ext <;>
      simp [MultiTapeTM.step, transferTM, Cfg.ofWords, Action.apply]

/-- The first unequal or terminating cells occur after a common nonblank
prefix, and equality at those terminating cells is precisely word equality.
**Proof sketch.** Remove equal leading bits recursively; unequal bits or either
empty list stop immediately. This also covers aliased physical tape indices. -/
private lemma catalog_compare_stop (u v : List Bool) :
    ∃ d ≤ min u.length v.length,
      (∀ r < d, ∃ b, u[r]? = some b ∧ v[r]? = some b) ∧
      (¬∃ b, u[d]? = some b ∧ v[d]? = some b) ∧
      (u[d]? = v[d]? ↔ u = v) := by
  induction u generalizing v with
  | nil =>
    cases v with
    | nil => exact ⟨0, by simp, by simp, by simp, by simp⟩
    | cons b v => exact ⟨0, by simp, by simp, by simp, by simp⟩
  | cons a u ih =>
    cases v with
    | nil => exact ⟨0, by simp, by simp, by simp, by simp⟩
    | cons b v =>
      by_cases hab : a = b
      · subst b
        obtain ⟨d, hd, hp, hs, he⟩ := ih v
        refine ⟨d + 1, by simpa using hd, ?_, ?_, ?_⟩
        · intro r hr
          cases r with
          | zero => exact ⟨a, rfl, rfl⟩
          | succ r => simpa using hp r (by omega)
        · simpa using hs
        · simpa using he
      · refine ⟨0, by simp, by simp, ?_, ?_⟩
        · simpa [eq_comm] using hab
        · simp [hab]

/-- Comparison's forward configuration retains every word and advances the
selected physical heads once each, including when the two indices coincide. -/
private def catalogCompareF (fst snd : Fin k) (w : Fin k → List Bool) (r : ℕ) :
    Cfg k Bool FlagPhase x :=
  catalogCfg .run w (fun j => if j = fst ∨ j = snd then (r : ℤ) else 0)

/-- Comparison's return configuration carries the verdict without changing words. -/
private def catalogCompareR (fst snd : Fin k) (w : Fin k → List Bool)
    (v : Bool) (r : ℕ) : Cfg k Bool FlagPhase x :=
  catalogCfg (.rewind v) w
    (fun j => if j = fst ∨ j = snd then (r : ℤ) - 1 else 0)

/-- Comparison's exact configuration invariant, at a first differing or blank
position. **Proof sketch.** The common-prefix condition supplies every forward
read and every first-tape return read. The stopping condition determines the
turn and verdict. The heads then return from `d-1` through `-1` to zero. -/
private lemma catalog_compare_trace (fst snd : Fin k) (w : Fin k → List Bool)
    (d : ℕ) (hd : d ≤ min (w fst).length (w snd).length)
    (hp : ∀ r < d, ∃ b, (w fst)[r]? = some b ∧ (w snd)[r]? = some b)
    (hs : ¬∃ b, (w fst)[d]? = some b ∧ (w snd)[d]? = some b)
    (he : ((w fst)[d]? = (w snd)[d]?) ↔ w fst = w snd) (t : ℕ) :
    (compareTM k fst snd).runFrom (Cfg.ofWords (input := x) .run w) t =
      catalogTrace (catalogCompareF fst snd w)
        (catalogCompareR fst snd w (decide (w fst = w snd)))
        (Cfg.ofWords (.done (decide (w fst = w snd))) w) d t := by
  have h0 : catalogCompareF (x := x) fst snd w 0 = Cfg.ofWords .run w := by
    apply Cfg.ext <;> simp [catalogCompareF, catalogCfg, Cfg.ofWords]
  rw [← h0]
  apply catalog_trace_run
  · intro r hr
    obtain ⟨b, hf, hg⟩ := hp r hr
    have hsf : (catalogCompareF (x := x) fst snd w r).workTapeSymbols fst = some b := by
      simpa [catalogCompareF, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols] using hf
    have hsg : (catalogCompareF (x := x) fst snd w r).workTapeSymbols snd = some b := by
      simpa [catalogCompareF, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols] using hg
    change ((compareTM k fst snd).tr .run _ _).apply _ = _
    simp only [compareTM, hsf, hsg, ↓reduceIte]
    apply Cfg.ext <;> simp [Action.apply, catalogCompareF, catalogCfg, Cfg.ofWords]
    all_goals
      funext j
      split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg] <;> omega
  · have hread : (catalogCompareF (x := x) fst snd w d).workTapeSymbols =
        fun j => FinTM.bufferTape (w j) (if j = fst ∨ j = snd then (d : ℤ) else 0) := rfl
    have ht : (compareTM k fst snd).tr .run
        (catalogCompareF (x := x) fst snd w d).inputSymbol
        (catalogCompareF (x := x) fst snd w d).workTapeSymbols =
        ⟨0, (fun j => if j = fst ∨ j = snd then (none, SignType.neg) else (none, 0)),
          none, some (.rewind (decide (w fst = w snd)))⟩ := by
      simp only [compareTM, hread, if_pos (Or.inl rfl : fst = fst ∨ fst = snd),
        if_pos (Or.inr rfl : snd = fst ∨ snd = snd), FinTM.bufferTape_nat]
      cases hf : (w fst)[d]? with
      | none =>
        cases hg : (w snd)[d]? with
        | none =>
          have heq : w fst = w snd := he.mp (by rw [hf, hg])
          simp [hf, hg, heq]
        | some b =>
          have hneq : w fst ≠ w snd := by
            intro h
            have h' := he.mpr h
            simp only [hf, hg, reduceCtorEq] at h'
          simp [hf, hg, hneq]
      | some a =>
        cases hg : (w snd)[d]? with
        | none =>
          have hneq : w fst ≠ w snd := by
            intro h
            have h' := he.mpr h
            simp only [hf, hg, reduceCtorEq] at h'
          simp [hf, hg, hneq]
        | some b =>
          have hab : a ≠ b := by
            intro h
            subst b
            exact hs ⟨a, hf, hg⟩
          have hneq : w fst ≠ w snd := by
            intro h
            have h' := he.mpr h
            exact hab (by simpa only [hf, hg, Option.some.injEq] using h')
          simp [hf, hg, hab, hneq]
    change ((compareTM k fst snd).tr .run _ _).apply _ = _
    rw [ht]
    apply Cfg.ext <;> simp [Action.apply, catalogCompareF, catalogCompareR, catalogCfg, Cfg.ofWords]
    all_goals
      funext j
      split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg]
  · intro r hr
    obtain ⟨b, hf, _⟩ := hp r hr
    have hread : (catalogCompareR (x := x) fst snd w (decide (w fst = w snd))
        (r + 1)).workTapeSymbols fst = some b := by
      simpa [catalogCompareR, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols,
        show ((r + 1 : ℕ) : ℤ) - 1 = (r : ℤ) by omega] using hf
    change ((compareTM k fst snd).tr (.rewind _) _ _).apply _ = _
    simp only [compareTM, hread]
    apply Cfg.ext <;> simp [Action.apply, catalogCompareR, catalogCfg, Cfg.ofWords]
    all_goals
      funext j
      split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg] <;> omega
  · apply Cfg.ext <;>
      simp [MultiTapeTM.step, compareTM, catalogCompareR, catalogCfg, Cfg.ofWords,
        Cfg.workTapeSymbols, Action.apply]
    all_goals
      funext j
      split_ifs <;> simp_all [SignType.cast]
  · apply Cfg.ext <;>
      simp [MultiTapeTM.step, compareTM, Cfg.ofWords, Action.apply]

/-- A word consists of its leading true bits followed by either a first false
bit and its tail, or no remaining bits. -/
private lemma catalog_increment_split (w : List Bool) :
    ∃ p : ℕ, ∃ tail : Option (List Bool),
      w = List.replicate p true ++ tail.elim [] (false :: ·) := by
  induction w with
  | nil => exact ⟨0, none, rfl⟩
  | cons b w ih =>
    cases b with
    | false => exact ⟨0, some w, rfl⟩
    | true =>
      obtain ⟨p, tail, hw⟩ := ih
      exact ⟨p + 1, tail, by simp [List.replicate_succ, hw]⟩

/-- Fixed-width increment flips the leading true prefix and the first false;
an absent first false gives overflow. -/
private lemma catalog_increment_value (p : ℕ) (tail : Option (List Bool)) :
    incFixed (List.replicate p true ++ tail.elim [] (false :: ·)) =
      tail.map (fun v => List.replicate p false ++ true :: v) := by
  induction p with
  | zero => cases tail <;> rfl
  | succ p ih =>
    simp only [List.replicate_succ, List.cons_append, incFixed, ih]
    cases tail <;> rfl

/-- Changing the cell immediately after a prefix changes exactly that bit.
**Proof sketch.** At the selected cell use list indexing at the prefix length;
elsewhere, the suffix and prefix lookups are unchanged. -/
private lemma catalog_write_middle (pre rest : List Bool) (a b : Bool) :
    Function.update (FinTM.bufferTape (pre ++ a :: rest)) (pre.length : ℤ) (some b) =
      FinTM.bufferTape (pre ++ b :: rest) := by
  funext z
  by_cases hz : z = (pre.length : ℤ)
  · subst z
    simp [FinTM.bufferTape]
  · rw [Function.update_of_ne hz]
    by_cases h0 : 0 ≤ z
    · simp only [FinTM.bufferTape, if_pos h0, List.getElem?_append]
      by_cases hlt : z.toNat < pre.length
      · simp [hlt]
      · have he : z.toNat - pre.length = (z.toNat - pre.length - 1) + 1 := by omega
        simp only [if_neg hlt]
        rw [he]
        rfl
    · simp [FinTM.bufferTape, h0]

/-- Increment's carry configuration: the first `r` bits have been reset, the
remaining true prefix and stopping suffix are intact, and the head is at `r`. -/
private def catalogIncF (i : Fin k) (w : Fin k → List Bool) (p : ℕ)
    (tail : Option (List Bool)) (r : ℕ) : Cfg k Bool FlagPhase x :=
  catalogCfg .run (Function.update w i
    (List.replicate r false ++ List.replicate (p - r) true ++ tail.elim [] (false :: ·)))
    (fun j => if j = i then (r : ℤ) else 0)

/-- Increment's return configuration holds the complete updated or wrapped
word and carries the success bit, with the head immediately before cell `r`. -/
private def catalogIncR (i : Fin k) (w : Fin k → List Bool) (p : ℕ)
    (tail : Option (List Bool)) (r : ℕ) : Cfg k Bool FlagPhase x :=
  catalogCfg (.rewind tail.isSome)
    (Function.update w i (List.replicate p false ++ tail.elim [] (true :: ·)))
    (fun j => if j = i then (r : ℤ) - 1 else 0)

/-- Increment's exact phase invariant. **Proof sketch.** Each carry step resets
one true bit; the first false is changed on the left-turn itself, so cell `p+1`
is not visited. With no false, the right blank turns without writing. Both cases
return over the reset prefix and enter the live exit after exactly `2p+2` steps. -/
private lemma catalog_increment_trace (i : Fin k) (w : Fin k → List Bool)
    (p : ℕ) (tail : Option (List Bool))
    (hw : w i = List.replicate p true ++ tail.elim [] (false :: ·)) (t : ℕ) :
    (incrementTM k i).runFrom (Cfg.ofWords (input := x) .run w) t =
      catalogTrace (catalogIncF i w p tail) (catalogIncR i w p tail)
        (Cfg.ofWords (.done tail.isSome)
          (Function.update w i (List.replicate p false ++ tail.elim [] (true :: ·)))) p t := by
  have h0 : catalogIncF (x := x) i w p tail 0 = Cfg.ofWords .run w := by
    apply Cfg.ext <;> simp [catalogIncF, catalogCfg, Cfg.ofWords, ← hw]
  rw [← h0]
  apply catalog_trace_run
  · intro r hr
    have hpr : p - r = (p - (r + 1)) + 1 := by omega
    have hs : (catalogIncF (x := x) i w p tail r).workTapeSymbols i = some true := by
      simp [catalogIncF, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols,
        hpr, List.replicate_succ, List.append_assoc]
    change ((incrementTM k i).tr .run _ _).apply _ = _
    simp only [incrementTM, hs]
    apply Cfg.ext <;> simp [Action.apply, catalogIncF, catalogCfg, Cfg.ofWords]
    · funext j
      by_cases hj : j = i
      · subst j
        have hh := catalog_write_middle (List.replicate r false)
          (List.replicate (p - (r + 1)) true ++ tail.elim [] (false :: ·)) true false
        simp only [ite_true, Function.update_self]
        rw [hpr, List.replicate_succ, List.cons_append]
        simpa only [List.length_replicate, List.replicate_succ',
          List.append_assoc, List.singleton_append] using hh
      · simp [hj]
    · funext j
      split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg] <;> omega
  · cases tail with
    | none =>
      have hs : (catalogIncF (x := x) i w p none p).workTapeSymbols i = none := by
        simp [catalogIncF, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols]
      change ((incrementTM k i).tr .run _ _).apply _ = _
      simp only [incrementTM, hs]
      apply Cfg.ext <;> simp [Action.apply, catalogIncF, catalogIncR, catalogCfg, Cfg.ofWords]
      all_goals
        funext j
        split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg]
    | some v =>
      have hs : (catalogIncF (x := x) i w p (some v) p).workTapeSymbols i = some false := by
        simp [catalogIncF, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols]
      change ((incrementTM k i).tr .run _ _).apply _ = _
      simp only [incrementTM, hs]
      apply Cfg.ext <;> simp [Action.apply, catalogIncF, catalogIncR, catalogCfg, Cfg.ofWords]
      · funext j
        by_cases hj : j = i
        · subst j
          simpa using catalog_write_middle (List.replicate p false) v false true
        · simp [hj]
      · funext j
        split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg]
  · intro r hr
    have hs : (catalogIncR (x := x) i w p tail (r + 1)).workTapeSymbols i = some false := by
      simp [catalogIncR, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols,
        show ((r + 1 : ℕ) : ℤ) - 1 = (r : ℤ) by omega,
        List.getElem?_append, hr]
    change ((incrementTM k i).tr (.rewind _) _ _).apply _ = _
    simp only [incrementTM, hs]
    apply Cfg.ext <;> simp [Action.apply, catalogIncR, catalogCfg, Cfg.ofWords]
    all_goals
      funext j
      split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg] <;> omega
  · apply Cfg.ext <;>
      simp [MultiTapeTM.step, incrementTM, catalogIncR, catalogCfg, Cfg.ofWords,
        Cfg.workTapeSymbols, Action.apply]
    all_goals
      funext j
      split_ifs <;> simp_all [SignType.cast]
  · apply Cfg.ext <;>
      simp [MultiTapeTM.step, incrementTM, Cfg.ofWords, Action.apply]

/-- **Transfer, the run contract** (spec, fill pending — design §12 R3;
[Bon26]). From the seam with word `w src` on the source and a blank
destination, the routine reaches — within `3|w src| + 3` steps and
without visiting the exit anchor earlier — the seam whose source is blank
and whose destination holds the word, everything else untouched.

**Proof sketch.** Two phase invariants. *Sweep*, time `p ≤ |w|`: heads of
`src`/`dst` at `p`, `dst` holding the copied prefix, `src` intact; the
turn at the right blank enters *rewind*. *Rewind*, positions `|w| - 1`
down to `-1`: `src` erased above the head, `dst` complete; the left-blank
overshoot steps right into `done` at the origin at time `2|w| + 2`
(` ≤ 3|w| + 3`). The cut holds because `done` only appears after the
overshoot. -/
theorem transferTM_run (k : ℕ) (src dst : Fin k) (hne : src ≠ dst)
    (w : Fin k → List Bool) (hdst : w dst = []) :
    ∃ T ≤ 3 * (w src).length + 3,
      (∀ t < T, ((transferTM k src dst).runFrom
        (Cfg.ofWords (input := x) SweepPhase.sweep w) t).state
          ≠ some SweepPhase.done) ∧
      (transferTM k src dst).runFrom
          (Cfg.ofWords (input := x) SweepPhase.sweep w) T =
        Cfg.ofWords SweepPhase.done
          (Function.update (Function.update w src []) dst (w src)) := by
  refine ⟨2 * (w src).length + 2, by omega, ?_, ?_⟩
  · intro t ht
    rw [catalog_transfer_trace src dst hne w hdst]
    simp only [catalogTrace]
    split_ifs <;> simp_all [catalogCopyF, catalogTransferR, catalogCfg, Cfg.ofWords]
    omega
  · rw [catalog_transfer_trace src dst hne w hdst]
    simp [catalogTrace, show ¬2 * (w src).length + 2 ≤ (w src).length by omega]

/-- **Transfer, per-tape space** (spec, fill pending — design §12 R3).
The two touched tapes visit at most the word interval plus the two
boundary blanks — `|w src| + 2` cells, from the `-1` overshoot to the
right blank at `|w src|` — and every other tape never leaves its origin.

**Proof sketch.** Head-movement count of the phases: both touched heads
walk `0 → |w src| → -1 → 0` in unit steps, so their trajectories lie in
`[-1, |w src|]` (`Finset.Icc`, cardinality `|w src| + 2`); all other
action components are `(none, 0)`, so those trajectories are constant and
the visited set is the origin singleton. -/
theorem transferTM_spaceUsedByTape (k : ℕ) (src dst : Fin k)
    (hne : src ≠ dst) (w : Fin k → List Bool) (hdst : w dst = []) (t : ℕ) :
    (transferTM k src dst).spaceUsedByTape
        (Cfg.ofWords (input := x) SweepPhase.sweep w) t src
      ≤ (w src).length + 2 ∧
    (transferTM k src dst).spaceUsedByTape
        (Cfg.ofWords (input := x) SweepPhase.sweep w) t dst
      ≤ (w src).length + 2 ∧
    ∀ j : Fin k, j ≠ src → j ≠ dst →
      (transferTM k src dst).spaceUsedByTape
          (Cfg.ofWords (input := x) SweepPhase.sweep w) t j = 1 := by
  have hb (j : Fin k) : (transferTM k src dst).spaceUsedByTape
      (Cfg.ofWords (input := x) .sweep w) t j ≤ (w src).length + 2 := by
    apply catalog_space_bound
    intro u
    rw [catalog_transfer_trace src dst hne w hdst]
    simp only [catalogTrace]
    split_ifs <;> simp only [catalogCopyF, catalogTransferR, catalogCfg, Cfg.ofWords] <;>
      (try split_ifs) <;> omega
  refine ⟨hb src, hb dst, ?_⟩
  intro j hs hd
  apply catalog_space_one
  intro u
  rw [catalog_transfer_trace src dst hne w hdst]
  simp only [catalogTrace]
  split_ifs <;> simp [catalogCopyF, catalogTransferR, catalogCfg, Cfg.ofWords, hs, hd]

/-- **Copy, the run contract** (spec, fill pending — design §12 R3;
[Bon26]; the A3 `3|w| + 3` row). From the seam with word `w src` on the
source and a blank destination, the routine reaches — within
`3|w src| + 3` steps and without visiting the exit anchor earlier — the
seam where both tapes hold the word.

**Proof sketch.** As `transferTM_run` without the erasure clause: sweep
copies the prefix in lockstep, rewind returns both heads guided by the
intact source, the overshoot enters `done` at time `2|w| + 2`. -/
theorem copyTM_run (k : ℕ) (src dst : Fin k) (hne : src ≠ dst)
    (w : Fin k → List Bool) (hdst : w dst = []) :
    ∃ T ≤ 3 * (w src).length + 3,
      (∀ t < T, ((copyTM k src dst).runFrom
        (Cfg.ofWords (input := x) SweepPhase.sweep w) t).state
          ≠ some SweepPhase.done) ∧
      (copyTM k src dst).runFrom
          (Cfg.ofWords (input := x) SweepPhase.sweep w) T =
        Cfg.ofWords SweepPhase.done (Function.update w dst (w src)) := by
  refine ⟨2 * (w src).length + 2, by omega, ?_, ?_⟩
  · intro t ht
    rw [catalog_copy_trace src dst hne w hdst]
    simp only [catalogTrace]
    split_ifs <;> simp_all [catalogCopyF, catalogCopyR, catalogCfg, Cfg.ofWords]
    omega
  · rw [catalog_copy_trace src dst hne w hdst]
    simp [catalogTrace, show ¬2 * (w src).length + 2 ≤ (w src).length by omega]

/-- **Copy, per-tape space** (spec, fill pending — design §12 R3). As the
transfer routine: the two touched tapes visit at most `|w src| + 2` cells
(the word interval plus both boundary blanks), every other tape exactly
its origin singleton.

**Proof sketch.** Identical head-movement count to
`transferTM_spaceUsedByTape`: both touched heads walk
`0 → |w src| → -1 → 0`; all other tapes receive `(none, 0)` throughout. -/
theorem copyTM_spaceUsedByTape (k : ℕ) (src dst : Fin k) (hne : src ≠ dst)
    (w : Fin k → List Bool) (hdst : w dst = []) (t : ℕ) :
    (copyTM k src dst).spaceUsedByTape
        (Cfg.ofWords (input := x) SweepPhase.sweep w) t src
      ≤ (w src).length + 2 ∧
    (copyTM k src dst).spaceUsedByTape
        (Cfg.ofWords (input := x) SweepPhase.sweep w) t dst
      ≤ (w src).length + 2 ∧
    ∀ j : Fin k, j ≠ src → j ≠ dst →
      (copyTM k src dst).spaceUsedByTape
          (Cfg.ofWords (input := x) SweepPhase.sweep w) t j = 1 := by
  have hb (j : Fin k) : (copyTM k src dst).spaceUsedByTape
      (Cfg.ofWords (input := x) .sweep w) t j ≤ (w src).length + 2 := by
    apply catalog_space_bound
    intro u
    rw [catalog_copy_trace src dst hne w hdst]
    simp only [catalogTrace]
    split_ifs <;> simp only [catalogCopyF, catalogCopyR, catalogCfg, Cfg.ofWords] <;>
      (try split_ifs) <;> omega
  refine ⟨hb src, hb dst, ?_⟩
  intro j hs hd
  apply catalog_space_one
  intro u
  rw [catalog_copy_trace src dst hne w hdst]
  simp only [catalogTrace]
  split_ifs <;> simp [catalogCopyF, catalogCopyR, catalogCfg, Cfg.ofWords, hs, hd]

/-- **Clear, the run contract** (spec, fill pending — design §12 R3;
[Bon26]; the A3 `2|w| + 2` row, P12's engine). From the seam with word
`w i` on tape `i`, the routine reaches — within `2|w i| + 2` steps and
without visiting the exit anchor earlier — the seam with tape `i` blank,
everything else untouched.

**Proof sketch.** Sweep walks right over the intact word to the right
blank (`|w i| + 1` steps including the turn), rewind erases on the way
back and overshoots to `-1`, the final step enters `done` at the origin:
exactly `2|w i| + 2` steps, matching the stated budget on the nose. -/
theorem clearTM_run (k : ℕ) (i : Fin k) (w : Fin k → List Bool) :
    ∃ T ≤ 2 * (w i).length + 2,
      (∀ t < T, ((clearTM k i).runFrom
        (Cfg.ofWords (input := x) SweepPhase.sweep w) t).state
          ≠ some SweepPhase.done) ∧
      (clearTM k i).runFrom
          (Cfg.ofWords (input := x) SweepPhase.sweep w) T =
        Cfg.ofWords SweepPhase.done (Function.update w i []) := by
  refine ⟨2 * (w i).length + 2, le_rfl, ?_, ?_⟩
  · intro t ht
    rw [catalog_clear_trace]
    simp only [catalogTrace]
    split_ifs <;> simp_all [catalogClearF, catalogClearR, catalogCfg, Cfg.ofWords]
    omega
  · rw [catalog_clear_trace]
    simp [catalogTrace, show ¬2 * (w i).length + 2 ≤ (w i).length by omega]

/-- **Clear, per-tape space** (spec, fill pending — design §12 R3). Tape
`i` visits at most `|w i| + 2` cells (the word interval plus both
boundary blanks); every other tape exactly its origin singleton.

**Proof sketch.** The single touched head walks `0 → |w i| → -1 → 0` in
unit steps, so its trajectory lies in `[-1, |w i|]`; every other tape's
action is `(none, 0)` in every phase. -/
theorem clearTM_spaceUsedByTape (k : ℕ) (i : Fin k)
    (w : Fin k → List Bool) (t : ℕ) :
    (clearTM k i).spaceUsedByTape
        (Cfg.ofWords (input := x) SweepPhase.sweep w) t i
      ≤ (w i).length + 2 ∧
    ∀ j : Fin k, j ≠ i →
      (clearTM k i).spaceUsedByTape
          (Cfg.ofWords (input := x) SweepPhase.sweep w) t j = 1 := by
  constructor
  · apply catalog_space_bound
    intro u
    rw [catalog_clear_trace]
    simp only [catalogTrace]
    split_ifs <;> simp [catalogClearF, catalogClearR, catalogCfg, Cfg.ofWords] <;> omega
  · intro j hj
    apply catalog_space_one
    intro u
    rw [catalog_clear_trace]
    simp only [catalogTrace]
    split_ifs <;> simp [catalogClearF, catalogClearR, catalogCfg, Cfg.ofWords, hj]

/-- **Compare, the run contract** (spec, fill pending — design §12 R3;
[Bon26]). From the seam, the routine reaches — within
`2·min(|w fst|, |w snd|) + 2` steps and without visiting either exit
anchor earlier — the seam carrying the equality verdict
`decide (w fst = w snd)` in its anchor, with every tape (the compared two
included) byte-identical to the entry.

**Proof sketch.** The lockstep scan maintains "prefixes below the heads
agree"; it ends at the first disagreeing position or the double blank,
at depth at most `min + 1`. List equality is exactly "no disagreement
and simultaneous blank". The return pass is guided by `fst`'s intact
content — sound because the scan depth never exceeds `|w fst| + 1`, so
the first blank met moving left is the `-1` overshoot. Both passes have
the same length, giving `2·min + 2` worst case. -/
theorem compareTM_run (k : ℕ) (fst snd : Fin k) (w : Fin k → List Bool) :
    ∃ T ≤ 2 * min (w fst).length (w snd).length + 2,
      (∀ t < T, ∀ v : Bool, ((compareTM k fst snd).runFrom
        (Cfg.ofWords (input := x) FlagPhase.run w) t).state
          ≠ some (FlagPhase.done v)) ∧
      (compareTM k fst snd).runFrom
          (Cfg.ofWords (input := x) FlagPhase.run w) T =
        Cfg.ofWords (FlagPhase.done (decide (w fst = w snd))) w := by
  obtain ⟨d, hd, hp, hs, he⟩ := catalog_compare_stop (w fst) (w snd)
  refine ⟨2 * d + 2, by omega, ?_, ?_⟩
  · intro t ht v
    rw [catalog_compare_trace fst snd w d hd hp hs he]
    simp only [catalogTrace]
    split_ifs <;> simp_all [catalogCompareF, catalogCompareR, catalogCfg, Cfg.ofWords]
    omega
  · rw [catalog_compare_trace fst snd w d hd hp hs he]
    simp [catalogTrace, show ¬2 * d + 2 ≤ d by omega]

/-- **Compare, per-tape space** (spec, fill pending — design §12 R3). The
two compared tapes visit at most `min(|w fst|, |w snd|) + 2` cells (the
scanned interval plus both boundary cells); every other tape exactly its
origin singleton.

**Proof sketch.** Exact position counting, uniformly over mismatches,
equal words, and unequal lengths (round-1 finding 6 — the earlier
`[-1, min + 1]` interval argument did not cover equal inputs): with `d`
the first differing position or the first position where a word ends
(`d ≤ min`), the scan turns at `d`, the return pass overshoots to `-1`,
and both touched trajectories are exactly the integers of `[-1, d]` —
`d + 2 ≤ min + 2` visited cells in every case, aliased indices included;
untouched tapes receive `(none, 0)` throughout. -/
theorem compareTM_spaceUsedByTape (k : ℕ) (fst snd : Fin k)
    (w : Fin k → List Bool) (t : ℕ) :
    (compareTM k fst snd).spaceUsedByTape
        (Cfg.ofWords (input := x) FlagPhase.run w) t fst
      ≤ min (w fst).length (w snd).length + 2 ∧
    (compareTM k fst snd).spaceUsedByTape
        (Cfg.ofWords (input := x) FlagPhase.run w) t snd
      ≤ min (w fst).length (w snd).length + 2 ∧
    ∀ j : Fin k, j ≠ fst → j ≠ snd →
      (compareTM k fst snd).spaceUsedByTape
          (Cfg.ofWords (input := x) FlagPhase.run w) t j = 1 := by
  obtain ⟨d, hd, hp, hs, he⟩ := catalog_compare_stop (w fst) (w snd)
  have hb (j : Fin k) : (compareTM k fst snd).spaceUsedByTape
      (Cfg.ofWords (input := x) .run w) t j ≤ d + 2 := by
    apply catalog_space_bound
    intro u
    rw [catalog_compare_trace fst snd w d hd hp hs he]
    simp only [catalogTrace]
    split_ifs <;> simp only [catalogCompareF, catalogCompareR, catalogCfg, Cfg.ofWords] <;>
      (try split_ifs) <;> omega
  refine ⟨(hb fst).trans (by omega), (hb snd).trans (by omega), ?_⟩
  intro j hf hg
  apply catalog_space_one
  intro u
  rw [catalog_compare_trace fst snd w d hd hp hs he]
  simp only [catalogTrace]
  split_ifs <;> simp [catalogCompareF, catalogCompareR, catalogCfg, Cfg.ofWords, hf, hg]

/-- **Increment, the success contract** (spec, fill pending — design §12
R3). If the word on tape `i` has a successor at its width
(`Turing.incFixed (w i) = some v`), the routine reaches — within
`2|w i| + 2` steps and without visiting either exit anchor earlier — the
seam carrying the success verdict and the incremented word `v` in place.

**Proof sketch.** The carry pass flips the maximal `true`-prefix to
`false` and the first `false` to `true`, which is exactly
`Turing.incFixed`'s recursion. With `p` the first `false` position, the
machine takes `p` carry steps, one left-turn/write step, `p` rewind
steps, and one right-entry step — **exactly `2p + 2 ≤ 2|w i|` steps**,
visited interval `[-1, p]`; it never visits `p + 1` on success, and
`[false]` returns in two steps (round-1 finding 7 corrected the earlier
mixed count). The looser public `2|w i| + 2` is deliberate slack. -/
theorem incrementTM_run_succ (k : ℕ) (i : Fin k) (w : Fin k → List Bool)
    (v : List Bool) (hv : incFixed (w i) = some v) :
    ∃ T ≤ 2 * (w i).length + 2,
      (∀ t < T, ∀ b : Bool, ((incrementTM k i).runFrom
        (Cfg.ofWords (input := x) FlagPhase.run w) t).state
          ≠ some (FlagPhase.done b)) ∧
      (incrementTM k i).runFrom
          (Cfg.ofWords (input := x) FlagPhase.run w) T =
        Cfg.ofWords (FlagPhase.done true) (Function.update w i v) := by
  obtain ⟨p, tail, hw⟩ := catalog_increment_split (w i)
  rw [hw, catalog_increment_value] at hv
  cases tail with
  | none => simp at hv
  | some tail =>
    have hv' : v = List.replicate p false ++ true :: tail := by simpa using hv.symm
    have hp : p < (w i).length := by simp [hw]
    refine ⟨2 * p + 2, by omega, ?_, ?_⟩
    · intro t ht b
      rw [catalog_increment_trace i w p (some tail) hw]
      simp only [catalogTrace]
      split_ifs <;> simp_all [catalogIncF, catalogIncR, catalogCfg, Cfg.ofWords]
      omega
    · rw [catalog_increment_trace i w p (some tail) hw]
      simp [catalogTrace, show ¬2 * p + 2 ≤ p by omega, hv']

/-- **Increment, the overflow contract** (spec, fill pending — design §12
R3). If the word on tape `i` is all `true` (`Turing.incFixed (w i) =
none`), the routine reaches — within `2|w i| + 2` steps and without
visiting either exit anchor earlier — the seam carrying the overflow
verdict and the wrapped all-`false` word, the enumerator's counter
convention.

**Proof sketch.** The carry pass flips every cell and falls off the width
at the right blank (`|w i| + 1` steps), the return pass over the written
`false` word overshoots to `-1` and enters `done false` at the origin:
exactly `2|w i| + 2` steps. -/
theorem incrementTM_run_overflow (k : ℕ) (i : Fin k)
    (w : Fin k → List Bool) (hv : incFixed (w i) = none) :
    ∃ T ≤ 2 * (w i).length + 2,
      (∀ t < T, ∀ b : Bool, ((incrementTM k i).runFrom
        (Cfg.ofWords (input := x) FlagPhase.run w) t).state
          ≠ some (FlagPhase.done b)) ∧
      (incrementTM k i).runFrom
          (Cfg.ofWords (input := x) FlagPhase.run w) T =
        Cfg.ofWords (FlagPhase.done false)
          (Function.update w i (List.replicate (w i).length false)) := by
  obtain ⟨p, tail, hw⟩ := catalog_increment_split (w i)
  rw [hw, catalog_increment_value] at hv
  cases tail with
  | some tail => simp at hv
  | none =>
    have hp : (w i).length = p := by simp [hw]
    refine ⟨2 * p + 2, by omega, ?_, ?_⟩
    · intro t ht b
      rw [catalog_increment_trace i w p none hw]
      simp only [catalogTrace]
      split_ifs <;> simp_all [catalogIncF, catalogIncR, catalogCfg, Cfg.ofWords]
      omega
    · rw [catalog_increment_trace i w p none hw]
      simp [catalogTrace, show ¬2 * p + 2 ≤ p by omega, hp]

/-- **Increment, per-tape space** (spec, fill pending — design §12 R3).
Tape `i` visits at most `|w i| + 2` cells; every other tape exactly its
origin singleton.

**Proof sketch.** The carry head walks right to at most the right blank
at `|w i|`, back to the `-1` overshoot, and home: trajectory inside
`[-1, |w i|]`; other tapes receive `(none, 0)` in every phase. -/
theorem incrementTM_spaceUsedByTape (k : ℕ) (i : Fin k)
    (w : Fin k → List Bool) (t : ℕ) :
    (incrementTM k i).spaceUsedByTape
        (Cfg.ofWords (input := x) FlagPhase.run w) t i
      ≤ (w i).length + 2 ∧
    ∀ j : Fin k, j ≠ i →
      (incrementTM k i).spaceUsedByTape
          (Cfg.ofWords (input := x) FlagPhase.run w) t j = 1 := by
  obtain ⟨p, tail, hw⟩ := catalog_increment_split (w i)
  have hp : p ≤ (w i).length := by simp [hw]
  constructor
  · have hb : (incrementTM k i).spaceUsedByTape
        (Cfg.ofWords (input := x) .run w) t i ≤ p + 2 := by
      apply catalog_space_bound
      intro u
      rw [catalog_increment_trace i w p tail hw]
      simp only [catalogTrace]
      split_ifs <;> simp [catalogIncF, catalogIncR, catalogCfg, Cfg.ofWords] <;> omega
    omega
  · intro j hj
    apply catalog_space_one
    intro u
    rw [catalog_increment_trace i w p tail hw]
    simp only [catalogTrace]
    split_ifs <;> simp [catalogIncF, catalogIncR, catalogCfg, Cfg.ofWords, hj]

/-- **W1 space row** (spec, fill pending — design §12 R3, decision 12.3).
Under the hypotheses of `Turing.capture_run`, the host's source-bank
tapes visit exactly the source's cells — per-tape, on the nose — and the
capture tape's space usage is bounded by the output recorded in the
window plus one.

**Proof sketch.** `Turing.capture_run` makes the host trajectory on tape
`i.castSucc` pointwise equal to the source's on tape `i`, so the visited
images and their cardinalities agree. The capture head sits at
`|pre ++ output-so-far|`, which is nondecreasing (one cell per recorded
emission, `Turing.MultiTapeTM.output_prefix`), so its visited set is an
integer interval of length the output growth plus one. -/
theorem capture_visitedByTapeHead {k : ℕ} {S H : Type*} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (host : MultiTapeTM (k + 1) Bool H)
    (emb : S → H) (ret : H)
    (hagree : ∀ (s : S) (inp : Option Bool) (w : Fin (k + 1) → Option Bool),
      host.tr (emb s) inp w =
        captureAction emb ret (tm.tr s inp fun i => w i.castSucc))
    (pre out₀ : List Bool) (c₀ : Cfg k Bool S x) (t : ℕ)
    (hlive : ∀ t' < t, ¬(tm.runFrom c₀ t').Halted) :
    (∀ i : Fin k,
      host.visitedByTapeHead (captureCfg emb ret pre out₀ c₀) t i.castSucc
        = tm.visitedByTapeHead c₀ t i ∧
      host.spaceUsedByTape (captureCfg emb ret pre out₀ c₀) t i.castSucc
        = tm.spaceUsedByTape c₀ t i) ∧
    host.spaceUsedByTape (captureCfg emb ret pre out₀ c₀) t (Fin.last k)
      ≤ (tm.runFrom c₀ t).output.length - c₀.output.length + 1 := by
  have hr (u : ℕ) (hu : u ≤ t) :=
    capture_run tm host emb ret hagree pre out₀ c₀ u
      (fun v hv => hlive v (by omega))
  constructor
  · intro i
    have he : host.visitedByTapeHead (captureCfg emb ret pre out₀ c₀) t i.castSucc =
        tm.visitedByTapeHead c₀ t i := by
      unfold MultiTapeTM.visitedByTapeHead
      apply Finset.image_congr
      intro u hu
      dsimp only
      rw [hr u (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hu))]
      simp [captureCfg, i.isLt]
    exact ⟨he, congrArg Finset.card he⟩
  · have hmono {u v : ℕ} (huv : u ≤ v) :
        (tm.runFrom c₀ u).output.length ≤ (tm.runFrom c₀ v).output.length :=
      (tm.output_prefix c₀ huv).length_le
    have hbound : c₀.output.length ≤ (tm.runFrom c₀ t).output.length :=
      hmono (Nat.zero_le t)
    have hsub : host.visitedByTapeHead (captureCfg emb ret pre out₀ c₀) t (Fin.last k) ⊆
        Finset.Icc ((pre.length + c₀.output.length : ℕ) : ℤ)
          ((pre.length + (tm.runFrom c₀ t).output.length : ℕ) : ℤ) := by
      intro z hz
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
      have hut : u ≤ t := by have := Finset.mem_range.mp hu; omega
      rw [hr u hut]
      simp only [captureCfg, Fin.val_last, lt_self_iff_false, ↓reduceDIte,
        List.length_append, Finset.mem_Icc]
      have hlo := hmono (Nat.zero_le u)
      have hhi := hmono hut
      simp only [MultiTapeTM.runFrom_zero] at hlo
      constructor <;> omega
    exact (Finset.card_le_card hsub).trans (by
      rw [Int.card_Icc]
      omega)

/-! ### Framed contracts (design §12.6)

The R3 rows above start from `Cfg.ofWords`: every head at the origin and every
tape a globally buffered word. The routines themselves are local, since each
step reads only the scanned cells of the touched tapes. The contracts below
state them for an **arbitrary** configuration whose touched tapes carry a
*delimited* word at the current head: the word's cells, plus a blank at
relative positions `-1` and `|w|`. Every other cell, every other tape, the
native input position and the output are arbitrary and are preserved. This is
the form a consumer needs when the routine runs at displaced heads inside a
larger tape (the zone carrier, `Build/Zone.lean`; escalation of ZF-A2,
`audits/zone-agent-reports/f1-A2-REPORT.md`).

Times are exact. For increment the time is carry-sensitive, so a counter's
total cost can be summed geometrically.
-/

/-- **Transfer, framed** (design §12.6; spec, fill pending). From any
configuration in the sweep phase whose source tape carries the word `w`
delimited by blanks at relative positions `-1` and `|w|`, the transfer
reaches the `done` anchor at exactly `2|w| + 2` and not earlier. At that
point:

- the source interval `[pos, pos + |w|)` is blank;
- the destination interval holds `w`;
- every other cell, the head positions, the native input position and the
  output are unchanged.

The destination's old contents are arbitrary, because the routine never
branches on them. Up to the exit, both touched heads stay within one cell of
their word interval, and every other head is fixed. With the origin heads and
globally buffered words of `Cfg.ofWords` this specializes to
`Turing.transferTM_run`.

**Proof sketch.** Generalize the canonical forward/rewind trace over the
fixed outer frame and the two start coordinates. The forward pass takes `|w|`
steps copying source to destination in lockstep without touching the source.
The source's right delimiter turns both heads in one step. The rewind takes
`|w|` steps erasing exactly the source interior. The left delimiter supplies
the final entry step. -/
theorem transferTM_run_ofCfg {k : ℕ} {x : List Bool} (src dst : Fin k)
    (hne : src ≠ dst) (w : List Bool) (d : Cfg k Bool SweepPhase x)
    (hstate : d.state = some SweepPhase.sweep)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      d.workTapes src (d.workTapePos src + p) = FinTM.bufferTape w p) :
    (transferTM k src dst).runFrom d (2 * w.length + 2) =
        { d with
          state := some SweepPhase.done
          workTapes := fun j q =>
            if j = src ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ)
              then none
            else if j = dst ∧ d.workTapePos j ≤ q ∧
                q < d.workTapePos j + (w.length : ℤ)
              then FinTM.bufferTape w (q - d.workTapePos j)
            else d.workTapes j q } ∧
      (∀ t < 2 * w.length + 2,
        ((transferTM k src dst).runFrom d t).state ≠ some SweepPhase.done) ∧
      (∀ (j : Fin k) (t : ℕ), t ≤ 2 * w.length + 2 →
        if j = src ∨ j = dst then
          ((transferTM k src dst).runFrom d t).workTapePos j ∈
            Finset.Icc (d.workTapePos j - 1) (d.workTapePos j + (w.length : ℤ))
        else ((transferTM k src dst).runFrom d t).workTapePos j = d.workTapePos j) := by
  sorry

/-- **Copy, framed** (design §12.6; spec, fill pending). As
`Turing.transferTM_run_ofCfg`, except that the source is left intact: at
exactly `2|w| + 2` the destination interval holds `w` and every other cell is
unchanged. This specializes to `Turing.copyTM_run`.

**Proof sketch.** The transfer's trace without the erasure. The rewind is
guided by the intact source word, whose left delimiter at `-1` is the first
blank met moving left. -/
theorem copyTM_run_ofCfg {k : ℕ} {x : List Bool} (src dst : Fin k)
    (hne : src ≠ dst) (w : List Bool) (d : Cfg k Bool SweepPhase x)
    (hstate : d.state = some SweepPhase.sweep)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      d.workTapes src (d.workTapePos src + p) = FinTM.bufferTape w p) :
    (copyTM k src dst).runFrom d (2 * w.length + 2) =
        { d with
          state := some SweepPhase.done
          workTapes := fun j q =>
            if j = dst ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ)
              then FinTM.bufferTape w (q - d.workTapePos j)
            else d.workTapes j q } ∧
      (∀ t < 2 * w.length + 2,
        ((copyTM k src dst).runFrom d t).state ≠ some SweepPhase.done) ∧
      (∀ (j : Fin k) (t : ℕ), t ≤ 2 * w.length + 2 →
        if j = src ∨ j = dst then
          ((copyTM k src dst).runFrom d t).workTapePos j ∈
            Finset.Icc (d.workTapePos j - 1) (d.workTapePos j + (w.length : ℤ))
        else ((copyTM k src dst).runFrom d t).workTapePos j = d.workTapePos j) := by
  sorry

/-- **Clear, framed** (design §12.6; spec, fill pending). From any
configuration in the sweep phase whose tape `i` carries the delimited word
`w`, the routine reaches `done` at exactly `2|w| + 2` and not earlier, with
the word interval blank and every other cell, head, the input position and the
output unchanged. Up to the exit the head stays within one cell of the
interval. This specializes to `Turing.clearTM_run`.

**Proof sketch.** The forward pass walks right over the intact word in `|w|`
steps, the right delimiter turns the head in one step, the rewind erases the
interior in `|w|` steps, and the left delimiter supplies the entry step. -/
theorem clearTM_run_ofCfg {k : ℕ} {x : List Bool} (i : Fin k) (w : List Bool)
    (d : Cfg k Bool SweepPhase x) (hstate : d.state = some SweepPhase.sweep)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      d.workTapes i (d.workTapePos i + p) = FinTM.bufferTape w p) :
    (clearTM k i).runFrom d (2 * w.length + 2) =
        { d with
          state := some SweepPhase.done
          workTapes := fun j q =>
            if j = i ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ)
              then none
            else d.workTapes j q } ∧
      (∀ t < 2 * w.length + 2,
        ((clearTM k i).runFrom d t).state ≠ some SweepPhase.done) ∧
      (∀ (j : Fin k) (t : ℕ), t ≤ 2 * w.length + 2 →
        if j = i then
          ((clearTM k i).runFrom d t).workTapePos j ∈
            Finset.Icc (d.workTapePos j - 1) (d.workTapePos j + (w.length : ℤ))
        else ((clearTM k i).runFrom d t).workTapePos j = d.workTapePos j) := by
  sorry

/-- **Increment, framed success with exact carry cost** (design §12.6; spec,
fill pending). Let the delimited word `w` on tape `i` have a successor at its
width, `incFixed w = some v`, and let `p = (w.takeWhile id).length` be its
number of leading `true` cells. Then the routine reaches the success anchor
at exactly `2p + 2` and not earlier, with the word interval holding `v` and
everything else unchanged. Up to the exit the head stays within
`[pos - 1, pos + p]`. This specializes to `Turing.incrementTM_run_succ`,
whose `2|w| + 2` is the slack form of this bound.

**Proof sketch.** The carry pass takes `p` steps flipping the `true` prefix,
then one step writes the first `false` as `true` and turns left. The return
takes `p` steps and the left delimiter supplies the entry step, so the total
is `2p + 2`. Cells beyond `p` are never visited. -/
theorem incrementTM_run_succ_ofCfg {k : ℕ} {x : List Bool} (i : Fin k)
    (w v : List Bool) (hv : incFixed w = some v) (d : Cfg k Bool FlagPhase x)
    (hstate : d.state = some FlagPhase.run)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      d.workTapes i (d.workTapePos i + p) = FinTM.bufferTape w p) :
    (incrementTM k i).runFrom d (2 * (w.takeWhile id).length + 2) =
        { d with
          state := some (FlagPhase.done true)
          workTapes := fun j q =>
            if j = i ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ)
              then FinTM.bufferTape v (q - d.workTapePos j)
            else d.workTapes j q } ∧
      (∀ t < 2 * (w.takeWhile id).length + 2, ∀ b : Bool,
        ((incrementTM k i).runFrom d t).state ≠ some (FlagPhase.done b)) ∧
      (∀ (j : Fin k) (t : ℕ), t ≤ 2 * (w.takeWhile id).length + 2 →
        if j = i then
          ((incrementTM k i).runFrom d t).workTapePos j ∈
            Finset.Icc (d.workTapePos j - 1)
              (d.workTapePos j + ((w.takeWhile id).length : ℤ))
        else ((incrementTM k i).runFrom d t).workTapePos j = d.workTapePos j) := by
  sorry

/-- **Increment, framed overflow** (design §12.6; spec, fill pending). If the
delimited word `w` on tape `i` has no successor at its width
(`incFixed w = none`, that is, it is all `true`), the routine reaches the
overflow anchor at exactly `2|w| + 2` and not earlier. The word interval then
holds `|w|` copies of `false`, the enumerator's wrap convention, and
everything else is unchanged. Up to the exit the head stays within
`[pos - 1, pos + |w|]`. This specializes to `Turing.incrementTM_run_overflow`.

**Proof sketch.** The carry pass takes `|w|` steps flipping every cell, the
right delimiter turns the head with the overflow verdict, the return takes
`|w|` steps, and the left delimiter supplies the entry step. -/
theorem incrementTM_run_overflow_ofCfg {k : ℕ} {x : List Bool} (i : Fin k)
    (w : List Bool) (hv : incFixed w = none) (d : Cfg k Bool FlagPhase x)
    (hstate : d.state = some FlagPhase.run)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      d.workTapes i (d.workTapePos i + p) = FinTM.bufferTape w p) :
    (incrementTM k i).runFrom d (2 * w.length + 2) =
        { d with
          state := some (FlagPhase.done false)
          workTapes := fun j q =>
            if j = i ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ)
              then FinTM.bufferTape (List.replicate w.length false) (q - d.workTapePos j)
            else d.workTapes j q } ∧
      (∀ t < 2 * w.length + 2, ∀ b : Bool,
        ((incrementTM k i).runFrom d t).state ≠ some (FlagPhase.done b)) ∧
      (∀ (j : Fin k) (t : ℕ), t ≤ 2 * w.length + 2 →
        if j = i then
          ((incrementTM k i).runFrom d t).workTapePos j ∈
            Finset.Icc (d.workTapePos j - 1) (d.workTapePos j + (w.length : ℤ))
        else ((incrementTM k i).runFrom d t).workTapePos j = d.workTapePos j) := by
  sorry

end Turing

namespace Turing.FinTM

/- F2 local witness copies from Composition.lean and Build/Primitives.lean.
Their transition tables and time proofs are unchanged except for the f2_ prefix;
local copies keep the frozen source modules and their private interfaces intact. -/

/-- The one-state copy machine: emits each input bit moving right, and halts on the
boundary blank. -/
private def f2_idTM : FinTM Bool where
  k := 0
  State := Unit
  tm :=
    { q₀ := ()
      tr := fun _ inp _ =>
        match inp with
        | some b => ⟨SignType.pos, fun i => i.elim0, some b, some ()⟩
        | none => ⟨SignType.zero, fun i => i.elim0, none, none⟩ }

/-- Run invariant of the copy machine: after `t ≤ n` steps it is live, its input head
sits at position `t + 1`, and it has emitted exactly the first `t` input bits. -/
private lemma f2_idTM_run (x : List Bool) : ∀ t, t ≤ x.length →
    (f2_idTM.tm.runFrom (f2_idTM.tm.initCfg x) t).state = some () ∧
    (((f2_idTM.tm.runFrom (f2_idTM.tm.initCfg x) t).inputPos : ℕ) = t + 1) ∧
    (f2_idTM.tm.runFrom (f2_idTM.tm.initCfg x) t).output = x.take t := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨rfl, ?_, rfl⟩
    simp [MultiTapeTM.runFrom]
  | succ t ih =>
    intro ht
    obtain ⟨hstate, hpos, hout⟩ := ih (Nat.le_of_succ_le ht)
    have hrun1 : f2_idTM.tm.runFrom (f2_idTM.tm.initCfg x) (t + 1) =
        (f2_idTM.tm.tr () (some (x[t]'(by omega)))
          ((f2_idTM.tm.runFrom (f2_idTM.tm.initCfg x) t).workTapeSymbols)).apply
          (f2_idTM.tm.runFrom (f2_idTM.tm.initCfg x) t) := by
      rw [MultiTapeTM.runFrom_succ_eq_step']
      unfold MultiTapeTM.step
      rw [hstate]
      dsimp only
      rw [inputSymbolInner (p := t) (by omega) (by omega)]
    refine ⟨?_, ?_, ?_⟩
    · rw [hrun1]
      simp [f2_idTM, Action.apply]
    · rw [hrun1]
      simp only [f2_idTM, Action.apply]
      rw [moveInputPos_pos_of_ne_right _ (by omega)]
      show ((f2_idTM.tm.runFrom (f2_idTM.tm.initCfg x) t).inputPos : ℕ) + 1 = t + 2
      omega
    · rw [hrun1]
      simp only [f2_idTM, Action.apply]
      rw [hout, List.take_succ, List.getElem?_eq_getElem (by omega)]

/-- The zero-work-tape machine whose states form the emission chain for `w`. -/
private def f2_constTM (w : List Bool) : FinTM Bool where
  k := 0
  State := Fin (w.length + 1)
  tm := { q₀ := 0, tr := fun i _ _ => emitAction w id i }

/-- Emit the fixed prefix, then copy the input verbatim. No work tape is needed;
the last finite state is the copy state. -/
private def f2_catalogPrefixTM (w : List Bool) : FinTM Bool where
  k := 0
  State := Fin (w.length + 1)
  tm :=
    { q₀ := 0
      tr := fun q inp _ =>
        if h : q.val < w.length then
          ⟨0, fun i => i.elim0, some w[q.val], some ⟨q.val + 1, by omega⟩⟩
        else match inp with
          | some b => ⟨1, fun i => i.elim0, some b, some q⟩
          | none => ⟨0, fun i => i.elim0, none, none⟩ }

/-- A prefixing-machine configuration with the vacuous work fields suppressed. -/
private def f2_catalogPrefixCfg (w x : List Bool) (q : Option (Fin (w.length + 1)))
    (p : Fin (x.length + 2)) (out : List Bool) : Cfg 0 Bool (Fin (w.length + 1)) x :=
  ⟨q, p, fun i => i.elim0, fun i => i.elim0, out⟩

/-- After `i` prefix steps exactly the first `i` fixed bits have been emitted,
and the input head has not moved. -/
private lemma f2_catalogPrefixTM_emit (w x : List Bool) : ∀ i (hi : i ≤ w.length),
    (f2_catalogPrefixTM w).tm.runFrom ((f2_catalogPrefixTM w).tm.initCfg x) i =
      f2_catalogPrefixCfg w x (some ⟨i, by omega⟩) 1 (w.take i) := by
  intro i
  induction i with
  | zero =>
    intro hi
    apply Cfg.ext_zero_tapes <;> simp [f2_catalogPrefixCfg, f2_catalogPrefixTM]
  | succ i ih =>
    intro hi
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hlt : i < w.length := by omega
    simp only [MultiTapeTM.step, f2_catalogPrefixCfg, f2_catalogPrefixTM, dif_pos hlt, Action.apply]
    apply Cfg.ext_zero_tapes
    · rfl
    · simp
    · rw [List.take_succ, List.getElem?_eq_getElem hlt]

/-- The copy phase emits one input bit per step and preserves the fixed prefix. -/
private lemma f2_catalogPrefixTM_copy (w x : List Bool) : ∀ i (hi : i ≤ x.length),
    (f2_catalogPrefixTM w).tm.runFrom
      (f2_catalogPrefixCfg w x (some ⟨w.length, by omega⟩) 1 w) i =
      f2_catalogPrefixCfg w x (some ⟨w.length, by omega⟩) ⟨i + 1, by omega⟩
        (w ++ x.take i) := by
  intro i
  induction i with
  | zero => intro hi; simp [f2_catalogPrefixCfg]
  | succ i ih =>
    intro hi
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hsym : (f2_catalogPrefixCfg w x (some ⟨w.length, by omega⟩)
        ⟨i + 1, by omega⟩ (w ++ x.take i)).inputSymbol = some (x[i]'(by omega)) :=
      inputSymbolInner i (by simp only [f2_catalogPrefixCfg]; omega) (by omega)
    change ((f2_catalogPrefixTM w).tm.tr ⟨w.length, by omega⟩
      (f2_catalogPrefixCfg w x (some ⟨w.length, by omega⟩) ⟨i + 1, by omega⟩
        (w ++ x.take i)).inputSymbol _).apply _ = _
    rw [hsym]
    simp only [f2_catalogPrefixTM, Nat.lt_irrefl, ↓reduceDIte, Action.apply, f2_catalogPrefixCfg]
    apply Cfg.ext_zero_tapes
    · rfl
    · change moveInputPos (⟨i + 1, by omega⟩ : Fin (x.length + 2)) .pos = _
      rw [moveInputPos_pos_of_ne_right _ (by simp; omega)]
    · rw [List.take_succ, List.getElem?_eq_getElem (by omega), List.append_assoc]

/-- Prefixing computes `w ++ x` in exactly the bound `|w| + |x| + 1`,
including the final blank-reading halting step.

**Proof sketch.** Concatenate the fixed-word emission run and the input-copy
run; the input head then scans the right boundary, so one final step halts
without emitting anything further. This also covers empty prefix and input. -/
private lemma f2_catalogPrefixTM_computes (w : List Bool) :
    (f2_catalogPrefixTM w).ComputesFunInTime (fun x => w ++ x) (fun n => w.length + n + 1) := by
  intro x
  apply (FinTM.computesInTime_iff _ _ _ _).mpr
  dsimp only
  rw [show w.length + x.length + 1 = w.length + (x.length + 1) by omega,
    MultiTapeTM.runFrom_add, f2_catalogPrefixTM_emit w x w.length (Nat.le_refl _)]
  simp only [List.take_length]
  rw [MultiTapeTM.runFrom_succ_eq_step', f2_catalogPrefixTM_copy w x x.length (Nat.le_refl _)]
  simp [f2_catalogPrefixTM, f2_catalogPrefixCfg, MultiTapeTM.step, Cfg.inputSymbol, Fin.ext_iff, Action.apply]


/-- A zero-work-tape configuration indexed by the number of input bits passed. -/
private def f2_scanCfg {S : Type} (x : List Bool) (q : Option S)
    (i : ℕ) (hi : i ≤ x.length) (out : List Bool) : Cfg 0 Bool S x :=
  ⟨q, ⟨i + 1, by omega⟩, fun j => j.elim0, fun j => j.elim0, out⟩

/-- Reading at the indexed input position returns the optional list entry. -/
private lemma f2_scanCfg_read {S : Type} (x : List Bool) (q : Option S)
    (i : ℕ) (hi : i ≤ x.length) (out : List Bool) :
    (f2_scanCfg x q i hi out).inputSymbol = x[i]? := by
  by_cases h : i < x.length
  · rw [List.getElem?_eq_getElem h]
    exact inputSymbolInner i (by simp [f2_scanCfg]; omega) h
  · have he : i = x.length := by omega
    subst i
    simp [f2_scanCfg, Cfg.inputSymbol, Fin.ext_iff]

/-- A copy state emits the next `j` input bits after an arbitrary output prefix.
**Proof sketch.** Induct on the number of copied cells; each transition appends
the scanned bit and moves right. The indexed configuration keeps the boundary
case separate from the actual bit-reading steps. -/
private lemma f2_scanCopy_run {S : Type} (tm : MultiTapeTM 0 Bool S) (q : S)
    (htr : ∀ inp work, tm.tr q inp work = match inp with
      | some b => ⟨.pos, fun j => j.elim0, some b, some q⟩
      | none => ⟨0, fun j => j.elim0, none, none⟩)
    (x out : List Bool) : ∀ j (hj : j ≤ x.length),
    tm.runFrom (f2_scanCfg x (some q) 0 (by omega) out) j =
      f2_scanCfg x (some q) j hj (out ++ x.take j) := by
  intro j
  induction j with
  | zero => intro hj; simp [f2_scanCfg]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    unfold MultiTapeTM.step
    change (tm.tr q (f2_scanCfg x (some q) j (by omega) (out ++ x.take j)).inputSymbol
      _).apply _ = _
    rw [htr, f2_scanCfg_read, List.getElem?_eq_getElem (by omega)]
    apply Cfg.ext_zero_tapes
    · rfl
    · exact moveInputPos_pos_of_ne_right _ (by simp [f2_scanCfg]; omega)
    · simp only [Action.apply, f2_scanCfg, Option.toList_some, List.take_succ,
        List.getElem?_eq_getElem (by omega : j < x.length), List.append_assoc]

/-- After copying the entire input, the right-blank transition halts silently. -/
private lemma f2_scanCopy_finish {S : Type} (tm : MultiTapeTM 0 Bool S) (q : S)
    (htr : ∀ inp work, tm.tr q inp work = match inp with
      | some b => ⟨.pos, fun j => j.elim0, some b, some q⟩
      | none => ⟨0, fun j => j.elim0, none, none⟩)
    (x out : List Bool) :
    tm.runFrom (f2_scanCfg x (some q) 0 (by omega) out) (x.length + 1) =
      f2_scanCfg x none x.length (by omega) (out ++ x) := by
  rw [MultiTapeTM.runFrom_succ_eq_step', f2_scanCopy_run tm q htr x out _ (by omega)]
  unfold MultiTapeTM.step
  change (tm.tr q (f2_scanCfg x (some q) x.length (by omega)
    (out ++ x.take x.length)).inputSymbol _).apply _ = _
  rw [htr, f2_scanCfg_read]
  apply Cfg.ext_zero_tapes <;> simp [Action.apply, f2_scanCfg]

/-- Duplicate the input into the self-delimiting pair: double on the first
pass, rewind silently after emitting the separator's first bit, then emit its
second bit and copy. Every input is legal, so no validation buffer is needed. -/
private def f2_pairDupTM : FinTM Bool where
  k := 0
  State := Fin 5
  tm :=
    { q₀ := 0
      tr := fun q inp _ => match q.val with
        | 0 => match inp with
          | some b => ⟨0, fun j => j.elim0, some b, some 1⟩
          | none => ⟨.neg, fun j => j.elim0, some false, some 2⟩
        | 1 => ⟨.pos, fun j => j.elim0, inp, some 0⟩
        | 2 => match inp with
          | some _ => controlAction .neg (some 2)
          | none => controlAction .pos (some 3)
        | 3 => ⟨0, fun j => j.elim0, some true, some 4⟩
        | _ => match inp with
          | some b => ⟨.pos, fun j => j.elim0, some b, some 4⟩
          | none => ⟨0, fun j => j.elim0, none, none⟩ }

/-- Every two first-pass transitions emit one doubled input bit.
**Proof sketch.** The first transition emits while staying at the scanned
cell, and the second emits that same bit and advances. Induction concatenates
these two-step blocks, leaving the right blank for the separator transition. -/
private lemma f2_pairDup_double (x : List Bool) : ∀ j (hj : j ≤ x.length),
    f2_pairDupTM.tm.runFrom (f2_pairDupTM.tm.initCfg x) (2 * j) =
      f2_scanCfg x (some (0 : Fin 5)) j hj ((x.take j).flatMap fun b => [b, b]) := by
  intro j
  induction j with
  | zero => intro hj; apply Cfg.ext_zero_tapes <;> simp [f2_scanCfg, f2_pairDupTM]
  | succ j ih =>
    intro hj
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by omega,
      MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hread := f2_scanCfg_read x (some (0 : Fin 5)) j (by omega)
      ((x.take j).flatMap fun b => [b, b])
    rw [List.getElem?_eq_getElem (by omega)] at hread
    have hfirst : f2_pairDupTM.tm.step
        (f2_scanCfg x (some (0 : Fin 5)) j (by omega) ((x.take j).flatMap fun b => [b, b])) =
        f2_scanCfg x (some (1 : Fin 5)) j (by omega)
          (((x.take j).flatMap fun b => [b, b]) ++ [x[j]'(by omega)]) := by
      unfold MultiTapeTM.step
      change (f2_pairDupTM.tm.tr (0 : Fin 5) _ _).apply _ = _
      rw [hread]
      apply Cfg.ext_zero_tapes <;> simp [f2_pairDupTM, Action.apply, f2_scanCfg]
    rw [hfirst]
    unfold MultiTapeTM.step
    change (f2_pairDupTM.tm.tr (1 : Fin 5) _ _).apply _ = _
    rw [f2_scanCfg_read, List.getElem?_eq_getElem (by omega)]
    apply Cfg.ext_zero_tapes
    · rfl
    · exact moveInputPos_pos_of_ne_right _ (by simp [f2_scanCfg]; omega)
    · change (((x.take j).flatMap fun b => [b, b]) ++ [x[j]'(by omega)]) ++
        [x[j]'(by omega)] = (x.take (j + 1)).flatMap fun b => [b, b]
      simp only [List.take_succ, List.getElem?_eq_getElem (by omega : j < x.length),
        Option.toList_some, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.append_assoc, List.cons_append, List.nil_append]

/-- The two passes and rewind take exactly `4|x|+4` transitions.
**Proof sketch.** Doubling costs `2|x|`, emitting the first separator bit
costs one, rewind and dispatch cost `|x|+1`, the second separator bit costs
one, and copying with its final blank test costs `|x|+1`. -/
private lemma f2_pairDup_computes (x : List Bool) :
    f2_pairDupTM.ComputesInTime x (pairEncode x x) (4 * (x.length + 1)) := by
  let pre := x.flatMap fun b => [b, b]
  let c : Cfg 0 Bool (Fin 5) x :=
    ⟨some 2, ⟨x.length, by omega⟩, fun j => j.elim0, fun j => j.elim0, pre ++ [false]⟩
  have hsep : f2_pairDupTM.tm.step (f2_scanCfg x (some (0 : Fin 5)) x.length (by omega) pre) = c := by
    unfold MultiTapeTM.step
    change (f2_pairDupTM.tm.tr (0 : Fin 5) _ _).apply _ = _
    rw [f2_scanCfg_read]
    apply Cfg.ext_zero_tapes
    · simp [f2_pairDupTM, c]
    · simpa [f2_pairDupTM, Action.apply, f2_scanCfg, c] using
        moveInputPos_neg_of_ne_left (⟨x.length + 1, by omega⟩ : Fin (x.length + 2))
          (by simp [Fin.ext_iff])
    · simp [f2_pairDupTM, Action.apply, f2_scanCfg, c]
  have hr := rewind_scan f2_pairDupTM.tm (2 : Fin 5) (some (3 : Fin 5)) (fun _ _ => rfl) c rfl (by simp [c])
  have hemit : f2_pairDupTM.tm.step {c with state := some (3 : Fin 5), inputPos := 1} =
      f2_scanCfg x (some (4 : Fin 5)) 0 (by omega) (pre ++ [false, true]) := by
    apply Cfg.ext_zero_tapes <;>
      simp [MultiTapeTM.step, f2_pairDupTM, c, f2_scanCfg, Action.apply, List.append_assoc]
  have h1 : f2_pairDupTM.tm.runFrom (f2_pairDupTM.tm.initCfg x) (2 * x.length + 1) = c := by
    rw [MultiTapeTM.runFrom_succ_eq_step', f2_pairDup_double x x.length (by omega)]
    simpa only [List.take_length] using hsep
  have h2 : f2_pairDupTM.tm.runFrom (f2_pairDupTM.tm.initCfg x)
      (2 * x.length + 1 + (x.length + 1)) =
      {c with state := some (3 : Fin 5), inputPos := 1} := by
    rw [MultiTapeTM.runFrom_add, h1]
    exact hr
  have h3 : f2_pairDupTM.tm.runFrom (f2_pairDupTM.tm.initCfg x)
      (2 * x.length + 1 + (x.length + 1) + 1) =
      f2_scanCfg x (some (4 : Fin 5)) 0 (by omega) (pre ++ [false, true]) := by
    rw [MultiTapeTM.runFrom_succ_eq_step', h2, hemit]
  apply (computesInTime_iff _ _ _ _).mpr
  rw [show 4 * (x.length + 1) = (2 * x.length + 1 + (x.length + 1) + 1) +
    (x.length + 1) by omega, MultiTapeTM.runFrom_add, h3,
    f2_scanCopy_finish f2_pairDupTM.tm (4 : Fin 5) (fun _ _ => rfl)]
  exact ⟨rfl, rfl⟩

/-- Copy a suffix from an already-positioned input head, preserving prior output.
**Proof sketch.** Induct on the suffix. A nonempty suffix emits its first bit
and shifts the prefix/suffix boundary by one. The empty suffix reads the right
blank and halts without another emission. -/
private lemma f2_scanCopy_suffix {S : Type} (tm : MultiTapeTM 0 Bool S) (q : S)
    (htr : ∀ inp work, tm.tr q inp work = match inp with
      | some b => ⟨.pos, fun j => j.elim0, some b, some q⟩
      | none => ⟨0, fun j => j.elim0, none, none⟩)
    (x rest : List Bool) : ∀ pre out (hx : x = pre ++ rest),
    tm.runFrom (f2_scanCfg x (some q) pre.length (by simp [hx]) out) (rest.length + 1) =
      f2_scanCfg x none x.length (by omega) (out ++ rest) := by
  induction rest with
  | nil =>
    intro pre out hx
    subst x
    simp only [List.length_nil, MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change (tm.tr q _ _).apply _ = _
    rw [htr, f2_scanCfg_read]
    apply Cfg.ext_zero_tapes <;> simp [Action.apply, f2_scanCfg]
  | cons b rest ih =>
    intro pre out hx
    have hlen : pre.length < x.length := by simp [hx]
    have hread : x[pre.length]? = some b := by simp [hx]
    have hs : tm.step (f2_scanCfg x (some q) pre.length (by omega) out) =
        f2_scanCfg x (some q) (pre ++ [b]).length (by simp [hx]) (out ++ [b]) := by
      unfold MultiTapeTM.step
      change (tm.tr q _ _).apply _ = _
      rw [htr, f2_scanCfg_read, hread]
      apply Cfg.ext_zero_tapes
      · rfl
      · simpa [f2_scanCfg] using moveInputPos_pos_of_ne_right
          (⟨pre.length + 1, by omega⟩ : Fin (x.length + 2)) (by simp; omega)
      · rfl
    simp only [List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    simpa only [List.append_assoc, List.singleton_append] using
      ih (pre ++ [b]) (out ++ [b]) (by simpa [List.append_assoc] using hx)

/-- A true-prefix scan either remains silent or emits one false per true.
**Proof sketch.** Induct on the prefix length. Taking a shorter prefix gives
the induction hypothesis, and the last entry of the longer prefix identifies
the symbol read by the next transition. -/
private lemma f2_scanTrues_run {S : Type} (tm : MultiTapeTM 0 Bool S) (q : S)
    (emit : Bool)
    (htr : ∀ work, tm.tr q (some true) work =
      ⟨.pos, fun j => j.elim0, if emit then some false else none, some q⟩)
    (x : List Bool) : ∀ j (hj : j ≤ x.length),
    x.take j = List.replicate j true →
    tm.runFrom (f2_scanCfg x (some q) 0 (by omega) []) j =
      f2_scanCfg x (some q) j hj (if emit then List.replicate j false else []) := by
  intro j
  induction j with
  | zero => intro hj hp; cases emit <;> rfl
  | succ j ih =>
    intro hj hp
    have hshort : x.take j = List.replicate j true := by
      have h := congrArg (List.take j) hp
      simpa only [List.take_take, List.take_replicate, Nat.min_eq_left (by omega : j ≤ j + 1)] using h
    have hb : x[j]? = some true := by
      have h := congrArg (fun w : List Bool => w[j]?) hp
      simpa [List.getElem?_take, Nat.lt_succ_self] using h
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega) hshort]
    unfold MultiTapeTM.step
    change (tm.tr q _ _).apply _ = _
    rw [f2_scanCfg_read, hb, htr]
    apply Cfg.ext_zero_tapes
    · rfl
    · exact moveInputPos_pos_of_ne_right _ (by simp [f2_scanCfg]; omega)
    · cases emit <;> simp [Action.apply, f2_scanCfg, List.replicate_succ']

/-- Either every input bit is true (overflow), or its first false splits off
the carry prefix and determines the exact incremented word. -/
private lemma f2_incFixed_cases (x : List Bool) :
    (x = List.replicate x.length true ∧ incFixed x = none) ∨
      ∃ j rest, x = List.replicate j true ++ false :: rest ∧
        incFixed x = some (List.replicate j false ++ true :: rest) := by
  induction x with
  | nil => exact Or.inl ⟨rfl, rfl⟩
  | cons b x ih =>
    cases b with
    | false => exact Or.inr ⟨0, x, rfl, rfl⟩
    | true =>
      rcases ih with ⟨hx, hinc⟩ | ⟨j, rest, hx, hinc⟩
      · exact Or.inl ⟨by simpa only [List.length_cons, List.replicate_succ, List.cons.injEq, true_and] using hx, by simp [incFixed, hinc]⟩
      · exact Or.inr ⟨j + 1, rest, by simp [hx, List.replicate_succ],
          by simp [incFixed, hinc, List.replicate_succ]⟩

/-- Detect a nonoverflowing word silently, rewind, then perform the carry
while emitting. This is the enumerator's carry discipline adapted to native
input and append-only output; unlike the in-place harvest, it validates first. -/
private def f2_incFixedTM : FinTM Bool where
  k := 0
  State := Fin 4
  tm :=
    { q₀ := 0
      tr := fun q inp _ => match q.val with
        | 0 => match inp with
          | some true => ⟨.pos, fun j => j.elim0, none, some 0⟩
          | some false => controlAction .neg (some 1)
          | none => controlAction 0 none
        | 1 => match inp with
          | some _ => controlAction .neg (some 1)
          | none => controlAction .pos (some 2)
        | 2 => match inp with
          | some true => ⟨.pos, fun j => j.elim0, some false, some 2⟩
          | some false => ⟨.pos, fun j => j.elim0, some true, some 3⟩
          | none => controlAction 0 none
        | _ => match inp with
          | some b => ⟨.pos, fun j => j.elim0, some b, some 3⟩
          | none => ⟨0, fun j => j.elim0, none, none⟩ }

/-- Fixed-width increment is computed within `3(|x|+1)` steps, with no output
on overflow, including the empty word.
**Proof sketch.** The all-true case scans and halts silently. Otherwise let
`j` be the first false's index. Detection plus rewind costs `2j+2`; carry
emission and suffix copy cost `|x|+1`. Since `j < |x|`, the advertised
linear envelope covers the whole run. -/
private lemma f2_incFixed_computes (x : List Bool) :
    f2_incFixedTM.ComputesInTime x ((incFixed x).getD []) (3 * (x.length + 1)) := by
  rcases f2_incFixed_cases x with ⟨hx, hinc⟩ | ⟨j, rest, hx, hinc⟩
  · have hr := f2_scanTrues_run f2_incFixedTM.tm (0 : Fin 4) false (fun _ => rfl)
      x x.length (by omega) (by simpa using hx)
    have hh : f2_incFixedTM.ComputesInTime x [] (x.length + 1) := by
      apply (computesInTime_iff _ _ _ _).mpr
      rw [MultiTapeTM.runFrom_succ_eq_step', show f2_incFixedTM.tm.initCfg x =
        f2_scanCfg x (some (0 : Fin 4)) 0 (by omega) [] from
          by apply Cfg.ext_zero_tapes <;> simp [f2_incFixedTM, f2_scanCfg], hr]
      unfold MultiTapeTM.step
      change ((f2_incFixedTM.tm.tr (0 : Fin 4) _ _).apply _).state = none ∧ _
      rw [f2_scanCfg_read]
      simp [f2_incFixedTM, controlAction, Action.apply, f2_scanCfg]
    simpa only [hinc, Option.getD_none] using hh.mono (by omega)
  · have hj : j < x.length := by simp [hx]
    have hpre : x.take j = List.replicate j true := by simp [hx]
    have hread : x[j]? = some false := by simp [hx]
    let c : Cfg 0 Bool (Fin 4) x :=
      ⟨some 1, ⟨j, by omega⟩, fun i => i.elim0, fun i => i.elim0, []⟩
    have hdet : f2_incFixedTM.tm.runFrom (f2_incFixedTM.tm.initCfg x) (j + 1) = c := by
      rw [MultiTapeTM.runFrom_succ_eq_step', show f2_incFixedTM.tm.initCfg x =
        f2_scanCfg x (some (0 : Fin 4)) 0 (by omega) [] from
          by apply Cfg.ext_zero_tapes <;> simp [f2_incFixedTM, f2_scanCfg],
        f2_scanTrues_run f2_incFixedTM.tm (0 : Fin 4) false (fun _ => rfl) x j (by omega) hpre]
      unfold MultiTapeTM.step
      change (f2_incFixedTM.tm.tr (0 : Fin 4) _ _).apply _ = _
      rw [f2_scanCfg_read, hread]
      apply Cfg.ext_zero_tapes
      · rfl
      · simpa [f2_incFixedTM, controlAction, Action.apply, f2_scanCfg, c] using
          moveInputPos_neg_of_ne_left (⟨j + 1, by omega⟩ : Fin (x.length + 2))
            (by simp [Fin.ext_iff])
      · rfl
    have hrew : f2_incFixedTM.tm.runFrom (f2_incFixedTM.tm.initCfg x) (j + 1 + (j + 1)) =
        f2_scanCfg x (some (2 : Fin 4)) 0 (by omega) [] := by
      rw [MultiTapeTM.runFrom_add, hdet]
      exact rewind_scan f2_incFixedTM.tm (1 : Fin 4) (some (2 : Fin 4))
        (fun _ _ => rfl) c rfl (by simp [c]; omega)
    have hemit : f2_incFixedTM.tm.runFrom (f2_scanCfg x (some (2 : Fin 4)) 0 (by omega) [])
        (j + 1) = f2_scanCfg x (some (3 : Fin 4)) (j + 1) (by omega)
          (List.replicate j false ++ [true]) := by
      rw [MultiTapeTM.runFrom_succ_eq_step',
        f2_scanTrues_run f2_incFixedTM.tm (2 : Fin 4) true (fun _ => rfl) x j (by omega) hpre]
      unfold MultiTapeTM.step
      change (f2_incFixedTM.tm.tr (2 : Fin 4) _ _).apply _ = _
      rw [f2_scanCfg_read, hread]
      apply Cfg.ext_zero_tapes
      · rfl
      · exact moveInputPos_pos_of_ne_right _ (by simp [f2_scanCfg]; omega)
      · rfl
    have hcopy := f2_scanCopy_suffix f2_incFixedTM.tm (3 : Fin 4) (fun _ _ => rfl)
      x rest (List.replicate j true ++ [false]) (List.replicate j false ++ [true])
      (by simpa [List.append_assoc] using hx)
    have hh : f2_incFixedTM.ComputesInTime x (List.replicate j false ++ true :: rest)
        ((j + 1 + (j + 1)) + ((j + 1) + (rest.length + 1))) := by
      apply (computesInTime_iff _ _ _ _).mpr
      rw [MultiTapeTM.runFrom_add, hrew, MultiTapeTM.runFrom_add, hemit]
      simp only [List.length_append, List.length_replicate, List.length_singleton] at hcopy
      rw [hcopy]
      exact ⟨rfl, by simp [f2_scanCfg, List.append_assoc]⟩
    have hlen : x.length = j + 1 + rest.length := by simp [hx]; omega
    simpa only [hinc, Option.getD_some] using hh.mono (by omega)

/-- A right-moving zero-tape transition advances the indexed configuration
and appends exactly its optional emission. -/
private lemma f2_scanStep_right {S : Type} (tm : MultiTapeTM 0 Bool S)
    (x : List Bool) (q : S) (q' : Option S) (i : ℕ) (hi : i < x.length)
    (out : List Bool) (emit : Option Bool)
    (htr : ∀ work, tm.tr q x[i]? work = ⟨.pos, fun j => j.elim0, emit, q'⟩) :
    tm.step (f2_scanCfg x (some q) i (by omega) out) =
      f2_scanCfg x q' (i + 1) (by omega) (out ++ emit.toList) := by
  unfold MultiTapeTM.step
  change (tm.tr q _ _).apply _ = _
  rw [f2_scanCfg_read, htr]
  apply Cfg.ext_zero_tapes
  · rfl
  · exact moveInputPos_pos_of_ne_right _ (by simp [f2_scanCfg]; omega)
  · rfl

/-- Scan aligned pairs of bits, retaining just the first bit of the current
block. Only a terminal verdict transition emits output. -/
private def f2_pairValidTM : FinTM Bool where
  k := 0
  State := Option Bool
  tm :=
    { q₀ := none
      tr := fun q inp _ => match q, inp with
        | none, some b => ⟨.pos, fun j => j.elim0, none, some (some b)⟩
        | some b, some c =>
          if b = c then ⟨.pos, fun j => j.elim0, none, some none⟩
          else ⟨.pos, fun j => j.elim0, some (!b && c), none⟩
        | _, none => ⟨0, fun j => j.elim0, some false, none⟩ }

/-- One aligned block either continues silently or halts with its verdict. -/
private lemma f2_pairValid_block (x pre rest : List Bool) (b c : Bool)
    (hx : x = pre ++ b :: c :: rest) :
    f2_pairValidTM.tm.runFrom (f2_scanCfg x (some none) pre.length (by simp [hx]) []) 2 =
      if b = c then f2_scanCfg x (some none) (pre.length + 2) (by simp [hx]) []
      else f2_scanCfg x none (pre.length + 2) (by simp [hx]) [!b && c] := by
  have h1 := f2_scanStep_right f2_pairValidTM.tm x none (some (some b)) pre.length
    (by simp [hx]) [] none (by intro work; simp [hx, f2_pairValidTM])
  have h2 := f2_scanStep_right f2_pairValidTM.tm x (some b)
    (if b = c then some none else none) (pre.length + 1) (by simp [hx])
    [] (if b = c then none else some (!b && c)) (by
      intro work
      have hr : x[pre.length + 1]? = some c := by simp [hx]
      rw [hr]
      by_cases h : b = c <;> simp [f2_pairValidTM, h])
  change f2_pairValidTM.tm.step (f2_pairValidTM.tm.step _) = _
  rw [h1]
  simp only [Option.toList_none, List.append_nil]
  rw [h2]
  by_cases h : b = c <;> simp [h]

/-- The validity scanner halts within one more than the unprocessed length.
**Proof sketch.** Induct in aligned two-bit blocks. The empty and singleton
cases fail on a boundary blank. Equal-bit blocks invoke the induction
hypothesis silently; `01` succeeds and `10` fails immediately, independently
of the suffix. Thus no verdict is emitted before validity is decided. -/
private lemma f2_pairValid_run (x rest : List Bool) : ∀ pre (hx : x = pre ++ rest),
    ∃ t ≤ rest.length + 1,
      (f2_pairValidTM.tm.runFrom
        (f2_scanCfg x (some none) pre.length (by simp [hx]) []) t).state = none ∧
      (f2_pairValidTM.tm.runFrom
        (f2_scanCfg x (some none) pre.length (by simp [hx]) []) t).output =
          [(pairDecode rest).isSome] := by
  induction rest using List.twoStepInduction with
  | nil =>
    intro pre hx
    refine ⟨1, by simp, ?_⟩
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change ((f2_pairValidTM.tm.tr none _ _).apply _).state = none ∧ _
    rw [f2_scanCfg_read]
    simp [hx, f2_pairValidTM, Action.apply, f2_scanCfg, pairDecode]
  | singleton b =>
    intro pre hx
    have h1 := f2_scanStep_right f2_pairValidTM.tm x none (some (some b)) pre.length
      (by simp [hx]) [] none (by intro work; simp [hx, f2_pairValidTM])
    refine ⟨2, by simp, ?_⟩
    change (f2_pairValidTM.tm.step (f2_pairValidTM.tm.step _)).state = none ∧
      (f2_pairValidTM.tm.step (f2_pairValidTM.tm.step _)).output = _
    rw [h1]
    unfold MultiTapeTM.step
    change ((f2_pairValidTM.tm.tr (some b) _ _).apply _).state = none ∧ _
    rw [f2_scanCfg_read]
    cases b <;> simp [hx, f2_pairValidTM, Action.apply, f2_scanCfg, pairDecode]
  | cons_cons b c rest ih _ =>
    intro pre hx
    by_cases h : b = c
    · subst c
      obtain ⟨t, ht, hs, ho⟩ := ih (pre ++ [b, b]) (by simpa [List.append_assoc] using hx)
      refine ⟨2 + t, by simp only [List.length_cons] at *; omega, ?_⟩
      rw [MultiTapeTM.runFrom_add, f2_pairValid_block x pre rest b b hx, if_pos rfl]
      simp only [List.length_append, List.length_cons, List.length_nil] at hs ho
      refine ⟨hs, ?_⟩
      cases b <;> simpa [pairDecode] using ho
    · refine ⟨2, by simp, ?_⟩
      rw [f2_pairValid_block x pre rest b c hx, if_neg h]
      cases b <;> cases c <;> simp_all [f2_scanCfg, pairDecode]

/-- The validity test starts with an empty aligned prefix and uses the
linear envelope `|x|+1`. -/
private lemma f2_pairValid_computes (x : List Bool) :
    f2_pairValidTM.ComputesInTime x [(pairDecode x).isSome] (x.length + 1) := by
  obtain ⟨t, ht, hs, ho⟩ := f2_pairValid_run x x [] rfl
  have hinit : f2_pairValidTM.tm.initCfg x = f2_scanCfg x (some none) 0 (by omega) [] := by
    apply Cfg.ext_zero_tapes <;> simp [f2_pairValidTM, f2_scanCfg]
  have h : f2_pairValidTM.ComputesInTime x [(pairDecode x).isSome] t := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [hinit]
    exact ⟨hs, ho⟩
  exact h.mono ht


/-- A shared extractor buffers the decoded prefix, validates the separator,
rewinds and replays the buffer, then optionally copies the suffix. The two
flags select the first component, the second, or their concatenation. -/
private def f2_pairExtractTM (first second : Bool) : FinTM Bool where
  k := 1
  State := Option Bool ⊕ Fin 3
  tm :=
    { q₀ := .inl none
      tr := fun q inp work => match q with
        | .inl none => match inp with
          | some b => ⟨.pos, fun _ => (none, 0), none, some (.inl (some b))⟩
          | none => ⟨0, fun _ => (none, 0), none, none⟩
        | .inl (some b) => match inp with
          | none => ⟨0, fun _ => (none, 0), none, none⟩
          | some c =>
            if b = c then
              ⟨.pos, fun _ => (some (some b), .pos), none, some (.inl none)⟩
            else if b then ⟨.pos, fun _ => (none, 0), none, none⟩
            else ⟨.pos, fun _ => (none, .neg), none, some (.inr 0)⟩
        | .inr q => match q.val with
          | 0 => match work 0 with
            | some _ => ⟨0, fun _ => (none, .neg), none, some (.inr 0)⟩
            | none => ⟨0, fun _ => (none, .pos), none, some (.inr 1)⟩
          | 1 => match work 0 with
            | some b => ⟨0, fun _ => (none, .pos), if first then some b else none, some (.inr 1)⟩
            | none => ⟨0, fun _ => (none, 0), none, some (.inr 2)⟩
          | _ => if second then match inp with
              | some b => ⟨.pos, fun _ => (none, 0), some b, some (.inr 2)⟩
              | none => ⟨0, fun _ => (none, 0), none, none⟩
            else ⟨0, fun _ => (none, 0), none, none⟩ }

/-- The shared extractor's one-buffer configurations. -/
private def f2_extractCfg (x : List Bool) (q : Option (Option Bool ⊕ Fin 3))
    (i : ℕ) (hi : i ≤ x.length) (a : List Bool) (z : ℤ) (out : List Bool) :
    Cfg 1 Bool (Option Bool ⊕ Fin 3) x :=
  ⟨q, ⟨i + 1, by omega⟩, fun _ => bufferTape a, fun _ => z, out⟩

/-- The extractor reads the indexed input entry independently of its buffer. -/
private lemma f2_extractCfg_read (x : List Bool) (q : Option (Option Bool ⊕ Fin 3))
    (i : ℕ) (hi : i ≤ x.length) (a : List Bool) (z : ℤ) (out : List Bool) :
    (f2_extractCfg x q i hi a z out).inputSymbol = x[i]? :=
  f2_scanCfg_read x q i hi out

/-- Reading the first half of an aligned block preserves the buffer silently. -/
private lemma f2_extract_first (first second : Bool) (x pre rest a : List Bool) (b : Bool)
    (hx : x = pre ++ b :: rest) :
    (f2_pairExtractTM first second).tm.step
      (f2_extractCfg x (some (.inl none)) pre.length (by simp [hx]) a a.length []) =
      f2_extractCfg x (some (.inl (some b))) (pre.length + 1) (by simp [hx]) a a.length [] := by
  unfold MultiTapeTM.step
  change ((f2_pairExtractTM first second).tm.tr (.inl none) _ _).apply _ = _
  rw [f2_extractCfg_read]
  have hr : x[pre.length]? = some b := by simp [hx]
  rw [hr]
  refine Cfg.ext rfl ?_ rfl ?_ rfl
  · exact moveInputPos_pos_of_ne_right _ (by simp [f2_extractCfg, hx])
  · funext i; simp [f2_pairExtractTM, Action.apply, f2_extractCfg]

/-- Equal-bit blocks append one decoded bit; `01` begins replay and `10`
halts silently. In particular, neither transition emits physical output. -/
private lemma f2_extract_block (first second : Bool) (x pre rest a : List Bool) (b c : Bool)
    (hx : x = pre ++ b :: c :: rest) :
    (f2_pairExtractTM first second).tm.runFrom
      (f2_extractCfg x (some (.inl none)) pre.length (by simp [hx]) a a.length []) 2 =
      if b = c then f2_extractCfg x (some (.inl none)) (pre.length + 2) (by simp [hx])
          (a ++ [b]) (a ++ [b]).length []
      else if b then f2_extractCfg x none (pre.length + 2) (by simp [hx]) a a.length []
      else f2_extractCfg x (some (.inr 0)) (pre.length + 2) (by simp [hx]) a (a.length - 1) [] := by
  change (f2_pairExtractTM first second).tm.step ((f2_pairExtractTM first second).tm.step _) = _
  rw [f2_extract_first first second x pre (c :: rest) a b hx]
  unfold MultiTapeTM.step
  change ((f2_pairExtractTM first second).tm.tr (.inl (some b)) _ _).apply _ = _
  rw [f2_extractCfg_read]
  have hr : x[pre.length + 1]? = some c := by simp [hx]
  rw [hr]
  have hm : moveInputPos (⟨pre.length + 1 + 1, by simp [hx]⟩ : Fin (x.length + 2)) .pos =
      ⟨pre.length + 2 + 1, by simp [hx]; omega⟩ := by
    exact moveInputPos_pos_of_ne_right _ (by simp [hx])
  cases b <;> cases c <;> simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
  all_goals refine Cfg.ext rfl hm ?_ ?_ rfl
  all_goals first
    | rfl
    | (funext i; exact (bufferTape_append a _).symm)
    | (funext i; simp [f2_pairExtractTM, Action.apply, f2_extractCfg])

/-- Rewinding the validated buffer from cell `j-1` takes `j+1` transitions.
**Proof sketch.** At the left blank, move right and enter replay. Otherwise
read a buffer cell, move left, and invoke the induction hypothesis. -/
private lemma f2_extract_rewind (first second : Bool) (x a : List Bool)
    (i : ℕ) (hi : i ≤ x.length) : ∀ j, j ≤ a.length →
    (f2_pairExtractTM first second).tm.runFrom
      (f2_extractCfg x (some (.inr 0)) i hi a ((j : ℤ) - 1) []) (j + 1) =
      f2_extractCfg x (some (.inr 1)) i hi a 0 [] := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    simp only [f2_pairExtractTM, f2_extractCfg, Cfg.workTapeSymbols, Nat.cast_zero,
      zero_sub, bufferTape_left]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext k; simp [Action.apply]
  | succ j ih =>
    intro hj
    have hs : (f2_pairExtractTM first second).tm.step
        (f2_extractCfg x (some (.inr 0)) i hi a (((j + 1 : ℕ) : ℤ) - 1) []) =
        f2_extractCfg x (some (.inr 0)) i hi a ((j : ℤ) - 1) [] := by
      have hz : (((j + 1 : ℕ) : ℤ) - 1) = j := by omega
      rw [hz]
      unfold MultiTapeTM.step
      simp only [f2_pairExtractTM, f2_extractCfg, Cfg.workTapeSymbols, bufferTape_nat,
        List.getElem?_eq_getElem (by omega : j < a.length)]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext k; simp [Action.apply, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Replay reads the buffered word once; the first-component flag decides
whether those reads emit. At the right blank the controller starts the suffix.
**Proof sketch.** Induct on the number of replayed cells. Each live step
preserves the tape and appends either its bit or nothing. -/
private lemma f2_extract_replay (first second : Bool) (x a : List Bool)
    (i : ℕ) (hi : i ≤ x.length) : ∀ j (_hj : j ≤ a.length),
    (f2_pairExtractTM first second).tm.runFrom
      (f2_extractCfg x (some (.inr 1)) i hi a 0 []) j =
      f2_extractCfg x (some (.inr 1)) i hi a j (if first then a.take j else []) := by
  intro j
  induction j with
  | zero => intro hj; cases first <;> rfl
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    unfold MultiTapeTM.step
    simp only [f2_pairExtractTM, f2_extractCfg, Cfg.workTapeSymbols, bufferTape_nat,
      List.getElem?_eq_getElem (by omega : j < a.length)]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ ?_
    · funext k; simp [Action.apply]
    · change (if first then a.take j else []) ++
        (if first then some (a[j]'(by omega)) else none).toList =
          (if first then a.take (j + 1) else [])
      have ht : a.take j ++ [a[j]'(by omega)] = a.take (j + 1) := by
        rw [List.take_succ, List.getElem?_eq_getElem (by omega)]
        rfl
      cases first with
      | false => rfl
      | true => exact ht

/-- Replay's right-blank test dispatches to the suffix state silently. -/
private lemma f2_extract_replay_finish (first second : Bool) (x a : List Bool)
    (i : ℕ) (hi : i ≤ x.length) :
    (f2_pairExtractTM first second).tm.runFrom
      (f2_extractCfg x (some (.inr 1)) i hi a 0 []) (a.length + 1) =
      f2_extractCfg x (some (.inr 2)) i hi a a.length (if first then a else []) := by
  rw [MultiTapeTM.runFrom_succ_eq_step', f2_extract_replay first second x a i hi _ (by omega)]
  unfold MultiTapeTM.step
  simp only [f2_pairExtractTM, f2_extractCfg, Cfg.workTapeSymbols, bufferTape_nat,
    List.getElem?_length, List.take_length]
  refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ ?_
  · funext k; simp [Action.apply]
  · simp [Action.apply]

/-- With suffix copying enabled, the final phase emits the remaining input.
**Proof sketch.** The input prefix grows by one at each emitting transition;
the buffer and its head remain fixed. A right-blank test supplies the final
halting step. This is the one-buffer version of the private suffix-copy lemma. -/
private lemma f2_extract_suffix (first : Bool) (x rest a : List Bool) :
    ∀ pre out (hx : x = pre ++ rest),
    (f2_pairExtractTM first true).tm.runFrom
      (f2_extractCfg x (some (.inr 2)) pre.length (by simp [hx]) a a.length out)
        (rest.length + 1) =
      f2_extractCfg x none x.length (by omega) a a.length (out ++ rest) := by
  induction rest with
  | nil =>
    intro pre out hx
    simp only [List.length_nil, MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change ((f2_pairExtractTM first true).tm.tr (.inr 2) _ _).apply _ = _
    rw [f2_extractCfg_read]
    have hr : x[pre.length]? = none := by simp [hx]
    rw [hr]
    refine Cfg.ext rfl ?_ rfl ?_ ?_
    · simp [f2_pairExtractTM, Action.apply, f2_extractCfg, hx]
    · funext k; simp [f2_pairExtractTM, Action.apply, f2_extractCfg]
    · simp [f2_pairExtractTM, Action.apply, f2_extractCfg]
  | cons b rest ih =>
    intro pre out hx
    have hs : (f2_pairExtractTM first true).tm.step
        (f2_extractCfg x (some (.inr 2)) pre.length (by simp [hx]) a a.length out) =
        f2_extractCfg x (some (.inr 2)) (pre ++ [b]).length (by simp [hx])
          a a.length (out ++ [b]) := by
      unfold MultiTapeTM.step
      change ((f2_pairExtractTM first true).tm.tr (.inr 2) _ _).apply _ = _
      rw [f2_extractCfg_read]
      have hr : x[pre.length]? = some b := by simp [hx]
      rw [hr]
      refine Cfg.ext rfl ?_ rfl ?_ rfl
      · simpa [f2_extractCfg] using moveInputPos_pos_of_ne_right
          (⟨pre.length + 1, by simp [hx]; omega⟩ : Fin (x.length + 2)) (by simp [hx])
      · funext k; simp [f2_pairExtractTM, Action.apply, f2_extractCfg]
    simp only [List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    simpa only [List.append_assoc, List.singleton_append] using
      ih (pre ++ [b]) (out ++ [b]) (by simpa [List.append_assoc] using hx)

/-- Once validation succeeds, rewind, replay, and optional suffix copying
cost at most `2|a|+|rest|+3` steps.
**Proof sketch.** The rewind costs `|a|+1`, and replay plus dispatch costs
`|a|+1`. Disabled suffix copying halts in one step; enabled copying uses
`|rest|+1`. Only these postvalidation phases emit output. -/
private lemma f2_extract_finish (first second : Bool) (x pre rest a : List Bool)
    (hx : x = pre ++ rest) :
    ∃ t ≤ 2 * a.length + rest.length + 3,
      ((f2_pairExtractTM first second).tm.runFrom
        (f2_extractCfg x (some (.inr 0)) pre.length (by simp [hx]) a (a.length - 1) []) t).state = none ∧
      ((f2_pairExtractTM first second).tm.runFrom
        (f2_extractCfg x (some (.inr 0)) pre.length (by simp [hx]) a (a.length - 1) []) t).output =
          (if first then a else []) ++ (if second then rest else []) := by
  have hp : (f2_pairExtractTM first second).tm.runFrom
      (f2_extractCfg x (some (.inr 0)) pre.length (by simp [hx]) a (a.length - 1) [])
        ((a.length + 1) + (a.length + 1)) =
      f2_extractCfg x (some (.inr 2)) pre.length (by simp [hx]) a a.length (if first then a else []) := by
    rw [MultiTapeTM.runFrom_add, f2_extract_rewind first second x a _ _ _ (by omega),
      f2_extract_replay_finish]
  cases second with
  | false =>
    refine ⟨(a.length + 1) + (a.length + 1) + 1, by omega, ?_⟩
    rw [MultiTapeTM.runFrom_succ_eq_step', hp]
    simp [MultiTapeTM.step, f2_pairExtractTM, f2_extractCfg, Action.apply]
  | true =>
    refine ⟨((a.length + 1) + (a.length + 1)) + (rest.length + 1), by omega, ?_⟩
    rw [MultiTapeTM.runFrom_add, hp, f2_extract_suffix first x rest a pre _ hx]
    exact ⟨rfl, rfl⟩

/-- The silent aligned parser either rejects or validates and invokes replay.
**Proof sketch.** Induct over aligned two-bit blocks while carrying the
already-decoded buffer. A doubled bit costs two steps and enlarges the buffer
by one; the linear potential `3|rest|+2|a|+5` pays for both effects. Missing
and forbidden separators halt silently. At `01`, apply the validated finish
ledger. The result includes the previously buffered prefix only on success. -/
private lemma f2_extract_run (first second : Bool) (x rest : List Bool) :
    ∀ pre a (hx : x = pre ++ rest),
    ∃ t ≤ 3 * rest.length + 2 * a.length + 5,
      ((f2_pairExtractTM first second).tm.runFrom
        (f2_extractCfg x (some (.inl none)) pre.length (by simp [hx]) a a.length []) t).state = none ∧
      ((f2_pairExtractTM first second).tm.runFrom
        (f2_extractCfg x (some (.inl none)) pre.length (by simp [hx]) a a.length []) t).output =
          match pairDecode rest with
          | some (b, c) => (if first then a ++ b else []) ++ (if second then c else [])
          | none => [] := by
  induction rest using List.twoStepInduction with
  | nil =>
    intro pre a hx
    refine ⟨1, by omega, ?_⟩
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change (((f2_pairExtractTM first second).tm.tr (.inl none) _ _).apply _).state = none ∧ _
    rw [f2_extractCfg_read]
    simp [hx, f2_pairExtractTM, Action.apply, f2_extractCfg, pairDecode]
  | singleton b =>
    intro pre a hx
    refine ⟨2, by simp, ?_⟩
    change ((f2_pairExtractTM first second).tm.step ((f2_pairExtractTM first second).tm.step _)).state = none ∧
      ((f2_pairExtractTM first second).tm.step ((f2_pairExtractTM first second).tm.step _)).output = _
    rw [f2_extract_first first second x pre [] a b hx]
    unfold MultiTapeTM.step
    change (((f2_pairExtractTM first second).tm.tr (.inl (some b)) _ _).apply _).state = none ∧ _
    rw [f2_extractCfg_read]
    cases b <;> simp [hx, f2_pairExtractTM, Action.apply, f2_extractCfg, pairDecode]
  | cons_cons b c rest ih _ =>
    intro pre a hx
    by_cases h : b = c
    · subst c
      obtain ⟨t, ht, hs, ho⟩ := ih (pre ++ [b, b]) (a ++ [b]) (by simpa [List.append_assoc] using hx)
      refine ⟨2 + t, by simp only [List.length_append, List.length_cons, List.length_nil] at *; omega, ?_⟩
      rw [MultiTapeTM.runFrom_add, f2_extract_block first second x pre rest a b b hx, if_pos rfl]
      simp only [List.length_append, List.length_cons, List.length_nil] at hs ho
      refine ⟨?_, ?_⟩
      · simpa only [List.length_append, List.length_cons, List.length_nil] using hs
      · cases b <;> cases hd : pairDecode rest with
        | none => simpa [pairDecode, hd] using ho
        | some p => cases p; simpa [pairDecode, hd, List.append_assoc] using ho
    · cases b <;> cases c
      · exact False.elim (h rfl)
      · obtain ⟨t, ht, hs, ho⟩ := f2_extract_finish first second x (pre ++ [false, true]) rest a
          (by simpa [List.append_assoc] using hx)
        refine ⟨2 + t, by simp only [List.length_cons]; omega, ?_⟩
        rw [MultiTapeTM.runFrom_add, f2_extract_block first second x pre rest a false true hx]
        simp only [Bool.false_eq_true, ↓reduceIte]
        simp only [List.length_append, List.length_cons, List.length_nil] at hs ho
        exact ⟨hs, by simpa [pairDecode] using ho⟩
      · refine ⟨2, by simp, ?_⟩
        rw [f2_extract_block first second x pre rest a true false hx]
        simp [f2_extractCfg, pairDecode]
      · exact False.elim (h rfl)

/-- The three extractor modes share the uniform linear envelope `5(|x|+1)`.
The initial buffer and decoded prefix are empty. -/
private lemma f2_pairExtract_computes (first second : Bool) (x : List Bool) :
    (f2_pairExtractTM first second).ComputesInTime x
      (match pairDecode x with
        | some (a, b) => (if first then a else []) ++ (if second then b else [])
        | none => []) (5 * (x.length + 1)) := by
  obtain ⟨t, ht, hs, ho⟩ := f2_extract_run first second x x [] [] rfl
  have hinit : (f2_pairExtractTM first second).tm.initCfg x =
      f2_extractCfg x (some (.inl none)) 0 (by omega) [] 0 [] := by
    apply Cfg.ext <;> simp [f2_pairExtractTM, f2_extractCfg, MultiTapeTM.initCfg, Cfg.init]
  have hh : (f2_pairExtractTM first second).ComputesInTime x
      (match pairDecode x with
        | some (a, b) => (if first then a else []) ++ (if second then b else [])
        | none => []) t := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [hinit]
    exact ⟨hs, by simpa using ho⟩
  exact hh.mono (by simp only [List.length_nil] at ht; omega)


/-- Control for copying the side length, nested unary loops, and constant emission. -/
private inductive f2_CatalogPolyControl (c C : ℕ) where
  | copy | setup
  | loop (i : Fin (c + 1))
  | rewind (i : Fin (c + 1))
  | advance (i : Fin (c + 2))
  | emit (j : Fin (C + 1))

/-- Enumerate the control through a finite sum representation, privately. -/
private instance f2_catalogPolyControlFintype (c C : ℕ) : Fintype (f2_CatalogPolyControl c C) :=
  derive_fintype% _

/-- Compare control states through the same finite sum representation, privately. -/
private instance f2_catalogPolyControlDecidableEq (c C : ℕ) : DecidableEq (f2_CatalogPolyControl c C) :=
  (proxy_equiv% (f2_CatalogPolyControl c C)).symm.decidableEq

/-- A unary word of length `q`, surrounded by blanks. -/
private def f2_catalogPolyTape (q : ℕ) (z : ℤ) : Option Bool :=
  if 0 ≤ z ∧ z < q then some true else none

/-- Move just the selected work head, preserving every tape. -/
private def f2_catalogPolyMove {c C : ℕ} (i : Fin (c + 1)) (d : SignType)
    (s : f2_CatalogPolyControl c C) : Action (c + 1) Bool (f2_CatalogPolyControl c C) :=
  ⟨0, fun j => (none, if j = i then d else 0), none, some s⟩

/-- Finite machine emitting `C` symbols at each point of a `(c+1)`-dimensional
box. The unary loop tapes are copied in parallel; rewinding a completed inner
loop costs its side length, charged to the iterations that just completed. -/
private def f2_catalogPolyUnaryTM (c C : ℕ) : FinTM Bool where
  k := c + 1
  State := f2_CatalogPolyControl c C
  tm := {
    q₀ := .copy
    tr := fun s inp w => match s with
      | .copy => match inp with
        | some _ => ⟨.pos, fun _ => (some (some true), .pos), none, some .copy⟩
        | none => ⟨0, fun _ => (some (some true), .neg), none, some .setup⟩
      | .setup =>
        if w 0 = none then
          ⟨0, fun _ => (none, .pos), none, some (.loop (Fin.last c))⟩
        else ⟨0, fun _ => (none, .neg), none, some .setup⟩
      | .loop i =>
        if w i = none then f2_catalogPolyMove i .neg (.rewind i)
        else ⟨0, fun _ => (none, 0), none,
          some (if h : i.val = 0 then .emit ⟨C, Nat.lt_succ_self C⟩
            else .loop ⟨i.val - 1, by omega⟩)⟩
      | .rewind i =>
        if w i = none then f2_catalogPolyMove i .pos (.advance ⟨i.val + 1, by omega⟩)
        else f2_catalogPolyMove i .neg (.rewind i)
      | .advance i =>
        if h : i.val < c + 1 then f2_catalogPolyMove ⟨i.val, h⟩ .pos (.loop ⟨i.val, h⟩)
        else ⟨0, fun _ => (none, 0), none, none⟩
      | .emit j =>
        if h : j.val = 0 then ⟨0, fun _ => (none, 0), none, some (.advance 0)⟩
        else ⟨0, fun _ => (none, 0), some true,
          some (.emit ⟨j.val - 1, by omega⟩)⟩ }

/-- A loop configuration, with all unary tapes installed and arbitrary head positions. -/
private def f2_catalogPolyCfg {c C : ℕ} (x : List Bool) (q : ℕ)
    (s : f2_CatalogPolyControl c C) (h : Fin (c + 1) → ℤ) (o : List Bool) :
    Cfg (c + 1) Bool (f2_CatalogPolyControl c C) x :=
  ⟨some s, ⟨x.length + 1, by omega⟩, fun _ => f2_catalogPolyTape q, h, o⟩

/-- Applying a head-only action updates exactly the selected head. -/
private lemma f2_catalogPolyMove_apply {c C : ℕ} (x : List Bool) (q : ℕ)
    (s s' : f2_CatalogPolyControl c C) (h : Fin (c + 1) → ℤ) (o : List Bool)
    (i : Fin (c + 1)) (d : SignType) :
    (f2_catalogPolyMove i d s').apply (f2_catalogPolyCfg x q s h o) =
      f2_catalogPolyCfg x q s' (Function.update h i (h i + d.cast)) o := by
  apply Cfg.ext
  · rfl
  · exact moveInputPos_zero _
  · rfl
  · funext j
    by_cases hj : j = i <;> simp [f2_catalogPolyMove, f2_catalogPolyCfg, Action.apply, hj]
  · simp [f2_catalogPolyMove, f2_catalogPolyCfg, Action.apply]

/-- The finite emission chain appends exactly its remaining number of true bits. -/
private lemma f2_catalogPoly_emit {c C : ℕ} (x : List Bool) (q : ℕ)
    (h : Fin (c + 1) → ℤ) : ∀ j (hj : j ≤ C) (o : List Bool),
    (f2_catalogPolyUnaryTM c C).tm.runFrom
      (f2_catalogPolyCfg x q (.emit ⟨j, by omega⟩) h o) (j + 1) =
      f2_catalogPolyCfg x q (.advance 0) h (o ++ List.replicate j true) := by
  intro j
  induction j with
  | zero =>
    intro hj o
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    apply Cfg.ext <;> simp [MultiTapeTM.step, f2_catalogPolyUnaryTM, f2_catalogPolyCfg, Action.apply]
  | succ j ih =>
    intro hj o
    have hs : (f2_catalogPolyUnaryTM c C).tm.step
        (f2_catalogPolyCfg x q (.emit ⟨j + 1, by omega⟩) h o) =
        f2_catalogPolyCfg x q (.emit ⟨j, by omega⟩) h (o ++ [true]) := by
      apply Cfg.ext <;> simp [MultiTapeTM.step, f2_catalogPolyUnaryTM, f2_catalogPolyCfg, Action.apply]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs, ih (by omega)]
    simp [List.replicate_succ, List.append_assoc]

/-- Rewinding crosses a unary prefix and its left boundary, restoring head zero.
The other loop heads and the accumulated output remain unchanged. -/
private lemma f2_catalogPoly_rewind {c C : ℕ} (x : List Bool) (q : ℕ)
    (h : Fin (c + 1) → ℤ) (o : List Bool) (i : Fin (c + 1)) :
    ∀ j (_hj : j ≤ q),
    (f2_catalogPolyUnaryTM c C).tm.runFrom
      (f2_catalogPolyCfg x q (.rewind i) (Function.update h i ((j : ℤ) - 1)) o) (j + 1) =
      f2_catalogPolyCfg x q (.advance ⟨i.val + 1, by omega⟩) (Function.update h i 0) o := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    change ((if _ then _ else _) : Action (c + 1) Bool (f2_CatalogPolyControl c C)).apply _ = _
    simp only [Cfg.workTapeSymbols, f2_catalogPolyCfg, Function.update_self,
      Nat.cast_zero, zero_sub, f2_catalogPolyTape, show ¬(0 ≤ (-1 : ℤ) ∧ (-1 : ℤ) < q) by omega,
      ↓reduceIte]
    simpa [f2_catalogPolyCfg] using f2_catalogPolyMove_apply x q (.rewind i)
      (.advance ⟨i.val + 1, by omega⟩) (Function.update h i (-1)) o i .pos
  | succ j ih =>
    intro hj
    have hs : (f2_catalogPolyUnaryTM c C).tm.step
        (f2_catalogPolyCfg x q (.rewind i) (Function.update h i ((j + 1 : ℕ) - 1 : ℤ)) o) =
        f2_catalogPolyCfg x q (.rewind i) (Function.update h i ((j : ℤ) - 1)) o := by
      change ((if _ then _ else _) : Action (c + 1) Bool (f2_CatalogPolyControl c C)).apply _ = _
      simp only [Cfg.workTapeSymbols, f2_catalogPolyCfg, Function.update_self,
        Nat.cast_add, Nat.cast_one, add_sub_cancel_right, f2_catalogPolyTape,
        if_pos (show 0 ≤ (j : ℤ) ∧ (j : ℤ) < q by omega),
        reduceCtorEq, ↓reduceIte]
      simpa [f2_catalogPolyCfg, sub_eq_add_neg] using f2_catalogPolyMove_apply x q (.rewind i)
        (.rewind i) (Function.update h i (j : ℤ)) o i .neg
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Returning from an inner loop advances the next outer loop by one cell. -/
private lemma f2_catalogPoly_advance {c C : ℕ} (x : List Bool) (q : ℕ)
    (h : Fin (c + 1) → ℤ) (o : List Bool) (i : Fin (c + 1)) :
    (f2_catalogPolyUnaryTM c C).tm.step
      (f2_catalogPolyCfg x q (.advance ⟨i.val, by omega⟩) h o) =
      f2_catalogPolyCfg x q (.loop i) (Function.update h i (h i + 1)) o := by
  simp only [MultiTapeTM.step, f2_catalogPolyUnaryTM, f2_catalogPolyCfg, i.isLt, ↓reduceDIte]
  simpa [f2_catalogPolyCfg] using f2_catalogPolyMove_apply x q
    (.advance ⟨i.val, by omega⟩) (.loop i) h o i .pos

/-- Exact time for a full nest of unary loops, with `r` loop levels. -/
private def f2_catalogPolyCost (q C : ℕ) : ℕ → ℕ
  | 0 => C + 1
  | r + 1 => q * (f2_catalogPolyCost q C r + 2) + q + 2

/-- A loop at level `i` executes its remaining iterations, resets its head,
and returns to its parent with exactly `C*q^i` new symbols per iteration.

**Proof sketch.** Induct on the nesting level, then on the number of remaining
iterations. At level zero the body is the finite emission chain. At higher
levels it is a complete inner loop. Each body has one dispatch and one parent
advance; after the final iteration the unary rewind restores the head to zero.
The invariant leaves all outer heads arbitrary, making recursive calls composable. -/
private lemma f2_catalogPoly_loop {c C : ℕ} (x : List Bool) (q : ℕ) (_hq : 0 < q) :
    ∀ i (hi : i < c + 1) (h : Fin (c + 1) → ℤ)
      (_hh : ∀ k, k.val ≤ i → h k = 0) (o : List Bool) (r j : ℕ), j + r = q →
    (f2_catalogPolyUnaryTM c C).tm.runFrom
      (f2_catalogPolyCfg x q (.loop ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ (j : ℤ)) o)
      (r * (f2_catalogPolyCost q C i + 2) + q + 2) =
      f2_catalogPolyCfg x q (.advance ⟨i + 1, by omega⟩) h
        (o ++ List.replicate (r * (C * q ^ i)) true) := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi h hh o r
    have hbody (j : ℕ) (hj : j < q) (o : List Bool) :
        (f2_catalogPolyUnaryTM c C).tm.runFrom
          (f2_catalogPolyCfg x q (.loop ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ (j : ℤ)) o)
          (f2_catalogPolyCost q C i + 2) =
        f2_catalogPolyCfg x q (.loop ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ ((j : ℤ) + 1))
          (o ++ List.replicate (C * q ^ i) true) := by
      let h' := Function.update h ⟨i, hi⟩ (j : ℤ)
      have hread : (f2_catalogPolyCfg (C := C) x q (.loop ⟨i, hi⟩) h' o).workTapeSymbols ⟨i, hi⟩ =
          some true := by simp [h', f2_catalogPolyCfg, Cfg.workTapeSymbols, f2_catalogPolyTape, hj]
      have hs : (f2_catalogPolyUnaryTM c C).tm.step (f2_catalogPolyCfg x q (.loop ⟨i, hi⟩) h' o) =
          f2_catalogPolyCfg x q (if hz : i = 0 then .emit ⟨C, by omega⟩
            else .loop ⟨i - 1, by omega⟩) h' o := by
        unfold MultiTapeTM.step
        change ((f2_catalogPolyUnaryTM c C).tm.tr (.loop ⟨i, hi⟩) _ _).apply _ = _
        simp only [f2_catalogPolyUnaryTM, hread, reduceCtorEq, ↓reduceIte]
        apply Cfg.ext <;> simp [f2_catalogPolyCfg, Action.apply]
      by_cases hz : i = 0
      · subst i
        simp only [↓reduceDIte] at hs
        change (f2_catalogPolyUnaryTM c C).tm.runFrom (f2_catalogPolyCfg x q (.loop 0) h' o) _ = _
        rw [show f2_catalogPolyCost q C 0 + 2 = 1 + (C + 1) + 1 by simp [f2_catalogPolyCost]; omega,
          MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add,
          show (f2_catalogPolyUnaryTM c C).tm.runFrom (f2_catalogPolyCfg x q (.loop 0) h' o) 1 =
            f2_catalogPolyCfg x q (.emit ⟨C, by omega⟩) h' o by simpa using hs,
          f2_catalogPoly_emit x q h' C (le_refl C),
          MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
        simpa [h'] using f2_catalogPoly_advance (C := C) x q h'
          (o ++ List.replicate C true) (⟨0, hi⟩ : Fin (c + 1))
      · have hlow : ∀ k : Fin (c + 1), k.val ≤ i - 1 → h' k = 0 := by
          intro k hk
          have hne : k ≠ ⟨i, hi⟩ := by intro he; have := congrArg Fin.val he; simp at this; omega
          simp only [h', Function.update_of_ne hne]
          exact hh k (by omega)
        have hinner := ih (i - 1) (by omega) (by omega) h' hlow o q 0 (by omega)
        have hupdate : Function.update h' ⟨i - 1, by omega⟩ 0 = h' := by
          rw [← hlow ⟨i - 1, by omega⟩ (le_refl _)]
          exact Function.update_eq_self _ _
        have hi' : i - 1 + 1 = i := by omega
        have hout : q * (C * q ^ (i - 1)) = C * q ^ i := by
          calc
            q * (C * q ^ (i - 1)) = C * (q ^ (i - 1) * q) := by ring
            _ = C * q ^ i := by simp only [← Nat.pow_succ, Nat.succ_eq_add_one, hi']
        simp only [dif_neg hz] at hs
        simp only [Nat.cast_zero] at hinner
        rw [hupdate] at hinner
        have hinner' : (f2_catalogPolyUnaryTM c C).tm.runFrom
            (f2_catalogPolyCfg x q (.loop ⟨i - 1, by omega⟩) h' o) (f2_catalogPolyCost q C i) =
            f2_catalogPolyCfg x q (.advance ⟨i, by omega⟩) h'
              (o ++ List.replicate (C * q ^ i) true) := by
          have hcost : q * (f2_catalogPolyCost q C (i - 1) + 2) + q + 2 =
              f2_catalogPolyCost q C i := by
            calc
              _ = f2_catalogPolyCost q C (i - 1 + 1) := rfl
              _ = f2_catalogPolyCost q C i := by rw [hi']
          simpa only [hcost, hi', hout] using hinner
        change (f2_catalogPolyUnaryTM c C).tm.runFrom (f2_catalogPolyCfg x q (.loop ⟨i, hi⟩) h' o) _ = _
        rw [show f2_catalogPolyCost q C i + 2 = 1 + f2_catalogPolyCost q C i + 1 by omega,
          MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add,
          show (f2_catalogPolyUnaryTM c C).tm.runFrom (f2_catalogPolyCfg x q (.loop ⟨i, hi⟩) h' o) 1 =
            f2_catalogPolyCfg x q (.loop ⟨i - 1, by omega⟩) h' o by simpa using hs,
          hinner', MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
        simpa [h'] using f2_catalogPoly_advance (C := C) x q h'
          (o ++ List.replicate (C * q ^ i) true) (⟨i, hi⟩ : Fin (c + 1))
    induction r generalizing o with
    | zero =>
      intro j hj
      have hj' : j = q := by omega
      subst j
      have hs : (f2_catalogPolyUnaryTM c C).tm.step
          (f2_catalogPolyCfg x q (.loop ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ (q : ℤ)) o) =
          f2_catalogPolyCfg x q (.rewind ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ ((q : ℤ) - 1)) o := by
        unfold MultiTapeTM.step
        change ((f2_catalogPolyUnaryTM c C).tm.tr (.loop ⟨i, hi⟩) _ _).apply _ = _
        simp only [f2_catalogPolyUnaryTM, Cfg.workTapeSymbols, f2_catalogPolyCfg, Function.update_self,
          f2_catalogPolyTape, lt_self_iff_false, and_false, ↓reduceIte]
        simpa [f2_catalogPolyCfg, sub_eq_add_neg] using f2_catalogPolyMove_apply x q (.loop ⟨i, hi⟩)
          (.rewind ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ (q : ℤ)) o ⟨i, hi⟩ .neg
      simp only [Nat.zero_mul, Nat.zero_add, List.replicate_zero, List.append_nil]
      rw [MultiTapeTM.runFrom_succ_eq_step, hs, f2_catalogPoly_rewind x q h o ⟨i, hi⟩ q (le_refl q)]
      rw [← hh ⟨i, hi⟩ (le_refl _), Function.update_eq_self]
    | succ r ihr =>
      intro j hj
      have hjq : j < q := by omega
      rw [show (r + 1) * (f2_catalogPolyCost q C i + 2) + q + 2 =
          (f2_catalogPolyCost q C i + 2) + (r * (f2_catalogPolyCost q C i + 2) + q + 2) by ring,
        MultiTapeTM.runFrom_add, hbody j hjq]
      have hr := ihr (o ++ List.replicate (C * q ^ i) true) (j + 1) (by omega)
      simp only [Nat.cast_add, Nat.cast_one] at hr
      rw [hr, List.append_assoc, ← List.replicate_add]
      congr 3
      ring

/-- Writing at the first blank extends a unary tape by exactly one cell. -/
private lemma f2_catalogPolyTape_write (q : ℕ) :
    Function.update (f2_catalogPolyTape q) (q : ℤ) (some true) = f2_catalogPolyTape (q + 1) := by
  funext z
  by_cases hz : z = (q : ℤ)
  · subst z
    simp [f2_catalogPolyTape]
  · rw [Function.update_of_ne hz]
    unfold f2_catalogPolyTape
    have he : (0 ≤ z ∧ z < (q : ℤ)) ↔ (0 ≤ z ∧ z < ((q + 1 : ℕ) : ℤ)) := by omega
    simp only [he]

/-- The full loop costs at most a constant times the number of box points.
Each level's rewinds are charged to its `q` completed body iterations. -/
private lemma f2_catalogPolyCost_le (q C : ℕ) (hq : 0 < q) : ∀ r,
    f2_catalogPolyCost q C r ≤ (C + 1 + 5 * r) * q ^ r := by
  intro r
  induction r with
  | zero => simp [f2_catalogPolyCost]
  | succ r ih =>
    have hqpow : q ≤ q ^ (r + 1) := by
      simpa only [Nat.pow_one] using Nat.pow_le_pow_right hq (show 1 ≤ r + 1 by omega)
    have hpos : 1 ≤ q ^ (r + 1) := Nat.one_le_pow _ _ hq
    calc
      f2_catalogPolyCost q C (r + 1) = q * (f2_catalogPolyCost q C r + 2) + q + 2 := rfl
      _ ≤ q * ((C + 1 + 5 * r) * q ^ r + 2) + q + 2 :=
        Nat.add_le_add_right (Nat.add_le_add_right
          (Nat.mul_le_mul_left q (Nat.add_le_add_right ih 2)) q) 2
      _ = (C + 1 + 5 * r) * q ^ (r + 1) + 3 * q + 2 := by rw [Nat.pow_succ]; ring
      _ ≤ (C + 1 + 5 * r) * q ^ (r + 1) + 5 * q ^ (r + 1) := by omega
      _ = (C + 1 + 5 * (r + 1)) * q ^ (r + 1) := by ring

/-- Configurations while copying the input length to every unary loop tape. -/
private def f2_catalogPolyCopyCfg (c C : ℕ) (x : List Bool) (i : ℕ) (hi : i ≤ x.length) :
    Cfg (c + 1) Bool (f2_CatalogPolyControl c C) x :=
  ⟨some .copy, ⟨i + 1, by omega⟩, fun _ => f2_catalogPolyTape i, fun _ => i, []⟩

/-- One input scan copies its length, in unary, onto every loop tape at once. -/
private lemma f2_catalogPoly_copy (c C : ℕ) (x : List Bool) : ∀ i (hi : i ≤ x.length),
    (f2_catalogPolyUnaryTM c C).tm.runFrom ((f2_catalogPolyUnaryTM c C).tm.initCfg x) i =
      f2_catalogPolyCopyCfg c C x i hi := by
  intro i
  induction i with
  | zero =>
    intro hi
    apply Cfg.ext
    · rfl
    · rfl
    · funext k z
      simp [MultiTapeTM.initCfg, Cfg.init, f2_catalogPolyCopyCfg, f2_catalogPolyTape,
        show ¬(0 ≤ z ∧ z < (0 : ℤ)) by omega]
    · rfl
    · rfl
  | succ i ih =>
    intro hi
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hin : (f2_catalogPolyCopyCfg c C x i (by omega)).inputSymbol = some x[i] :=
      inputSymbolInner i (by simp [f2_catalogPolyCopyCfg, Nat.add_comm]) (by omega)
    unfold MultiTapeTM.step
    change ((f2_catalogPolyUnaryTM c C).tm.tr .copy _ _).apply _ = _
    rw [hin]
    apply Cfg.ext
    · rfl
    · apply Fin.ext
      change (moveInputPos (⟨i + 1, by omega⟩ : Fin (x.length + 2)) .pos).val = i + 1 + 1
      rw [moveInputPos_pos_of_ne_right _ (by simp; omega)]
    · funext k
      exact f2_catalogPolyTape_write i
    · funext k
      simp [f2_catalogPolyUnaryTM, f2_catalogPolyCopyCfg, Action.apply, Nat.add_comm]
    · rfl

/-- The startup rewind moves all synchronized heads left, then enters the outermost loop. -/
private lemma f2_catalogPoly_setup (c C : ℕ) (x : List Bool) (q : ℕ) : ∀ j (_hj : j ≤ q),
    (f2_catalogPolyUnaryTM c C).tm.runFrom
      (f2_catalogPolyCfg x q .setup (fun _ => (j : ℤ) - 1) []) (j + 1) =
      f2_catalogPolyCfg x q (.loop (Fin.last c)) (fun _ => 0) [] := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    apply Cfg.ext <;>
      simp [MultiTapeTM.step, f2_catalogPolyUnaryTM, f2_catalogPolyCfg, Cfg.workTapeSymbols, f2_catalogPolyTape, Action.apply]
  | succ j ih =>
    intro hj
    have hs : (f2_catalogPolyUnaryTM c C).tm.step
        (f2_catalogPolyCfg x q .setup (fun _ => ((j + 1 : ℕ) : ℤ) - 1) []) =
        f2_catalogPolyCfg x q .setup (fun _ => (j : ℤ) - 1) [] := by
      apply Cfg.ext <;>
        simp [MultiTapeTM.step, f2_catalogPolyUnaryTM, f2_catalogPolyCfg, Cfg.workTapeSymbols, f2_catalogPolyTape,
          show (j : ℤ) < q by omega, Action.apply, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Startup installs side length `|x|+1` and puts every loop head at zero.
The final extra unary cell handles empty input without a special case. -/
private lemma f2_catalogPoly_start (c C : ℕ) (x : List Bool) :
    (f2_catalogPolyUnaryTM c C).tm.runFrom ((f2_catalogPolyUnaryTM c C).tm.initCfg x)
      (2 * (x.length + 1)) =
      f2_catalogPolyCfg x (x.length + 1) (.loop (Fin.last c)) (fun _ => 0) [] := by
  have hs : (f2_catalogPolyUnaryTM c C).tm.step
      (f2_catalogPolyCopyCfg c C x x.length (le_refl _)) =
      f2_catalogPolyCfg x (x.length + 1) .setup (fun _ => (x.length : ℤ) - 1) [] := by
    have hin : (f2_catalogPolyCopyCfg c C x x.length (le_refl _)).inputSymbol = none := by
      simp [f2_catalogPolyCopyCfg, Cfg.inputSymbol]
    unfold MultiTapeTM.step
    change ((f2_catalogPolyUnaryTM c C).tm.tr .copy _ _).apply _ = _
    rw [hin]
    apply Cfg.ext
    · rfl
    · exact moveInputPos_zero _
    · funext k
      exact f2_catalogPolyTape_write x.length
    · funext k
      simp [f2_catalogPolyUnaryTM, f2_catalogPolyCopyCfg, f2_catalogPolyCfg, Action.apply, sub_eq_add_neg]
    · rfl
  have hpre : (f2_catalogPolyUnaryTM c C).tm.runFrom ((f2_catalogPolyUnaryTM c C).tm.initCfg x)
      (x.length + 1) =
      f2_catalogPolyCfg x (x.length + 1) .setup (fun _ => (x.length : ℤ) - 1) [] := by
    rw [MultiTapeTM.runFrom_succ_eq_step', f2_catalogPoly_copy c C x x.length (le_refl _), hs]
  rw [show 2 * (x.length + 1) = (x.length + 1) + (x.length + 1) by omega,
    MultiTapeTM.runFrom_add, hpre]
  exact f2_catalogPoly_setup c C x (x.length + 1) x.length (by omega)

/-- The explicit generator computes the exact unary catalogPolynomial in linear time
in its number of box points. This includes coefficient zero and empty input.

**Proof sketch.** Startup costs `2(n+1)`. The full outer loop emits
`C(n+1)^(c+1)` symbols and costs at most `(C+1+5(c+1))(n+1)^(c+1)`.
One final transition halts; `n+1 ≤ (n+1)^(c+1)` absorbs startup. -/
private lemma f2_catalogPoly_unary_computes (c C : ℕ) :
    (f2_catalogPolyUnaryTM c C).ComputesFunInTime
      (fun x => List.replicate (C * (x.length + 1) ^ (c + 1)) true)
      (fun n => (C + 5 * (c + 1) + 4) * (n + 1) ^ (c + 1)) := by
  intro x
  have hl := f2_catalogPoly_loop (c := c) (C := C) x (x.length + 1) (Nat.succ_pos _) c (by omega)
    (fun _ => 0) (by simp) [] (x.length + 1) 0 (by omega)
  have hout : (x.length + 1) * (C * (x.length + 1) ^ c) =
      C * (x.length + 1) ^ (c + 1) := by rw [Nat.pow_succ]; ring
  have hloop : (f2_catalogPolyUnaryTM c C).tm.runFrom
      (f2_catalogPolyCfg x (x.length + 1) (.loop (Fin.last c)) (fun _ => 0) [])
      (f2_catalogPolyCost (x.length + 1) C (c + 1)) =
      f2_catalogPolyCfg x (x.length + 1) (.advance (Fin.last (c + 1))) (fun _ => 0)
        (List.replicate (C * (x.length + 1) ^ (c + 1)) true) := by
    simpa [f2_catalogPolyCost, hout] using hl
  have hbase : (f2_catalogPolyUnaryTM c C).ComputesInTime x
      (List.replicate (C * (x.length + 1) ^ (c + 1)) true)
      (2 * (x.length + 1) + f2_catalogPolyCost (x.length + 1) C (c + 1) + 1) := by
    apply (FinTM.computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_add, f2_catalogPoly_start, hloop]
    simp [MultiTapeTM.step, f2_catalogPolyUnaryTM, f2_catalogPolyCfg, Action.apply]
  apply hbase.mono
  have hp : x.length + 1 ≤ (x.length + 1) ^ (c + 1) := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right (Nat.succ_pos x.length)
      (show 1 ≤ c + 1 by omega)
  have hpos : 1 ≤ (x.length + 1) ^ (c + 1) := Nat.one_le_pow _ _ (Nat.succ_pos _)
  calc
    _ ≤ 2 * (x.length + 1) +
        (C + 1 + 5 * (c + 1)) * (x.length + 1) ^ (c + 1) + 1 :=
      Nat.add_le_add_right (Nat.add_le_add_left
        (f2_catalogPolyCost_le (x.length + 1) C (Nat.succ_pos _) (c + 1)) _) 1
    _ ≤ (C + 1 + 5 * (c + 1)) * (x.length + 1) ^ (c + 1) +
        3 * (x.length + 1) ^ (c + 1) := by omega
    _ = _ := by ring



/-- After initialization each loop bank remains a fixed unary interval. The
active loop head may scan its right blank; the active rewind head may scan its
left blank; all other active indices stay strictly inside the installed bank. -/
private def f2_polyHeads {d C : ℕ} (q : ℕ)
    (s : Option (f2_CatalogPolyControl d C)) (h : Fin (d + 1) → ℤ) : Prop :=
  match s with
  | none => ∀ j, -1 ≤ h j ∧ h j ≤ q
  | some (.loop i) => ∀ j, 0 ≤ h j ∧ h j ≤ q ∧ (j ≠ i → h j < q)
  | some (.rewind i) => ∀ j, -1 ≤ h j ∧ h j < q ∧ (j ≠ i → 0 ≤ h j)
  | some (.advance _) | some (.emit _) => ∀ j, 0 ≤ h j ∧ h j < q
  | _ => False

/-- The loop-phase invariant implies the common closed head interval. -/
private lemma f2_polyHeads_bounds {d C q : ℕ}
    {s : Option (f2_CatalogPolyControl d C)} {h : Fin (d + 1) → ℤ}
    (hp : f2_polyHeads q s h) (j : Fin (d + 1)) :
    -1 ≤ h j ∧ h j ≤ q := by
  cases s with
  | none => exact hp j
  | some s =>
    cases s <;> simp only [f2_polyHeads] at hp
    all_goals first | contradiction | (have := hp j; omega)

/-- The nested-loop transitions preserve the installed unary words and the
phase-specific head intervals, independently of output length or round count.
**Proof sketch.** Only initialization writes. A loop's right move can reach its
right blank but no farther; a rewind turns on the left blank at minus one.
Advance changes one index, and emission changes no work head. -/
private lemma f2_poly_step {d C q : ℕ} {x : List Bool} (hq : 0 < q)
    (c : Cfg (d + 1) Bool (f2_CatalogPolyControl d C) x)
    (hw : c.workTapes = fun _ => f2_catalogPolyTape q)
    (hp : f2_polyHeads q c.state c.workTapePos) :
    ((f2_catalogPolyUnaryTM d C).tm.step c).workTapes =
        (fun _ => f2_catalogPolyTape q) ∧
      f2_polyHeads q ((f2_catalogPolyUnaryTM d C).tm.step c).state
        ((f2_catalogPolyUnaryTM d C).tm.step c).workTapePos := by
  have hr (i : Fin (d + 1)) : c.workTapeSymbols i =
      if 0 ≤ c.workTapePos i ∧ c.workTapePos i < q then some true else none := by
    simp only [Cfg.workTapeSymbols, hw, f2_catalogPolyTape]
  cases hs : c.state with
  | none => simpa only [MultiTapeTM.step, hs] using And.intro hw hp
  | some s =>
    simp only [hs] at hp
    cases s with
    | copy => exact False.elim hp
    | setup => exact False.elim hp
    | loop i =>
      dsimp only [f2_polyHeads] at hp
      by_cases hblank : c.workTapeSymbols i = none
      · constructor
        · simpa [MultiTapeTM.step, hs, f2_catalogPolyUnaryTM, hblank,
            f2_catalogPolyMove, Action.apply] using hw
        · simp only [MultiTapeTM.step, hs, f2_catalogPolyUnaryTM, hblank,
            ↓reduceIte, f2_catalogPolyMove, Action.apply, f2_polyHeads]
          intro j
          have hj := hp j
          by_cases he : j = i
          · subst j
            simp only [↓reduceIte, SignType.cast]
            omega
          · simp only [he, ↓reduceIte, SignType.cast]
            have := hj.2.2 he
            omega
      · have hi : c.workTapePos i < q := by
          rw [hr] at hblank
          split at hblank <;> simp_all
        have hall (j : Fin (d + 1)) : 0 ≤ c.workTapePos j ∧ c.workTapePos j < q := by
          have hj := hp j
          by_cases he : j = i
          · simpa [he] using And.intro (hp i).1 hi
          · exact ⟨hj.1, hj.2.2 he⟩
        constructor
        · simpa [MultiTapeTM.step, hs, f2_catalogPolyUnaryTM, hblank, Action.apply] using hw
        · simp only [MultiTapeTM.step, hs, f2_catalogPolyUnaryTM, hblank, ↓reduceIte,
            Action.apply]
          split <;> simp only [f2_polyHeads, SignType.cast, add_zero]
          · exact hall
          · intro j
            have := hall j
            exact ⟨this.1, le_of_lt this.2, fun _ => this.2⟩
    | rewind i =>
      dsimp only [f2_polyHeads] at hp
      by_cases hblank : c.workTapeSymbols i = none
      · have hi : c.workTapePos i = -1 := by
          have hlo := (hp i).1
          have hhi := (hp i).2.1
          rw [hr] at hblank
          have hn : ¬(0 ≤ c.workTapePos i ∧ c.workTapePos i < q) := by
            simpa only [ite_eq_right_iff, Option.some_ne_none, imp_false] using hblank
          omega
        constructor
        · simpa [MultiTapeTM.step, hs, f2_catalogPolyUnaryTM, hblank,
            f2_catalogPolyMove, Action.apply] using hw
        · simp only [MultiTapeTM.step, hs, f2_catalogPolyUnaryTM, hblank,
            ↓reduceIte, f2_catalogPolyMove, Action.apply, f2_polyHeads]
          intro j
          have hj := hp j
          by_cases he : j = i
          · subst j
            simp only [↓reduceIte, SignType.cast]
            omega
          · simp only [he, ↓reduceIte, SignType.cast, add_zero]
            exact ⟨hj.2.2 he, hj.2.1⟩
      · have hi : 0 ≤ c.workTapePos i := by
          rw [hr] at hblank
          split at hblank <;> simp_all
        constructor
        · simpa [MultiTapeTM.step, hs, f2_catalogPolyUnaryTM, hblank,
            f2_catalogPolyMove, Action.apply] using hw
        · simp only [MultiTapeTM.step, hs, f2_catalogPolyUnaryTM, hblank,
            ↓reduceIte, f2_catalogPolyMove, Action.apply, f2_polyHeads]
          intro j
          have hj := hp j
          by_cases he : j = i
          · subst j
            simp only [↓reduceIte, SignType.cast]
            omega
          · simp only [he, ↓reduceIte, SignType.cast, add_zero]
            exact hj
    | advance i =>
      dsimp only [f2_polyHeads] at hp
      by_cases hi : i.val < d + 1
      · constructor
        · simpa [MultiTapeTM.step, hs, f2_catalogPolyUnaryTM, hi,
            f2_catalogPolyMove, Action.apply] using hw
        · simp only [MultiTapeTM.step, hs, f2_catalogPolyUnaryTM, hi,
            ↓reduceDIte, f2_catalogPolyMove, Action.apply, f2_polyHeads]
          intro j
          have hj := hp j
          by_cases he : j = ⟨i.val, hi⟩
          · simp only [he, ↓reduceIte, SignType.cast]
            simp only [he] at hj
            omega
          · simp only [he, ↓reduceIte, SignType.cast, add_zero]
            exact ⟨hj.1, le_of_lt hj.2, fun _ => hj.2⟩
      · constructor
        · simpa [MultiTapeTM.step, hs, f2_catalogPolyUnaryTM, hi, Action.apply] using hw
        · simp only [MultiTapeTM.step, hs, f2_catalogPolyUnaryTM, hi, ↓reduceDIte,
            Action.apply, f2_polyHeads, SignType.cast, add_zero]
          intro j
          have := hp j
          omega
    | emit j =>
      constructor
      · simp only [MultiTapeTM.step, hs, f2_catalogPolyUnaryTM]
        split <;> simpa only [Action.apply] using hw
      · simp only [MultiTapeTM.step, hs, f2_catalogPolyUnaryTM, Action.apply]
        split <;> simpa only [f2_polyHeads, SignType.cast, add_zero] using hp

/-- A work head lies within the number of elapsed steps of its starting cell.
This is a trajectory bound obtained by adding the one-step movement bounds. -/
private lemma f2_head_steps {k : ℕ} {S : Type} {x : List Bool}
    (M : MultiTapeTM k Bool S) (c : Cfg k Bool S x) (t : ℕ) (i : Fin k) :
    c.workTapePos i - (t : ℤ) ≤ (M.runFrom c t).workTapePos i ∧
      (M.runFrom c t).workTapePos i ≤ c.workTapePos i + (t : ℤ) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hs := abs_le.mp (M.workTapePos_step_le (M.runFrom c t) i)
    rw [MultiTapeTM.runFrom_succ_eq_step']
    push_cast
    constructor <;> omega

/-- The generator's all-time work space is linear in the input length.
**Proof sketch.** Startup lasts `2(n+1)` steps from the origin, so its entire
trajectory fits the interval of that radius. The preserved loop invariant
confines every later head to `[-1,n+1]`, including after halt. Contain the
inclusive visited images in the larger fixed interval and sum its cardinality;
the number of loop iterations never appears in this bound. -/
private lemma f2_poly_space (d C : ℕ) (x : List Bool) (t : ℕ) :
    (f2_catalogPolyUnaryTM d C).tm.spaceUsed
      ((f2_catalogPolyUnaryTM d C).tm.initCfg x) t ≤
        (5 * (d + 1)) * (x.length + 1) := by
  let M := (f2_catalogPolyUnaryTM d C).tm
  let c := f2_catalogPolyCfg (c := d) (C := C) x (x.length + 1)
    (.loop (Fin.last d)) (fun _ => 0) []
  have hinv (u : ℕ) : (M.runFrom c u).workTapes =
      (fun _ => f2_catalogPolyTape (x.length + 1)) ∧
      f2_polyHeads (x.length + 1) (M.runFrom c u).state (M.runFrom c u).workTapePos := by
    induction u with
    | zero =>
      refine ⟨rfl, ?_⟩
      simp [c, f2_catalogPolyCfg, f2_polyHeads]
      omega
    | succ u ih =>
      rw [MultiTapeTM.runFrom_succ_eq_step']
      exact f2_poly_step (Nat.succ_pos _) _ ih.1 ih.2
  have hpos (u : ℕ) (i : Fin (d + 1)) :
      -(2 * (x.length + 1) : ℤ) ≤ (M.runFrom (M.initCfg x) u).workTapePos i ∧
        (M.runFrom (M.initCfg x) u).workTapePos i ≤ (2 * (x.length + 1) : ℤ) := by
    by_cases hu : u ≤ 2 * (x.length + 1)
    · have h := f2_head_steps M (M.initCfg x) u i
      change 0 - (u : ℤ) ≤ _ ∧ _ ≤ 0 + (u : ℤ) at h
      constructor <;> omega
    · rw [show u = 2 * (x.length + 1) + (u - 2 * (x.length + 1)) by omega,
        MultiTapeTM.runFrom_add, f2_catalogPoly_start]
      have h := f2_polyHeads_bounds (hinv (u - 2 * (x.length + 1))).2 i
      dsimp only [c, M] at h
      constructor <;> omega
  have hcard (i : Fin (d + 1)) : M.spaceUsedByTape (M.initCfg x) t i ≤
      5 * (x.length + 1) := by
    have hsub : M.visitedByTapeHead (M.initCfg x) t i ⊆
        Finset.Icc (-(2 * (x.length + 1) : ℤ)) (2 * (x.length + 1) : ℤ) := by
      intro z hz
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_Icc.mpr (hpos u i)
    exact (Finset.card_le_card hsub).trans (by rw [Int.card_Icc]; omega)
  change M.spaceUsed (M.initCfg x) t ≤ _
  unfold MultiTapeTM.spaceUsed
  calc
    _ ≤ ∑ _i : Fin (d + 1), 5 * (x.length + 1) :=
      Finset.sum_le_sum (fun i _ => hcard i)
    _ = _ := by simp; ring

/-- Increment a little-endian binary word, extending it on overflow. -/
private def f2_counterInc : List Bool → List Bool
  | [] => [true]
  | false :: bs => true :: bs
  | true :: bs => false :: f2_counterInc bs

/-- The number of initial true bits cleared by an increment. -/
private def f2_counterCarry : List Bool → ℕ
  | true :: bs => f2_counterCarry bs + 1
  | _ => 0

/-- Each cleared true bit decreases the potential by one; the final write adds one.
This is the local accounting identity behind the amortized bound. -/
private lemma f2_counterInc_potential (bs : List Bool) :
    (f2_counterInc bs).count true + f2_counterCarry bs = bs.count true + 1 := by
  induction bs with
  | nil => simp [f2_counterInc, f2_counterCarry]
  | cons b bs ih =>
    cases b with
    | false => simp [f2_counterInc, f2_counterCarry]
    | true => simp [f2_counterInc, f2_counterCarry]; omega

/-- The list increment is exactly successor in `Nat.bits`, including overflow.
**Proof sketch.** Binary induction: a low zero becomes one without a carry; a
low one becomes zero and applies the induction hypothesis to the high part. -/
private lemma f2_counterInc_bits (n : ℕ) : f2_counterInc n.bits = (n + 1).bits := by
  induction n using Nat.binaryRec' with
  | zero => simp [f2_counterInc]
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn]
    cases b with
    | false =>
      change true :: n.bits = (2 * n + 1).bits
      exact (Nat.bit1_bits n).symm
    | true =>
      simp only [f2_counterInc, ih]
      have he : Nat.bit true n + 1 = 2 * (n + 1) := by simp [Nat.bit_val]; omega
      rw [he, Nat.bit0_bits _ (by omega)]

/-- An increment grows the word by at most one cell, and all cleared cells lie
within the incremented word. -/
private lemma f2_counterInc_length (bs : List Bool) :
    (f2_counterInc bs).length ≤ bs.length + 1 ∧
      f2_counterCarry bs ≤ (f2_counterInc bs).length := by
  induction bs with
  | nil => simp [f2_counterInc, f2_counterCarry]
  | cons b bs ih =>
    cases b <;> simp only [f2_counterInc, f2_counterCarry, List.length_cons] <;> omega

/-- One carry transition, with the first transition also advancing the input. -/
private def f2_counterBump (d : SignType) (w : Option Bool) : Action 1 Bool (Fin 4) :=
  if w = some true then
    ⟨d, fun _ => (some (some false), .pos), none, some 1⟩
  else ⟨d, fun _ => (some (some true), .neg), none, some 2⟩

/-- The audit's four-state counter: count = 0, carry = 1, rewind = 2, emit = 3.
[AB09, §1.3 examples], implemented by the phase-1 reaudit's transition table. -/
private def f2_counterTM : FinTM Bool where
  k := 1
  State := Fin 4
  tm :=
    { q₀ := 0
      tr := fun q inp work =>
        if q = 0 then
          match inp with
          | none => ⟨.zero, fun _ => (none, .zero), none, some 3⟩
          | some _ => f2_counterBump .pos (work 0)
        else if q = 1 then f2_counterBump .zero (work 0)
        else if q = 2 then
          match work 0 with
          | none => ⟨.zero, fun _ => (none, .pos), none, some 0⟩
          | some _ => ⟨.zero, fun _ => (none, .neg), none, some 2⟩
        else
          match work 0 with
          | none => ⟨.zero, fun _ => (none, .zero), none, none⟩
          | some b => ⟨.zero, fun _ => (none, .pos), some b, some 3⟩ }

/-- A finite word on nonnegative cells, with a blank at every other cell. -/
private def f2_counterTape (bs : List Bool) (z : ℤ) : Option Bool :=
  if z < 0 then none else bs[z.toNat]?

/-- Canonical configurations for carry, rewind, count, and emission invariants. -/
private def f2_counterCfg (x : List Bool) (q : Fin 4) (p : Fin (x.length + 2))
    (z : ℤ) (bs out : List Bool) : Cfg 1 Bool (Fin 4) x :=
  ⟨some q, p, fun _ => f2_counterTape bs, fun _ => z, out⟩

/-- Reading after a prefix gives the head of the remaining word (blank if empty). -/
private lemma f2_counterTape_read (pre bs : List Bool) :
    f2_counterTape (pre ++ bs) pre.length = bs.head? := by
  simp only [f2_counterTape, if_neg (by omega : ¬(pre.length : ℤ) < 0), Int.toNat_natCast,
    List.getElem?_append_right (le_refl _), Nat.sub_self]
  cases bs <;> rfl

/-- Replace the first suffix bit, or extend the word if the suffix is empty.
**Proof sketch.** At the write position use the updated value. Before that
position both tapes read the unchanged prefix; afterwards both read the old tail.
Negative cells remain blank. -/
private lemma f2_counterTape_write (pre bs : List Bool) (b : Bool) :
    Function.update (f2_counterTape (pre ++ bs)) (pre.length : ℤ) (some b) =
      f2_counterTape (pre ++ b :: bs.tail) := by
  funext z
  by_cases hz : z = (pre.length : ℤ)
  · subst z
    simp [f2_counterTape_read]
  · rw [Function.update_of_ne hz]
    unfold f2_counterTape
    by_cases hn : z < 0
    · simp only [if_pos hn]
    · simp only [if_neg hn]
      by_cases hl : z.toNat < pre.length
      · rw [List.getElem?_append_left hl, List.getElem?_append_left hl]
      · have hg : pre.length < z.toNat := by omega
        rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega),
          List.getElem?_cons, if_neg (by omega), List.getElem?_tail]
        congr 1
        omega

/-- One carry transition updates exactly the currently scanned cell. -/
private lemma f2_counter_carry_step (x : List Bool) (p : Fin (x.length + 2))
    (pre bs : List Bool) :
    f2_counterTM.tm.step (f2_counterCfg x 1 p pre.length (pre ++ bs) []) =
      if bs.head? = some true then
        f2_counterCfg x 1 p (pre.length + 1) (pre ++ false :: bs.tail) []
      else f2_counterCfg x 2 p (pre.length - 1) (pre ++ true :: bs.tail) [] := by
  unfold MultiTapeTM.step
  change (f2_counterTM.tm.tr (1 : Fin 4) _ _).apply _ = _
  simp only [f2_counterTM, show (1 : Fin 4) ≠ 0 from by decide, ↓reduceIte]
  change (f2_counterBump .zero (f2_counterTape (pre ++ bs) pre.length)).apply _ = _
  rw [f2_counterTape_read]
  unfold f2_counterBump
  by_cases h : bs.head? = some true <;> simp only [h, ↓reduceIte]
  all_goals
    apply Cfg.ext
    · rfl
    · exact moveInputPos_zero p
    · funext j; exact f2_counterTape_write pre bs _
    · funext j; simp [Action.apply, f2_counterCfg, sub_eq_add_neg]
    · rfl

/-- A carry flips precisely the initial true bits, then writes the final true bit.
**Proof sketch.** Induct on the suffix. The empty suffix and a leading false bit
finish in one step. A leading true bit is replaced by false and included in the
prefix before invoking the induction hypothesis on the tail. -/
private lemma f2_counter_carry (x : List Bool) (p : Fin (x.length + 2))
    (bs : List Bool) : ∀ pre : List Bool,
    f2_counterTM.tm.runFrom (f2_counterCfg x 1 p pre.length (pre ++ bs) [])
        (f2_counterCarry bs + 1) =
      f2_counterCfg x 2 p ((pre.length : ℤ) + f2_counterCarry bs - 1)
        (pre ++ f2_counterInc bs) [] := by
  induction bs with
  | nil =>
    intro pre
    simp only [f2_counterCarry, MultiTapeTM.runFrom_succ_eq_step,
      MultiTapeTM.runFrom_zero, f2_counter_carry_step]
    simp [f2_counterInc]
  | cons b bs ih =>
    intro pre
    cases b with
    | false =>
      simp only [f2_counterCarry, MultiTapeTM.runFrom_succ_eq_step,
        MultiTapeTM.runFrom_zero, f2_counter_carry_step]
      simp [f2_counterInc]
    | true =>
      simp only [f2_counterCarry, MultiTapeTM.runFrom_succ_eq_step, f2_counter_carry_step,
        List.head?_cons, List.tail_cons, ↓reduceIte]
      have h := ih (pre ++ [false])
      rw [MultiTapeTM.runFrom_succ_eq_step] at h
      simpa [f2_counterInc, List.append_assoc, Nat.cast_add, Nat.cast_one,
        add_assoc, add_comm, add_left_comm] using h

/-- Rewind crosses the written prefix, detects the untouched blank at `-1`, and
returns to cell zero in the count state.
**Proof sketch.** Induct on the number of written cells still to cross.
Each bit causes one left move; at `-1` one right move ends the rewind. -/
private lemma f2_counter_rewind (x : List Bool) (p : Fin (x.length + 2))
    (bs : List Bool) : ∀ j (_hj : j ≤ bs.length),
    f2_counterTM.tm.runFrom (f2_counterCfg x 2 p ((j : ℤ) - 1) bs []) (j + 1) =
      f2_counterCfg x 0 p 0 bs [] := by
  intro j
  induction j with
  | zero =>
    intro hj
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    apply Cfg.ext <;>
      simp [MultiTapeTM.step, f2_counterTM, f2_counterCfg, Cfg.workTapeSymbols,
        f2_counterTape, Action.apply]
  | succ j ih =>
    intro hj
    have hw : (f2_counterCfg x 2 p (j : ℤ) bs []).workTapeSymbols 0 = some bs[j] := by
      simp only [f2_counterCfg, Cfg.workTapeSymbols, f2_counterTape,
        if_neg (by omega : ¬(j : ℤ) < 0), Int.toNat_natCast]
      exact List.getElem?_eq_getElem (by omega)
    have hs : f2_counterTM.tm.step (f2_counterCfg x 2 p (j : ℤ) bs []) =
        f2_counterCfg x 2 p ((j : ℤ) - 1) bs [] := by
      unfold MultiTapeTM.step
      change (f2_counterTM.tm.tr (2 : Fin 4) _ _).apply _ = _
      simp only [f2_counterTM, show (2 : Fin 4) ≠ 0 from by decide,
        show (2 : Fin 4) ≠ 1 from by decide, ↓reduceIte, hw]
      apply Cfg.ext
      · rfl
      · exact moveInputPos_zero p
      · rfl
      · funext k; simp [Action.apply, f2_counterCfg, sub_eq_add_neg]
      · rfl
    have he : ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) := by omega
    rw [he, MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- The first carry transition also consumes exactly one input symbol. -/
private lemma f2_counter_start (x : List Bool) (i : ℕ) (hi : i < x.length) (bs : List Bool) :
    f2_counterTM.tm.step (f2_counterCfg x 0 ⟨i + 1, by omega⟩ 0 bs []) =
      f2_counterTM.tm.step (f2_counterCfg x 1 ⟨i + 2, by omega⟩ 0 bs []) := by
  have hs : (f2_counterCfg x 0 ⟨i + 1, by omega⟩ 0 bs []).inputSymbol = some x[i] :=
    inputSymbolInner i (by simp only [f2_counterCfg]; omega) hi
  unfold MultiTapeTM.step
  change (f2_counterTM.tm.tr (0 : Fin 4) _ _).apply _ =
    (f2_counterTM.tm.tr (1 : Fin 4) _ _).apply _
  rw [hs]
  simp only [f2_counterTM, show (1 : Fin 4) ≠ 0 from by decide, ↓reduceIte]
  change (f2_counterBump .pos (f2_counterTape bs 0)).apply _ =
    (f2_counterBump .zero (f2_counterTape bs 0)).apply _
  unfold f2_counterBump
  by_cases h : f2_counterTape bs 0 = some true <;> simp only [h, ↓reduceIte]
  all_goals
    apply Cfg.ext
    · rfl
    · apply Fin.ext
      change (moveInputPos (⟨i + 1, by omega⟩ : Fin (x.length + 2)) .pos).val =
        (moveInputPos (⟨i + 2, by omega⟩ : Fin (x.length + 2)) 0).val
      rw [moveInputPos_zero, moveInputPos_pos_of_ne_right _ (by simp; omega)]
    · rfl
    · rfl
    · rfl

/-- One complete increment takes twice the carry length plus two transitions.
**Proof sketch.** The count transition is the first carry transition, with the
input advanced once. The carry uses `r + 1` steps and leaves the head at `r - 1`;
the rewind uses another `r + 1` steps and leaves the incremented word intact. -/
private lemma f2_counter_increment (x : List Bool) (i : ℕ) (hi : i < x.length)
    (bs : List Bool) :
    f2_counterTM.tm.runFrom (f2_counterCfg x 0 ⟨i + 1, by omega⟩ 0 bs [])
        (2 * f2_counterCarry bs + 2) =
      f2_counterCfg x 0 ⟨i + 2, by omega⟩ 0 (f2_counterInc bs) [] := by
  have hc : f2_counterTM.tm.runFrom (f2_counterCfg x 0 ⟨i + 1, by omega⟩ 0 bs [])
      (f2_counterCarry bs + 1) =
      f2_counterCfg x 2 ⟨i + 2, by omega⟩ ((f2_counterCarry bs : ℤ) - 1) (f2_counterInc bs) [] := by
    rw [MultiTapeTM.runFrom_succ_eq_step, f2_counter_start x i hi,
      ← MultiTapeTM.runFrom_succ_eq_step]
    simpa only [List.length_nil, Nat.cast_zero, zero_add, List.nil_append] using
      f2_counter_carry x ⟨i + 2, by omega⟩ bs []
  rw [show 2 * f2_counterCarry bs + 2 = (f2_counterCarry bs + 1) + (f2_counterCarry bs + 1) by omega,
    MultiTapeTM.runFrom_add, hc]
  exact f2_counter_rewind x ⟨i + 2, by omega⟩ (f2_counterInc bs) (f2_counterCarry bs)
    (f2_counterInc_length bs).2

/-- The counting invariant carries a nonnegative potential of twice the popcount.
**Proof sketch.** Initially both elapsed time and potential are zero. An increment
with `r` cleared bits costs `2r + 2` steps and changes the potential by `2 - 2r`.
Thus elapsed time plus potential increases by exactly four per input symbol.
The semantic invariant records the exact canonical binary word and head positions. -/
private lemma f2_counter_count (x : List Bool) : ∀ i (hi : i ≤ x.length),
    ∃ t, t + 2 * i.bits.count true ≤ 4 * i ∧
      f2_counterTM.tm.runFrom (f2_counterTM.tm.initCfg x) t =
        f2_counterCfg x 0 ⟨i + 1, by omega⟩ 0 i.bits [] := by
  intro i
  induction i with
  | zero =>
    intro hi
    refine ⟨0, by simp, ?_⟩
    apply Cfg.ext
    · rfl
    · rfl
    · funext j z
      simp [MultiTapeTM.initCfg, f2_counterCfg, f2_counterTape]
    · rfl
    · rfl
  | succ i ih =>
    intro hi
    obtain ⟨t, ht, hc⟩ := ih (by omega)
    refine ⟨t + 2 * f2_counterCarry i.bits + 2, ?_, ?_⟩
    · have hp := f2_counterInc_potential i.bits
      rw [f2_counterInc_bits] at hp
      omega
    · rw [show t + 2 * f2_counterCarry i.bits + 2 = t + (2 * f2_counterCarry i.bits + 2) by omega,
        MultiTapeTM.runFrom_add, hc, f2_counter_increment x i (by omega), f2_counterInc_bits]

/-- The emit phase appends exactly the stored prefix, one bit per step.
**Proof sketch.** Induct on the emitted length, using the nonblank cell at each
index below the word length; the tape contents and input position never change. -/
private lemma f2_counter_emit_run (x : List Bool) (p : Fin (x.length + 2))
    (bs : List Bool) : ∀ i (_hi : i ≤ bs.length),
    f2_counterTM.tm.runFrom (f2_counterCfg x 3 p 0 bs []) i =
      f2_counterCfg x 3 p i bs (bs.take i) := by
  intro i
  induction i with
  | zero => intro hi; rfl
  | succ i ih =>
    intro hi
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hw : (f2_counterCfg x 3 p i bs (bs.take i)).workTapeSymbols 0 = some bs[i] := by
      simp only [f2_counterCfg, Cfg.workTapeSymbols, f2_counterTape,
        if_neg (by omega : ¬(i : ℤ) < 0), Int.toNat_natCast]
      exact List.getElem?_eq_getElem (by omega)
    unfold MultiTapeTM.step
    change (f2_counterTM.tm.tr (3 : Fin 4) _ _).apply _ = _
    simp only [f2_counterTM, show (3 : Fin 4) ≠ 0 from by decide,
      show (3 : Fin 4) ≠ 1 from by decide, show (3 : Fin 4) ≠ 2 from by decide,
      ↓reduceIte, hw]
    apply Cfg.ext
    · rfl
    · exact moveInputPos_zero p
    · rfl
    · funext j; simp [Action.apply, f2_counterCfg]
    · simp only [Action.apply, f2_counterCfg]
      rw [List.take_succ, List.getElem?_eq_getElem (by omega)]

/-- At the first blank after the stored word, emission halts without extra output. -/
private lemma f2_counter_emit (x : List Bool) (p : Fin (x.length + 2)) (bs : List Bool) :
    let c := f2_counterTM.tm.runFrom (f2_counterCfg x 3 p 0 bs []) (bs.length + 1)
    c.state = none ∧ c.output = bs := by
  have hw : (f2_counterCfg x 3 p bs.length bs (bs.take bs.length)).workTapeSymbols 0 =
      none := by
    simp only [f2_counterCfg, Cfg.workTapeSymbols, f2_counterTape,
      if_neg (by omega : ¬(bs.length : ℤ) < 0), Int.toNat_natCast]
    exact List.getElem?_eq_none (le_refl _)
  dsimp only
  rw [MultiTapeTM.runFrom_succ_eq_step', f2_counter_emit_run x p bs bs.length (le_refl _)]
  unfold MultiTapeTM.step
  change ((f2_counterTM.tm.tr (3 : Fin 4) _ _).apply _).state = none ∧ _
  simp only [f2_counterTM, show (3 : Fin 4) ≠ 0 from by decide,
    show (3 : Fin 4) ≠ 1 from by decide, show (3 : Fin 4) ≠ 2 from by decide,
    ↓reduceIte, hw]
  simp [Action.apply, f2_counterCfg]

/-- The direct variable-width counter outputs the input length in at most
five times one plus that length. Its complete time proof is copied from the
explicit counter construction in ClassP/TimeConstructible.lean; no existential
witness or sharp space property of timeConstructible_id is assumed. -/
private lemma f2_counter_computes : f2_counterTM.ComputesFunInTime
    (fun x => Nat.bits x.length) (fun n => 5 * (n + 1)) := by
  intro x
  obtain ⟨t, ht, hc⟩ := f2_counter_count x x.length (le_refl _)
  have hs : f2_counterTM.tm.step
      (f2_counterCfg x 0 ⟨x.length + 1, by omega⟩ 0 x.length.bits []) =
      f2_counterCfg x 3 ⟨x.length + 1, by omega⟩ 0 x.length.bits [] := by
    have hin : (f2_counterCfg x 0 ⟨x.length + 1, by omega⟩ 0 x.length.bits []).inputSymbol =
        none := by simp [Cfg.inputSymbol, f2_counterCfg]
    unfold MultiTapeTM.step
    change (f2_counterTM.tm.tr (0 : Fin 4) _ _).apply _ = _
    rw [hin]
    apply Cfg.ext <;> simp [f2_counterTM, Action.apply, f2_counterCfg]
  have hstart : f2_counterTM.tm.runFrom (f2_counterTM.tm.initCfg x) (t + 1) =
      f2_counterCfg x 3 ⟨x.length + 1, by omega⟩ 0 x.length.bits [] := by
    rw [MultiTapeTM.runFrom_succ_eq_step', hc, hs]
  have he := f2_counter_emit x ⟨x.length + 1, by omega⟩ x.length.bits
  have hbase : f2_counterTM.ComputesInTime x x.length.bits
      ((t + 1) + (x.length.bits.length + 1)) := by
    refine ⟨_, ?_, ?_, rfl⟩
    · rw [MultiTapeTM.runFrom_add, hstart]; exact he.1
    · rw [MultiTapeTM.runFrom_add, hstart]; exact he.2
  apply hbase.mono
  have hl := Turing.length_bits_le_self x.length
  change (t + 1) + (x.length.bits.length + 1) ≤ 5 * (x.length + 1)
  omega

/-- The counting invariant also covers every suspended increment's head
trajectory. Each increment returns to the origin, and its carry length is
bounded by the final input length's binary width.
**Proof sketch.** Reuse the exact `2*carry+2` increment ledger and popcount
potential. Split each prefix at the preceding return; in the current increment
apply the unit-step trajectory bound from the origin. Binary width is monotone. -/
private lemma f2_counter_count_space (x : List Bool) : ∀ i (hi : i ≤ x.length),
    ∃ t, t + 2 * i.bits.count true ≤ 4 * i ∧
      f2_counterTM.tm.runFrom (f2_counterTM.tm.initCfg x) t =
        f2_counterCfg x 0 ⟨i + 1, by omega⟩ 0 i.bits [] ∧
      ∀ u ≤ t, ∀ j : Fin 1,
        -(2 * (Nat.size x.length + 1) : ℤ) ≤
          (f2_counterTM.tm.runFrom (f2_counterTM.tm.initCfg x) u).workTapePos j ∧
        (f2_counterTM.tm.runFrom (f2_counterTM.tm.initCfg x) u).workTapePos j ≤
          (2 * (Nat.size x.length + 1) : ℤ) := by
  intro i
  induction i with
  | zero =>
    intro hi
    refine ⟨0, by simp, ?_, ?_⟩
    · apply Cfg.ext
      · rfl
      · rfl
      · funext j z
        simp [MultiTapeTM.initCfg, f2_counterCfg, f2_counterTape]
      · rfl
      · rfl
    · intro u hu j
      have : u = 0 := by omega
      subst u
      simp [MultiTapeTM.initCfg, Cfg.init]
      omega
  | succ i ih =>
    intro hi
    obtain ⟨t, ht, hc, hb⟩ := ih (by omega)
    refine ⟨t + (2 * f2_counterCarry i.bits + 2), ?_, ?_, ?_⟩
    · have hp := f2_counterInc_potential i.bits
      rw [f2_counterInc_bits] at hp
      omega
    · rw [MultiTapeTM.runFrom_add, hc,
        f2_counter_increment x i (by omega), f2_counterInc_bits]
    · intro u hu j
      by_cases hut : u ≤ t
      · exact hb u hut j
      · rw [show u = t + (u - t) by omega, MultiTapeTM.runFrom_add, hc]
        have hp := f2_head_steps f2_counterTM.tm
          (f2_counterCfg x 0 ⟨i + 1, by omega⟩ 0 i.bits []) (u - t) j
        have hcarry := (f2_counterInc_length i.bits).2
        rw [f2_counterInc_bits, Nat.size_eq_bits_len] at hcarry
        have hwidth := Nat.size_le_size hi
        change 0 - ((u - t : ℕ) : ℤ) ≤ _ ∧ _ ≤ 0 + ((u - t : ℕ) : ℤ) at hp
        constructor <;> omega

/-- All prefixes of the direct counter, including its stationary halted tail,
fit a fixed interval whose radius is twice one plus the final binary width.
Counting rounds return their heads to zero; final emission traverses just the
stored binary word. -/
private lemma f2_counter_heads (x : List Bool) (u : ℕ) (j : Fin 1) :
    -(2 * (Nat.size x.length + 1) : ℤ) ≤
      (f2_counterTM.tm.runFrom (f2_counterTM.tm.initCfg x) u).workTapePos j ∧
    (f2_counterTM.tm.runFrom (f2_counterTM.tm.initCfg x) u).workTapePos j ≤
      (2 * (Nat.size x.length + 1) : ℤ) := by
  obtain ⟨t, _, hc, hb⟩ := f2_counter_count_space x x.length (le_refl _)
  let c := f2_counterCfg x 3 ⟨x.length + 1, by omega⟩ 0 x.length.bits []
  have hs : f2_counterTM.tm.step
      (f2_counterCfg x 0 ⟨x.length + 1, by omega⟩ 0 x.length.bits []) = c := by
    have hin : (f2_counterCfg x 0 ⟨x.length + 1, by omega⟩ 0 x.length.bits []).inputSymbol =
        none := by simp [Cfg.inputSymbol, f2_counterCfg]
    unfold MultiTapeTM.step
    change (f2_counterTM.tm.tr (0 : Fin 4) _ _).apply _ = _
    rw [hin]
    apply Cfg.ext <;> simp [c, f2_counterTM, Action.apply, f2_counterCfg]
  have hstart : f2_counterTM.tm.runFrom (f2_counterTM.tm.initCfg x) (t + 1) = c := by
    rw [MultiTapeTM.runFrom_succ_eq_step', hc, hs]
  let T := t + 1 + (x.length.bits.length + 1)
  have hhalt : (f2_counterTM.tm.runFrom (f2_counterTM.tm.initCfg x) T).state = none := by
    rw [show T = (t + 1) + (x.length.bits.length + 1) from rfl,
      MultiTapeTM.runFrom_add, hstart]
    exact (f2_counter_emit x ⟨x.length + 1, by omega⟩ x.length.bits).1
  have hpre (v : ℕ) (hv : v ≤ T) :
      -(2 * (Nat.size x.length + 1) : ℤ) ≤
        (f2_counterTM.tm.runFrom (f2_counterTM.tm.initCfg x) v).workTapePos j ∧
      (f2_counterTM.tm.runFrom (f2_counterTM.tm.initCfg x) v).workTapePos j ≤
        (2 * (Nat.size x.length + 1) : ℤ) := by
    by_cases hvt : v ≤ t
    · exact hb v hvt j
    · rw [show v = (t + 1) + (v - (t + 1)) by omega,
        MultiTapeTM.runFrom_add, hstart]
      have hp := f2_head_steps f2_counterTM.tm c (v - (t + 1)) j
      change 0 - ((v - (t + 1) : ℕ) : ℤ) ≤ _ ∧ _ ≤ 0 + ((v - (t + 1) : ℕ) : ℤ) at hp
      have hlen := Nat.size_eq_bits_len x.length
      dsimp only [T] at hv
      constructor <;> omega
  by_cases hu : u ≤ T
  · exact hpre u hu
  · rw [show u = T + (u - T) by omega, MultiTapeTM.runFrom_add,
      MultiTapeTM.runFrom_of_halt _ hhalt]
    exact hpre T (le_refl _)

/-- Taking the cardinality of the counter's inclusive trajectory interval
and summing over its single tape gives a logarithmic all-time space bound. -/
private lemma f2_counter_space (x : List Bool) (t : ℕ) :
    f2_counterTM.tm.spaceUsed (f2_counterTM.tm.initCfg x) t ≤
      5 * (Nat.size x.length + 1) := by
  have hcard (j : Fin 1) :
      f2_counterTM.tm.spaceUsedByTape (f2_counterTM.tm.initCfg x) t j ≤
        5 * (Nat.size x.length + 1) := by
    have hsub : f2_counterTM.tm.visitedByTapeHead (f2_counterTM.tm.initCfg x) t j ⊆
        Finset.Icc (-(2 * (Nat.size x.length + 1) : ℤ))
          (2 * (Nat.size x.length + 1) : ℤ) := by
      intro z hz
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_Icc.mpr (f2_counter_heads x u j)
    exact (Finset.card_le_card hsub).trans (by rw [Int.card_Icc]; omega)
  simpa [MultiTapeTM.spaceUsed] using hcard 0

/-- Administrative actions for the captured length checker move only the
input and final (countdown) head. No tape is written. -/
private def f2_lenAction (M : FinTM Bool) (m d : SignType) (b : Option Bool)
    (q : Option (M.State ⊕ (Fin 4 ⊕ Option Bool))) :
    Action (M.k + 1) Bool (M.State ⊕ (Fin 4 ⊕ Option Bool)) :=
  ⟨m, fun i => (none, if i.val < M.k then 0 else d), b, q⟩

/-- Capture a total generator, rewind the physical input, validate its pair
syntax, then compare the suffix length with the captured word's length.
Only the final comparison or rejection transition emits a verdict. -/
private def f2_pairCountTM (M : FinTM Bool) : FinTM Bool where
  k := M.k + 1
  State := M.State ⊕ (Fin 4 ⊕ Option Bool)
  tm := {
    q₀ := .inl M.tm.q₀
    tr := fun q inp work => match q with
      | .inl s => captureAction Sum.inl (.inr (.inl 0))
          (M.tm.tr s inp fun i => work i.castSucc)
      | .inr (.inl q) => match q.val with
        | 0 => f2_lenAction M 0 .neg none (some (.inr (.inl 1)))
        | 1 => controlAction .neg (some (.inr (.inl 2)))
        | 2 => match inp with
          | some _ => controlAction .neg (some (.inr (.inl 2)))
          | none => controlAction .pos (some (.inr (.inr none)))
        | _ => match inp with
          | none => f2_lenAction M 0 0 (some true) none
          | some _ => match work (Fin.last M.k) with
            | none => f2_lenAction M 0 0 (some false) none
            | some _ => f2_lenAction M .pos .neg none (some (.inr (.inl 3)))
      | .inr (.inr none) => match inp with
        | none => f2_lenAction M 0 0 (some false) none
        | some b => f2_lenAction M .pos 0 none (some (.inr (.inr (some b))))
      | .inr (.inr (some b)) => match inp with
        | none => f2_lenAction M 0 0 (some false) none
        | some d => if b = d then f2_lenAction M .pos 0 none (some (.inr (.inr none)))
          else if b then f2_lenAction M 0 0 (some false) none
          else f2_lenAction M .pos 0 none (some (.inr (.inl 3))) }

/-- Checker configurations retain the completed generator bank and its
captured output; `r` is the number of still available countdown cells. -/
private def f2_lenCfg (M : FinTM Bool) {x : List Bool} (c : Cfg M.k Bool M.State x)
    (q : Option (f2_pairCountTM M).State) (i : ℕ) (hi : i ≤ x.length) (r : ℕ) :
    Cfg (M.k + 1) Bool (f2_pairCountTM M).State x :=
  { captureCfg (fun s : M.State => (Sum.inl s : (f2_pairCountTM M).State))
      (.inr (.inl 0)) [] [] c with
    state := q
    inputPos := ⟨i + 1, by omega⟩
    workTapePos := fun j => if h : j.val < M.k then c.workTapePos ⟨j, h⟩
      else (r : ℤ) - 1 }

/-- The checker's input read is independent of the saved generator bank. -/
private lemma f2_lenCfg_read (M : FinTM Bool) {x : List Bool} (c : Cfg M.k Bool M.State x)
    (q : Option (f2_pairCountTM M).State) (i : ℕ) (hi : i ≤ x.length) (r : ℕ) :
    (f2_lenCfg M c q i hi r).inputSymbol = x[i]? :=
  inputSymbol_at _ i hi rfl

/-- A stationary or forward administrative action preserves all work tapes;
its last-head movement subtracts one precisely when consuming a cell. -/
private lemma f2_lenAction_apply (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (q q' : Option (f2_pairCountTM M).State)
    (i j r s : ℕ) (hi : i ≤ x.length) (hj : j ≤ x.length)
    (m d : SignType) (b : Option Bool)
    (hm : moveInputPos (⟨i + 1, by omega⟩ : Fin (x.length + 2)) m = ⟨j + 1, by omega⟩)
    (hd : (r : ℤ) - 1 + d.cast = (s : ℤ) - 1) :
    (f2_lenAction M m d b q').apply (f2_lenCfg M c q i hi r) =
      {f2_lenCfg M c q' j hj s with output := b.toList} := by
  refine Cfg.ext rfl hm ?_ ?_ rfl
  · rfl
  · funext k
    by_cases hk : k.val < M.k
    · simp [f2_lenAction, f2_lenCfg, Action.apply, hk]
    · simpa [f2_lenAction, f2_lenCfg, Action.apply, hk] using hd

/-- Suffix comparison consumes one captured cell per input bit and emits one
verdict at termination. Empty suffixes succeed even with an empty counter.
**Proof sketch.** Induct on the suffix. A zero counter rejects a nonempty
suffix immediately; otherwise one silent step decrements both lengths. -/
private lemma f2_lenSuffix_run (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (rest : List Bool) :
    ∀ pre (hx : x = pre ++ rest) r, r ≤ c.output.length →
    ∃ t ≤ rest.length + 1,
      ((f2_pairCountTM M).tm.runFrom
        (f2_lenCfg M c (some (.inr (.inl 3))) pre.length (by simp [hx]) r) t).state = none ∧
      ((f2_pairCountTM M).tm.runFrom
        (f2_lenCfg M c (some (.inr (.inl 3))) pre.length (by simp [hx]) r) t).output =
          [decide (rest.length ≤ r)] := by
  induction rest with
  | nil =>
    intro pre hx r hr
    refine ⟨1, by simp, ?_⟩
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change (((f2_pairCountTM M).tm.tr (.inr (.inl 3)) _ _).apply _).state = none ∧ _
    rw [f2_lenCfg_read]
    simp [hx, f2_pairCountTM, f2_lenAction, f2_lenCfg, captureCfg, Action.apply]
  | cons b rest ih =>
    intro pre hx r hr
    cases r with
    | zero =>
      refine ⟨1, by simp, ?_⟩
      simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
      unfold MultiTapeTM.step
      change (((f2_pairCountTM M).tm.tr (.inr (.inl 3)) _ _).apply _).state = none ∧ _
      rw [f2_lenCfg_read]
      simp [hx, f2_pairCountTM, f2_lenAction, f2_lenCfg, captureCfg, Cfg.workTapeSymbols,
        bufferTape_left, Action.apply]
    | succ r =>
      have hs : (f2_pairCountTM M).tm.step
          (f2_lenCfg M c (some (.inr (.inl 3))) pre.length (by simp [hx]) (r + 1)) =
          f2_lenCfg M c (some (.inr (.inl 3))) (pre.length + 1) (by simp [hx]) r := by
        unfold MultiTapeTM.step
        change ((f2_pairCountTM M).tm.tr (.inr (.inl 3)) _ _).apply _ = _
        rw [f2_lenCfg_read]
        have hin : x[pre.length]? = some b := by simp [hx]
        have hw : (f2_lenCfg M c (some (.inr (.inl 3))) pre.length
            (by simp [hx]) (r + 1)).workTapeSymbols (Fin.last M.k) =
              some (c.output[r]'(by omega)) := by
          simp [f2_lenCfg, captureCfg, Cfg.workTapeSymbols, bufferTape,
            List.getElem?_eq_getElem (by omega : r < c.output.length)]
        simp only [f2_pairCountTM, hin, hw]
        exact f2_lenAction_apply M c _ _ pre.length (pre.length + 1) (r + 1) r
          (by simp [hx]) (by simp [hx]) .pos .neg none
          (moveInputPos_pos_of_ne_right _ (by simp [hx])) (by simp [SignType.cast]; omega)
      obtain ⟨t, ht, hh, ho⟩ := ih (pre ++ [b]) (by simpa [List.append_assoc] using hx)
        r (by omega)
      refine ⟨1 + t, by simp only [List.length_cons]; omega, ?_⟩
      rw [MultiTapeTM.runFrom_add]
      simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
      rw [hs]
      simpa using And.intro hh ho

/-- The first half of an aligned block changes only finite control and the
input position; countdown cells remain untouched during validation. -/
private lemma f2_lenParse_first (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (pre rest : List Bool) (b : Bool) (r : ℕ)
    (hx : x = pre ++ b :: rest) :
    (f2_pairCountTM M).tm.step
      (f2_lenCfg M c (some (.inr (.inr none))) pre.length (by simp [hx]) r) =
      f2_lenCfg M c (some (.inr (.inr (some b)))) (pre.length + 1) (by simp [hx]) r := by
  unfold MultiTapeTM.step
  change ((f2_pairCountTM M).tm.tr (.inr (.inr none)) _ _).apply _ = _
  rw [f2_lenCfg_read]
  have hin : x[pre.length]? = some b := by simp [hx]
  simp only [f2_pairCountTM, hin]
  exact f2_lenAction_apply M c _ _ pre.length (pre.length + 1) r r
    (by simp [hx]) (by simp [hx]) .pos 0 none
    (moveInputPos_pos_of_ne_right _ (by simp [hx])) (by simp [SignType.cast])

/-- Two parser steps either advance over a doubled bit, enter the suffix
comparison at `01`, or reject `10`. Nothing is emitted on a valid block. -/
private lemma f2_lenParse_block (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (pre rest : List Bool) (b d : Bool) (r : ℕ)
    (hx : x = pre ++ b :: d :: rest) :
    (f2_pairCountTM M).tm.runFrom
      (f2_lenCfg M c (some (.inr (.inr none))) pre.length (by simp [hx]) r) 2 =
      if b = d then f2_lenCfg M c (some (.inr (.inr none)))
          (pre.length + 2) (by simp [hx]) r
      else if b then {f2_lenCfg M c none (pre.length + 1) (by simp [hx]) r with output := [false]}
      else f2_lenCfg M c (some (.inr (.inl 3))) (pre.length + 2) (by simp [hx]) r := by
  change (f2_pairCountTM M).tm.step ((f2_pairCountTM M).tm.step _) = _
  rw [f2_lenParse_first M c pre (d :: rest) b r hx]
  unfold MultiTapeTM.step
  change ((f2_pairCountTM M).tm.tr (.inr (.inr (some b))) _ _).apply _ = _
  rw [f2_lenCfg_read]
  have hin : x[pre.length + 1]? = some d := by simp [hx]
  rw [hin]
  have hm : moveInputPos (⟨pre.length + 1 + 1, by simp [hx]⟩ : Fin (x.length + 2)) .pos =
      ⟨pre.length + 2 + 1, by simp [hx]; omega⟩ :=
    moveInputPos_pos_of_ne_right _ (by simp [hx])
  cases b <;> cases d <;>
    simp only [f2_pairCountTM, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
  all_goals first
    | exact f2_lenAction_apply M c _ _ (pre.length + 1) (pre.length + 2) r r
        (by simp [hx]) (by simp [hx]) .pos 0 none hm (by simp [SignType.cast])
    | exact f2_lenAction_apply M c _ _ (pre.length + 1) (pre.length + 1) r r
        (by simp [hx]) (by simp [hx]) 0 0 (some false)
        (moveInputPos_zero _) (by simp [SignType.cast])

/-- Aligned validation followed by countdown comparison decides the payload
bound in at most one more than the unread input length.
**Proof sketch.** Induct over two-bit blocks, using the existing parser's
same grammar and induction pattern. Equal-bit blocks preserve the counter;
`01` invokes suffix comparison; malformed endings and `10` reject. -/
private lemma f2_lenParse_run (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (rest : List Bool) :
    ∀ pre (hx : x = pre ++ rest) r, r ≤ c.output.length →
    ∃ t ≤ rest.length + 1,
      ((f2_pairCountTM M).tm.runFrom
        (f2_lenCfg M c (some (.inr (.inr none))) pre.length (by simp [hx]) r) t).state = none ∧
      ((f2_pairCountTM M).tm.runFrom
        (f2_lenCfg M c (some (.inr (.inr none))) pre.length (by simp [hx]) r) t).output =
          [match pairDecode rest with
            | some (_, b) => decide (b.length ≤ r)
            | none => false] := by
  induction rest using List.twoStepInduction with
  | nil =>
    intro pre hx r hr
    refine ⟨1, by simp, ?_⟩
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change (((f2_pairCountTM M).tm.tr (.inr (.inr none)) _ _).apply _).state = none ∧ _
    rw [f2_lenCfg_read]
    simp [hx, f2_pairCountTM, f2_lenAction, f2_lenCfg, captureCfg, Action.apply, pairDecode]
  | singleton b =>
    intro pre hx r hr
    refine ⟨2, by simp, ?_⟩
    change ((f2_pairCountTM M).tm.step ((f2_pairCountTM M).tm.step _)).state = none ∧
      ((f2_pairCountTM M).tm.step ((f2_pairCountTM M).tm.step _)).output = _
    rw [f2_lenParse_first M c pre [] b r hx]
    unfold MultiTapeTM.step
    change (((f2_pairCountTM M).tm.tr (.inr (.inr (some b))) _ _).apply _).state = none ∧ _
    rw [f2_lenCfg_read]
    cases b <;> simp [hx, f2_pairCountTM, f2_lenAction, f2_lenCfg, captureCfg, Action.apply, pairDecode]
  | cons_cons b d rest ih _ =>
    intro pre hx r hr
    by_cases h : b = d
    · subst d
      obtain ⟨t, ht, hs, ho⟩ := ih (pre ++ [b, b])
        (by simpa [List.append_assoc] using hx) r hr
      refine ⟨2 + t, by simp only [List.length_cons] at *; omega, ?_⟩
      rw [MultiTapeTM.runFrom_add, f2_lenParse_block M c pre rest b b r hx, if_pos rfl]
      simp only [List.length_append, List.length_cons, List.length_nil] at hs ho
      refine ⟨hs, ?_⟩
      cases b <;> cases hd : pairDecode rest with
        | none => simpa [pairDecode, hd] using ho
        | some p => cases p; simpa [pairDecode, hd] using ho
    · cases b <;> cases d
      · exact False.elim (h rfl)
      · obtain ⟨t, ht, hs, ho⟩ := f2_lenSuffix_run M c rest (pre ++ [false, true])
          (by simpa [List.append_assoc] using hx) r hr
        refine ⟨2 + t, by simp only [List.length_cons]; omega, ?_⟩
        rw [MultiTapeTM.runFrom_add, f2_lenParse_block M c pre rest false true r hx]
        simp only [Bool.false_eq_true, ↓reduceIte]
        simp only [List.length_append, List.length_cons, List.length_nil] at hs ho
        exact ⟨hs, by simpa [pairDecode] using ho⟩
      · refine ⟨2, by simp, ?_⟩
        rw [f2_lenParse_block M c pre rest true false r hx]
        simp [f2_lenCfg, pairDecode]
      · exact False.elim (h rfl)

/-- Quantitative input rewind, adapted from the wrapper controller's proved
`timed_rewind` pattern using the public `rewind_scan` interface.
**Proof sketch.** One mandatory left move is followed by exactly the new
position plus one scan steps. Work tapes and output are preserved. -/
private lemma f2_catalogRewind {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (start scan : S) (dest : Option S)
    (hstart : ∀ inp work, tm.tr start inp work = controlAction .neg (some scan))
    (hscan : ∀ inp work, tm.tr scan inp work = match inp with
      | some _ => controlAction .neg (some scan)
      | none => controlAction .pos dest)
    (c : Cfg k Bool S x) (hs : c.state = some start) :
    ∃ r ≤ c.inputPos.val + 2,
      tm.runFrom c r = {c with state := dest, inputPos := 1} := by
  have hstep : tm.step c =
      {c with state := some scan, inputPos := moveInputPos c.inputPos .neg} := by
    unfold MultiTapeTM.step
    rw [hs]
    dsimp only
    rw [hstart, controlAction_apply]
  have hp : (moveInputPos c.inputPos .neg).val ≤ x.length := by
    rw [moveInputPos_neg_val]
    have := c.inputPos.isLt
    omega
  refine ⟨1 + ((moveInputPos c.inputPos .neg).val + 1), ?_, ?_⟩
  · rw [moveInputPos_neg_val]; omega
  · rw [MultiTapeTM.runFrom_add]
    change tm.runFrom (tm.step c) _ = _
    rw [hstep, rewind_scan tm scan dest hscan _ rfl hp]

/-- A completed generator is captured without physical output, then its
last cell and the first physical input cell are exposed for comparison.
**Proof sketch.** Use the least source halting time to discharge `capture_run`'s
liveness guard. One step moves the capture head left; quantitative rewind
restores the input head while preserving the completed generator bank. -/
private lemma f2_lenStart (M : FinTM Bool) (x w : List Bool) (T : ℕ)
    (hM : M.ComputesInTime x w T) :
    ∃ t ≤ T + x.length + 4, ∃ c : Cfg M.k Bool M.State x,
      c.output = w ∧
      (f2_pairCountTM M).tm.runFrom ((f2_pairCountTM M).tm.initCfg x) t =
        f2_lenCfg M c (some (.inr (.inr none))) 0 (by omega) c.output.length := by
  classical
  have hh : ∃ t, (M.tm.runFrom (M.tm.initCfg x) t).state = none :=
    ⟨T, ((computesInTime_iff _ _ _ _).mp hM).1⟩
  let t := Nat.find hh
  let c := M.tm.runFrom (M.tm.initCfg x) t
  have ht : t ≤ T := Nat.find_min' hh ((computesInTime_iff _ _ _ _).mp hM).1
  have hs : c.state = none := Nat.find_spec hh
  have hc : M.ComputesInTime x c.output t := (computesInTime_iff _ _ _ _).mpr ⟨hs, rfl⟩
  have ho : c.output = w := hc.output_unique hM
  let emb : M.State → (f2_pairCountTM M).State := Sum.inl
  let ret : (f2_pairCountTM M).State := .inr (.inl 0)
  have hinit : (f2_pairCountTM M).tm.initCfg x = captureCfg emb ret [] [] (M.tm.initCfg x) := by
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    · funext i; simp [captureCfg, MultiTapeTM.initCfg, Cfg.init]
    · funext i; simp [captureCfg, MultiTapeTM.initCfg, Cfg.init]
  have hcap : (f2_pairCountTM M).tm.runFrom ((f2_pairCountTM M).tm.initCfg x) t =
      captureCfg emb ret [] [] c := by
    rw [hinit]
    exact capture_run M.tm (f2_pairCountTM M).tm emb ret (fun _ _ _ => rfl)
      [] [] _ t (fun s hst => Nat.find_min hh hst)
  let ready : Cfg (M.k + 1) Bool (f2_pairCountTM M).State x :=
    {f2_lenCfg M c (some (.inr (.inl 1))) 0 (by omega) c.output.length with
      inputPos := c.inputPos}
  have hback : (f2_pairCountTM M).tm.step (captureCfg emb ret [] [] c) = ready := by
    have hstate : (captureCfg emb ret [] [] c).state = some ret := by simp [captureCfg, hs]
    simp only [MultiTapeTM.step, hstate]
    apply Cfg.ext
    · rfl
    · exact moveInputPos_zero _
    · rfl
    · funext i
      by_cases hi : i.val < M.k <;>
        simp [f2_pairCountTM, ret, f2_lenAction, Action.apply, captureCfg, ready, f2_lenCfg, hi,
          sub_eq_add_neg]
    · rfl
  obtain ⟨r, hrle, hr⟩ := f2_catalogRewind (f2_pairCountTM M).tm
    (.inr (.inl 1)) (.inr (.inl 2)) (some (.inr (.inr none)))
    (fun _ _ => rfl) (fun inp _ => by cases inp <;> rfl) ready rfl
  refine ⟨t + 1 + r, ?_, c, ho, ?_⟩
  · change r ≤ c.inputPos.val + 2 at hrle
    have := c.inputPos.isLt
    omega
  · rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add, hcap]
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    rw [hback, hr]
    rfl

/-- The captured checker compares a valid pair's payload with the length of
the generator's output, and rejects every malformed input.
**Proof sketch.** Compose the silent capture/rewind prefix with the aligned
parser and countdown ledger, then absorb the two linear scans. -/
private lemma f2_pairCount_computes {M : FinTM Bool} {g : List Bool → List Bool}
    {T : ℕ → ℕ} (hM : M.ComputesFunInTime g T) :
    (f2_pairCountTM M).ComputesFunInTime
      (fun x => [match pairDecode x with
        | some (_, b) => decide (b.length ≤ (g x).length)
        | none => false]) (fun n => T n + 2 * n + 5) := by
  intro x
  obtain ⟨t, ht, c, ho, hstart⟩ := f2_lenStart M x (g x) (T x.length) (hM x)
  obtain ⟨r, hr, hs, hout⟩ := f2_lenParse_run M c x [] rfl c.output.length (le_refl _)
  have hc : (f2_pairCountTM M).ComputesInTime x
      [match pairDecode x with
        | some (_, b) => decide (b.length ≤ (g x).length)
        | none => false] (t + r) := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_add, hstart]
    exact ⟨hs, by simpa only [ho] using hout⟩
  exact hc.mono (by dsimp only; omega)

/-- A successful aligned parse reconstructs the input's exact encoding.
**Proof sketch.** Induct over two-bit blocks: equal bits prepend one decoded
bit; the separator exposes the entire remaining suffix. -/
private lemma f2_catalogPair_inverse (x : List Bool) :
    ∀ a v, pairDecode x = some (a, v) → x = pairEncode a v := by
  induction x using List.twoStepInduction with
  | nil => intro a v h; simp [pairDecode] at h
  | singleton b => intro a v h; cases b <;> simp [pairDecode] at h
  | cons_cons b d rest ih _ =>
    intro a v h
    cases b <;> cases d
    · obtain ⟨p, hp, he⟩ := Option.map_eq_some_iff.mp h
      rcases p with ⟨u, w⟩
      cases he
      rw [ih u w hp]
      rfl
    · cases h; rfl
    · simp [pairDecode] at h
    · obtain ⟨p, hp, he⟩ := Option.map_eq_some_iff.mp h
      rcases p with ⟨u, w⟩
      cases he
      rw [ih u w hp]
      rfl

/-- Every all-time head position of a halted computation already occurs before
its time bound. Taking the image of that finite prefix gives at most `T+1`
cells per tape, including the initial cell.
**Proof sketch.** For a later time, split the run at `T` and use halt absorption;
for an earlier time use the same time index. Take cardinalities and sum. -/
private lemma f2_space_of_time {M : FinTM Bool} {x y : List Bool} {T : ℕ}
    (h : M.ComputesInTime x y T) (t : ℕ) :
    M.tm.spaceUsed (M.tm.initCfg x) t ≤ M.k * (T + 1) := by
  have hh := ((computesInTime_iff _ _ _ _).mp h).1
  have hsub (i : Fin M.k) :
      M.tm.visitedByTapeHead (M.tm.initCfg x) t i ⊆
        M.tm.visitedByTapeHead (M.tm.initCfg x) T i := by
    intro z hz
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hz
    by_cases hu : u ≤ T
    · exact Finset.mem_image.mpr ⟨u, Finset.mem_range.mpr (by omega), rfl⟩
    · have hr : M.tm.runFrom (M.tm.initCfg x) u =
          M.tm.runFrom (M.tm.initCfg x) T := by
        rw [show u = T + (u - T) by omega, MultiTapeTM.runFrom_add,
          MultiTapeTM.runFrom_of_halt _ hh]
      exact Finset.mem_image.mpr ⟨T, Finset.mem_range.mpr (by omega),
        congrArg (fun c => c.workTapePos i) hr.symm⟩
  calc
    _ ≤ ∑ _i : Fin M.k, (T + 1) := by
      apply Finset.sum_le_sum
      intro i _
      exact (Finset.card_le_card (hsub i)).trans (by
        unfold MultiTapeTM.visitedByTapeHead
        exact (Finset.card_image_le).trans (by rw [Finset.card_range]))
    _ = _ := by simp

/-- **P1 space row** (spec, fill pending — design §12 R3, decision 12.3;
annotates `Turing.FinTM.computesFunInTime_id`). The copy machine runs in
constant work-tape space: one witness does the whole job on its input and
output heads alone.

**Proof sketch.** The existing witness `idTM` has no work tapes, so every
`spaceUsed` value is `0`; re-exhibit it and join the audited time
contract with the constant bound. -/
theorem computesFunInTime_id_spaceUsed :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime id (fun n => c * (n + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c := by
  refine ⟨f2_idTM, 1, ?_, ?_⟩
  · intro x
    obtain ⟨hstate, hpos, hout⟩ := f2_idTM_run x x.length (le_refl _)
    have h0 : (f2_idTM.tm.runFrom (f2_idTM.tm.initCfg x) x.length).inputPos ≠ 0 := by
      intro h
      rw [h] at hpos
      simp at hpos
    have hsym : (f2_idTM.tm.runFrom (f2_idTM.tm.initCfg x) x.length).inputSymbol = none := by
      unfold Cfg.inputSymbol
      rw [dif_neg h0, dif_pos (by omega)]
    have hrun1 : f2_idTM.tm.runFrom (f2_idTM.tm.initCfg x) (x.length + 1) =
        (f2_idTM.tm.tr () none
          ((f2_idTM.tm.runFrom (f2_idTM.tm.initCfg x) x.length).workTapeSymbols)).apply
          (f2_idTM.tm.runFrom (f2_idTM.tm.initCfg x) x.length) := by
      rw [MultiTapeTM.runFrom_succ_eq_step']
      unfold MultiTapeTM.step
      rw [hstate]
      dsimp only
      rw [hsym]
    have hbase : f2_idTM.ComputesInTime x x (x.length + 1) := by
      refine ⟨_, ?_, ?_, rfl⟩
      · rw [hrun1]
        simp [f2_idTM, Action.apply]
      · rw [hrun1]
        simp only [f2_idTM, Action.apply]
        rw [hout]
        simp
    exact hbase.mono (le_of_eq (one_mul _).symm)
  · intro x t
    rw [MultiTapeTM.spaceUsed_zero_tapes_eq_zero _ _ rfl]
    omega

/-- **P2 space row** (spec, fill pending — design §12 R3; annotates
`Turing.FinTM.computesFunInTime_const`). The fixed-word emission chain
runs in constant work-tape space.

**Proof sketch.** The existing witness `constTM w` is a zero-work-tape
emission chain, so `spaceUsed` is identically `0`. -/
theorem computesFunInTime_const_spaceUsed (w : List Bool) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun _ => w) (fun n => c * (n + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c := by
  refine ⟨f2_constTM w, w.length + 1, ?_, ?_⟩
  · intro x
    obtain ⟨hs, ho⟩ := emit_halts (f2_constTM w).tm w id (fun _ _ _ => rfl)
      ((f2_constTM w).tm.initCfg x) rfl
    have hbase : (f2_constTM w).ComputesInTime x w (w.length + 1) := by
      exact ⟨_, hs, by simpa only [MultiTapeTM.initCfg, Cfg.init, List.nil_append] using ho, rfl⟩
    exact hbase.mono (Nat.le_mul_of_pos_right _ (by omega))
  · intro x t
    rw [MultiTapeTM.spaceUsed_zero_tapes_eq_zero _ _ rfl]
    omega

/-- **P3 space row** (spec, fill pending — design §12 R3; annotates
`Turing.FinTM.computesFunInTime_prepend`). Prepending a fixed word runs
in constant work-tape space: an emission chain followed by the input
copy scan never moves a work head.

**Proof sketch.** The existing witness `catalogPrefixTM` has no work-tape
movement (head-movement count zero on every phase), so each visited set
is the origin singleton and the total is the tape count, a machine
constant absorbed into `c`. -/
theorem computesFunInTime_prepend_spaceUsed (w : List Bool) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => w ++ x) (fun n => c * (n + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c := by
  refine ⟨f2_catalogPrefixTM w, w.length + 1, ?_, ?_⟩
  · intro x
    apply (f2_catalogPrefixTM_computes w x).mono
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    omega
  · intro x t
    rw [MultiTapeTM.spaceUsed_zero_tapes_eq_zero _ _ rfl]
    omega

/-- **P4 space row** (spec, fill pending — design §12 R3; annotates
`Turing.FinTM.computesFunInTime_lengthBits`). The binary length counter
runs in logarithmic work-tape space: the counter word has `Nat.size n`
bits and the scan never leaves its interval (the sharp clause the
chapter-4 campaign consumes).

**Proof sketch.** The witness drives an in-place binary counter on one
work tape (the `Turing.incFixed` carry discipline): its head stays within
the counter interval `[-1, Nat.size n + 1]`, whose visit count the carry
head-movement bounds; constants absorb the boundary cells. -/
theorem computesFunInTime_lengthBits_spaceUsed :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => Nat.bits x.length)
        (fun n => c * (n + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c * (Nat.size x.length + 1) := by
  exact ⟨f2_counterTM, 5, f2_counter_computes, f2_counter_space⟩

/-- **P5 space row, unary clause** (spec, fill pending — design §12 R3;
annotates `Turing.FinTM.computesFunInTime_polyUnary`). The unary
polynomial generator runs in linear work-tape space: each of its `e`
nested loop tapes holds a unary counter of side `n + 1`.

**Proof sketch.** Head-movement count per loop tape: installed by one
input scan and bounded by the box side `n + 1`, revisited in place
across iterations — per-tape visited sets lie in `[-1, n + 1]`, and the
tape count depends only on `e`, absorbed into `c`. -/
theorem computesFunInTime_polyUnary_spaceUsed (C e : ℕ) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun x => List.replicate (C * (x.length + 1) ^ e) true)
        (fun n => c * (n + 1) ^ (e + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c * (x.length + 1) := by
  cases e with
  | zero =>
    obtain ⟨M, c, ht, hs⟩ := computesFunInTime_const_spaceUsed (List.replicate C true)
    refine ⟨M, c, by simpa using ht, ?_⟩
    intro x t
    exact (hs x t).trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
  | succ d =>
    refine ⟨f2_catalogPolyUnaryTM d C, C + 10 * (d + 1) + 4, ?_, ?_⟩
    · intro x
      apply (f2_catalogPoly_unary_computes d C x).mono
      apply Nat.mul_le_mul
      · omega
      · exact Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
    · intro x t
      exact (f2_poly_space d C x t).trans
        (Nat.mul_le_mul_right (x.length + 1) (by omega))

/-- **P5 space row, binary clause** (spec, fill pending — design §12 R3;
annotates `Turing.FinTM.computesFunInTime_polyBits`). The binary
polynomial evaluator runs in linear work-tape space: it is the unary
generator buffered into the length counter, and the buffer tape holds
the unary intermediate — the linear clause is the witness family's
honest bound (a logarithmic-space evaluator would be a new machine, out
of this increment's scope; recorded as a deviation from the sharpest
conceivable form).

**Proof sketch.** Split on the coefficient and exponent (round-1
finding 5 — the unqualified buffered-generator route fails at `C = 0`,
where the old generator still initializes length-`n + 1` unary banks
against a constant bound): for `C = 0`, and likewise for `e = 0`, the
witness is the constant-output family (zero work tapes, constant
space); for `C > 0` and `e > 0`, where `n + 1 ≤ C·(n+1)^e`, the buffered
composition's buffer holds the unary intermediate of length
`C·(n+1)^e`, the generator's banks are linear, and the counter is
logarithmic — all inside the stated value-linear bound. -/
theorem computesFunInTime_polyBits_spaceUsed (C e : ℕ) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => Nat.bits (C * (x.length + 1) ^ e))
        (fun n => c * (n + 1) ^ (e + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c * (C * (x.length + 1) ^ e + 1) := by
  by_cases hC : C = 0
  · subst C
    obtain ⟨M, c, ht, hs⟩ := computesFunInTime_const_spaceUsed (Nat.bits 0)
    refine ⟨M, c, ?_, ?_⟩
    · intro x
      simpa only [Nat.zero_mul] using (ht x).mono
        (Nat.mul_le_mul_left c (by
          simpa only [Nat.pow_one] using
            Nat.pow_le_pow_right (Nat.succ_pos x.length) (show 1 ≤ e + 1 by omega)))
    · simpa using hs
  · cases e with
    | zero =>
      obtain ⟨M, c, ht, hs⟩ := computesFunInTime_const_spaceUsed (Nat.bits C)
      refine ⟨M, c, by simpa using ht, ?_⟩
      intro x t
      simpa using (hs x t).trans (Nat.le_mul_of_pos_right c (Nat.succ_pos C))
    | succ d =>
      let A := C + 5 * (d + 1) + 4
      let K := A + 6 * C + 7
      let M := bufferedCompTM (f2_catalogPolyUnaryTM d C) f2_counterTM
      have ht : M.ComputesFunInTime (fun x => Nat.bits (C * (x.length + 1) ^ (d + 1)))
          (fun n => K * (n + 1) ^ (d + 1)) := by
        intro x
        have h := bufferedCompTM_computesInTime
          (f2_catalogPolyUnaryTM d C) f2_counterTM
          (f2_catalogPoly_unary_computes d C x)
          (f2_counter_computes (List.replicate (C * (x.length + 1) ^ (d + 1)) true))
        simp only [List.length_replicate] at h
        apply h.mono
        have hp := Nat.one_le_pow (d + 1) (x.length + 1) (Nat.succ_pos _)
        change A * (x.length + 1) ^ (d + 1) + C * (x.length + 1) ^ (d + 1) + 2 +
          5 * (C * (x.length + 1) ^ (d + 1) + 1) ≤ K * (x.length + 1) ^ (d + 1)
        have hseven := Nat.mul_le_mul_left 7 hp
        calc
          _ = (A + 6 * C) * (x.length + 1) ^ (d + 1) + 7 := by ring
          _ ≤ (A + 6 * C) * (x.length + 1) ^ (d + 1) +
              7 * (x.length + 1) ^ (d + 1) := Nat.add_le_add_left hseven _
          _ = _ := by dsimp only [K]; ring
      refine ⟨M, M.k * (K + 1) + K, ?_, ?_⟩
      · intro x
        apply (ht x).mono
        exact Nat.mul_le_mul (by omega)
          (Nat.pow_le_pow_right (Nat.succ_pos _) (by omega))
      · intro x t
        have h := f2_space_of_time (ht x) t
        have hp : (x.length + 1) ^ (d + 1) ≤ C * (x.length + 1) ^ (d + 1) :=
          Nat.le_mul_of_pos_left _ (by omega)
        have hb : K * (x.length + 1) ^ (d + 1) + 1 ≤
            (K + 1) * (C * (x.length + 1) ^ (d + 1) + 1) := by
          have hh := Nat.mul_le_mul_left K hp
          simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
          omega
        exact h.trans ((Nat.mul_le_mul_left M.k hb).trans (by
          rw [← Nat.mul_assoc]
          exact Nat.mul_le_mul_right _ (Nat.le_add_right _ _)))

/-- **P6 space row, fixed-first-component encoder** (spec, fill pending —
design §12 R3; annotates `Turing.FinTM.computesFunInTime_pairEncodeFixed`).
Pairing with a fixed first component runs in constant work-tape space: it
is the prepend row at the doubled fixed word.

**Proof sketch.** Same witness route as
`computesFunInTime_prepend_spaceUsed` at the word
`(α doubled) ++ [false, true]`: no work-head movement at all. -/
theorem computesFunInTime_pairEncodeFixed_spaceUsed (α : List Bool) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => pairEncode α x)
        (fun n => c * (n + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c := by
  simpa only [pairEncode] using
    computesFunInTime_prepend_spaceUsed ((α.flatMap fun b => [b, b]) ++ [false, true])

/-- **P6 space row, first extraction** (spec, fill pending — design §12
R3; annotates `Turing.FinTM.computesFunInTime_pairFst`). The
first-component extractor runs in linear work-tape space: the aligned
scan buffers the undoubled prefix before any emission.

**Proof sketch.** The witness's single work tape holds the undoubled
prefix, of length at most half the input; its head walks the buffer
forward once and replays it once, so the visited set lies in
`[-1, n + 1]`. -/
theorem computesFunInTime_pairFst_spaceUsed :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => ((pairDecode x).map Prod.fst).getD [])
        (fun n => c * (n + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c * (x.length + 1) := by
  refine ⟨f2_pairExtractTM true false, 6, ?_, ?_⟩
  · intro x
    have h := (f2_pairExtract_computes true false x).mono
      (show 5 * (x.length + 1) ≤ 6 * (x.length + 1) by omega)
    cases hd : pairDecode x with
    | none => simpa [hd] using h
    | some p => cases p; simpa [hd] using h
  · intro x t
    have h := f2_space_of_time (f2_pairExtract_computes true false x) t
    change _ ≤ 1 * (5 * (x.length + 1) + 1) at h
    omega

/-- **P6 space row, second extraction** (spec, fill pending — design §12
R3; annotates `Turing.FinTM.computesFunInTime_pairSnd`). The
second-component extractor runs in linear work-tape space (it shares the
buffered parser with the first extractor).

**Proof sketch.** As `computesFunInTime_pairFst_spaceUsed`: one buffer
tape of at most the input length, walked forward and replayed once. -/
theorem computesFunInTime_pairSnd_spaceUsed :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => ((pairDecode x).map Prod.snd).getD [])
        (fun n => c * (n + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c * (x.length + 1) := by
  refine ⟨f2_pairExtractTM false true, 6, ?_, ?_⟩
  · intro x
    have h := (f2_pairExtract_computes false true x).mono
      (show 5 * (x.length + 1) ≤ 6 * (x.length + 1) by omega)
    cases hd : pairDecode x with
    | none => simpa [hd] using h
    | some p => cases p; simpa [hd] using h
  · intro x t
    have h := f2_space_of_time (f2_pairExtract_computes false true x) t
    change _ ≤ 1 * (5 * (x.length + 1) + 1) at h
    omega

/-- **P6 space row, validity test** (spec, fill pending — design §12 R3;
annotates `Turing.FinTM.computesFunInTime_pairValid`). The grammar
validity test runs in constant work-tape space: alignment is finite
control, nothing is buffered.

**Proof sketch.** The existing witness `pairValidTM` has no work tapes
(`k = 0`), so `spaceUsed` is identically `0`. -/
theorem computesFunInTime_pairValid_spaceUsed :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => [(pairDecode x).isSome])
        (fun n => c * (n + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c := by
  refine ⟨f2_pairValidTM, 1, ?_, ?_⟩
  · intro x
    simpa using f2_pairValid_computes x
  · intro x t
    rw [MultiTapeTM.spaceUsed_zero_tapes_eq_zero _ _ rfl]
    omega

/-- **P13 space row, pair to concatenation** (spec, fill pending — design
§12 R3; annotates `Turing.FinTM.computesFunInTime_pairConcat`). The
concatenation extractor runs in linear work-tape space.

**Proof sketch.** The shared buffered parser again: one buffer tape
holding the undoubled prefix, walked forward and replayed once before
the suffix copy. -/
theorem computesFunInTime_pairConcat_spaceUsed :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun z => match pairDecode z with
          | some (a, b) => a ++ b
          | none => [])
        (fun n => c * (n + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c * (x.length + 1) := by
  refine ⟨f2_pairExtractTM true true, 6, ?_, ?_⟩
  · intro x
    have h := (f2_pairExtract_computes true true x).mono
      (show 5 * (x.length + 1) ≤ 6 * (x.length + 1) by omega)
    cases hd : pairDecode x with
    | none => simpa [hd] using h
    | some p => cases p; simpa [hd] using h
  · intro x t
    have h := f2_space_of_time (f2_pairExtract_computes true true x) t
    change _ ≤ 1 * (5 * (x.length + 1) + 1) at h
    omega

/-- **P14 space row, pair duplication** (spec, fill pending — design §12
R3; annotates `Turing.FinTM.computesFunInTime_pairDup`). The duplication
encoder runs in constant work-tape space: both passes re-read the input
tape, nothing is buffered.

**Proof sketch.** The existing witness `pairDupTM` has no work tapes
(`k = 0`), so `spaceUsed` is identically `0`. -/
theorem computesFunInTime_pairDup_spaceUsed :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => pairEncode x x)
        (fun n => c * (n + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c := by
  refine ⟨f2_pairDupTM, 4, f2_pairDup_computes, ?_⟩
  intro x t
  rw [MultiTapeTM.spaceUsed_zero_tapes_eq_zero _ _ rfl]
  omega

/-- The unary generator's received time proof has the sharper degree `e`;
only the fixed-output case needs the separate linear allowance. -/
private lemma f2_unary_sharp (C e : ℕ) :
    ∃ (M : FinTM Bool) (a : ℕ),
      M.ComputesFunInTime (fun x => List.replicate (C * (x.length + 1) ^ e) true)
        (fun n => a * ((n + 1) ^ e + n + 1)) := by
  cases e with
  | zero =>
    obtain ⟨M, a, ht, _⟩ := computesFunInTime_const_spaceUsed (List.replicate C true)
    refine ⟨M, a, ?_⟩
    intro x
    simpa only [Nat.pow_zero, Nat.mul_one] using
      (ht x).mono (Nat.mul_le_mul_left a (by omega : x.length + 1 ≤ 1 + x.length + 1))
  | succ d =>
    refine ⟨f2_catalogPolyUnaryTM d C, C + 5 * (d + 1) + 4, ?_⟩
    intro x
    exact (f2_catalogPoly_unary_computes d C x).mono
      (Nat.mul_le_mul_left _ (by omega))

/-- The decoded first component is no longer than the original encoding;
a malformed encoding extracts the empty word. -/
private lemma f2_first_length (x : List Bool) :
    (((pairDecode x).map Prod.fst).getD []).length ≤ x.length := by
  cases hd : pairDecode x with
  | none => simp
  | some ab =>
    rcases ab with ⟨a, b⟩
    simp only [Option.map_some, Option.getD_some]
    rw [f2_catalogPair_inverse x a b hd, length_pairEncode]
    omega

/-- **P8 space row, threaded length check** (spec, fill pending — design
§12 R3; annotates `Turing.FinTM.computesFunInTime_pairLenCheck`). The
threaded length checker's space is dominated by the unary polynomial
bank `C·(|a|+1)^e` it counts down against, plus the linear parse
buffers.

**Proof sketch.** Head-movement count per stage: the extractor buffers at
most `n` cells, the unary generator's bank holds `C·(|a|+1)^e ≤
C·(n+1)^e` cells, and the countdown walks that bank in place; boundary
cells and the stage count go into `c`. -/
theorem computesFunInTime_pairLenCheck_spaceUsed (C e : ℕ) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun x => [match pairDecode x with
          | some (a, b) => decide (b.length ≤ C * (a.length + 1) ^ e)
          | none => false])
        (fun n => c * (n + 1) ^ (e + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t
          ≤ c * ((x.length + 1) ^ e + x.length + 1) := by
  obtain ⟨U, a, hU⟩ := f2_unary_sharp C e
  let G := bufferedCompTM (f2_pairExtractTM true false) U
  have hF : (f2_pairExtractTM true false).ComputesFunInTime
      (fun x => ((pairDecode x).map Prod.fst).getD []) (fun n => 5 * (n + 1)) := by
    intro x
    have h := f2_pairExtract_computes true false x
    cases hd : pairDecode x with
    | none => simpa [hd] using h
    | some ab => cases ab; simpa [hd] using h
  have hG : G.ComputesFunInTime
      (fun x => List.replicate (C * ((((pairDecode x).map Prod.fst).getD []).length + 1) ^ e) true)
      (fun n => (a + 8) * ((n + 1) ^ e + n + 1)) := by
    intro x
    have hlen := f2_first_length x
    have hpow := Nat.pow_le_pow_left (Nat.add_le_add_right hlen 1) e
    have hu := (hU (((pairDecode x).map Prod.fst).getD [])).mono
      (Nat.mul_le_mul_left a (Nat.add_le_add_right (Nat.add_le_add hpow hlen) 1))
    have h := bufferedCompTM_computesInTime _ _ (hF x) hu
    apply h.mono
    have hp := Nat.one_le_pow e (x.length + 1) (Nat.succ_pos _)
    simp only [Nat.add_mul]
    omega
  let M := f2_pairCountTM G
  let K := a + 13
  have ht : M.ComputesFunInTime
      (fun x => [match pairDecode x with
        | some (u, v) => decide (v.length ≤ C * (u.length + 1) ^ e)
        | none => false])
      (fun n => K * ((n + 1) ^ e + n + 1)) := by
    intro x
    have h := f2_pairCount_computes hG x
    have htime : (a + 8) * ((x.length + 1) ^ e + x.length + 1) + 2 * x.length + 5 ≤
        K * ((x.length + 1) ^ e + x.length + 1) := by
      dsimp only [K]
      simp only [Nat.add_mul]
      omega
    have h' := h.mono htime
    cases hd : pairDecode x with
    | none => simpa [hd] using h'
    | some uv => cases uv; simpa [hd] using h'
  refine ⟨M, 2 * K + M.k * (K + 1), ?_, ?_⟩
  · intro x
    apply (ht x).mono
    have hp : (x.length + 1) ^ e ≤ (x.length + 1) ^ (e + 1) :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
    have hn : x.length + 1 ≤ (x.length + 1) ^ (e + 1) := by
      simpa only [Nat.pow_one] using
        Nat.pow_le_pow_right (Nat.succ_pos x.length) (show 1 ≤ e + 1 by omega)
    calc
      K * ((x.length + 1) ^ e + x.length + 1) ≤
          K * (2 * (x.length + 1) ^ (e + 1)) := Nat.mul_le_mul_left _ (by omega)
      _ = (2 * K) * (x.length + 1) ^ (e + 1) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  · intro x t
    have h := f2_space_of_time (ht x) t
    have hb : K * ((x.length + 1) ^ e + x.length + 1) + 1 ≤
        (K + 1) * ((x.length + 1) ^ e + x.length + 1) := by
      calc
        _ ≤ K * ((x.length + 1) ^ e + x.length + 1) +
            ((x.length + 1) ^ e + x.length + 1) := by omega
        _ = _ := by ring
    exact h.trans ((Nat.mul_le_mul_left M.k hb).trans (by
      rw [← Nat.mul_assoc]
      exact Nat.mul_le_mul_right _ (Nat.le_add_left _ _)))

/- Local copies of the received raw-strip and guard witnesses. -/
/-- Copy the physical input, erase its final false-run and last true, rewind,
then replay. An all-false input halts silently during the reverse scan. -/
private def f2_rawStripTM : FinTM Bool where
  k := 1
  State := Fin 4
  tm := {
    q₀ := 0
    tr := fun q inp work => match q.val with
      | 0 => match inp with
        | some b => ⟨.pos, fun _ => (some (some b), .pos), none, some 0⟩
        | none => ⟨0, fun _ => (none, .neg), none, some 1⟩
      | 1 => match work 0 with
        | none => ⟨0, fun _ => (none, 0), none, none⟩
        | some b => ⟨0, fun _ => (some none, .neg), none, some (if b then 2 else 1)⟩
      | 2 => match work 0 with
        | some _ => ⟨0, fun _ => (none, .neg), none, some 2⟩
        | none => ⟨0, fun _ => (none, .pos), none, some 3⟩
      | _ => match work 0 with
        | some b => ⟨0, fun _ => (none, .pos), some b, some 3⟩
        | none => ⟨0, fun _ => (none, 0), none, none⟩ }

/-- Raw-strip configurations expose the indexed input and a contiguous buffer. -/
private def f2_stripCfg (x : List Bool) (q : Option (Fin 4)) (i : ℕ) (hi : i ≤ x.length)
    (w : List Bool) (h : ℤ) (out : List Bool) : Cfg 1 Bool (Fin 4) x :=
  ⟨q, ⟨i + 1, by omega⟩, fun _ => bufferTape w, fun _ => h, out⟩

/-- Erasing the last written cell restores exactly the shorter buffer. -/
private lemma f2_catalogBuffer_erase (w : List Bool) (b : Bool) :
    Function.update (bufferTape (w ++ [b])) (w.length : ℤ) none = bufferTape w := by
  rw [bufferTape_append, Function.update_idem]
  funext z
  by_cases hz : z = (w.length : ℤ)
  · subst z; simp
  · simp [Function.update_of_ne hz]

/-- The forward copy is silent and installs exactly the scanned input prefix.
**Proof sketch.** One input step appends the next bit at the buffer's right
blank; the input and work heads both advance once. -/
private lemma f2_rawStrip_copy (x : List Bool) : ∀ j (hj : j ≤ x.length),
    f2_rawStripTM.tm.runFrom (f2_rawStripTM.tm.initCfg x) j =
      f2_stripCfg x (some 0) j hj (x.take j) j [] := by
  intro j
  induction j with
  | zero => intro hj; apply Cfg.ext <;> simp [f2_rawStripTM, f2_stripCfg]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hin : (f2_stripCfg x (some 0) j (by omega) (x.take j) j []).inputSymbol =
        some (x[j]'(by omega)) := inputSymbolInner j (by simp [f2_stripCfg]; omega) (by omega)
    unfold MultiTapeTM.step
    change (f2_rawStripTM.tm.tr (0 : Fin 4) _ _).apply _ = _
    rw [hin]
    refine Cfg.ext rfl (moveInputPos_pos_of_ne_right _ (by simp [f2_stripCfg]; omega)) ?_ ?_ rfl
    · funext k
      change Function.update (bufferTape (x.take j)) (j : ℤ) (some (x[j]'(by omega))) =
        bufferTape (x.take (j + 1))
      rw [List.take_succ, List.getElem?_eq_getElem (by omega)]
      simpa only [List.length_take, Nat.min_eq_left (by omega : j ≤ x.length)] using
        (bufferTape_append (x.take j) (x[j]'(by omega))).symm
    · funext k; simp [f2_rawStripTM, f2_stripCfg, Action.apply]

/-- Rewinding the validated buffer from cell `j-1` takes `j+1` transitions.
**Proof sketch.** At the left blank, move right and enter replay. Otherwise
read a buffer cell, move left, and invoke the induction hypothesis. -/
private lemma f2_rawStrip_rewind (x a : List Bool)
    (i : ℕ) (hi : i ≤ x.length) : ∀ j, j ≤ a.length →
    f2_rawStripTM.tm.runFrom
      (f2_stripCfg x (some 2) i hi a ((j : ℤ) - 1) []) (j + 1) =
      f2_stripCfg x (some 3) i hi a 0 [] := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    simp only [f2_rawStripTM, f2_stripCfg, Cfg.workTapeSymbols, Nat.cast_zero,
      zero_sub, bufferTape_left]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext k; simp [Action.apply]
  | succ j ih =>
    intro hj
    have hs : f2_rawStripTM.tm.step
        (f2_stripCfg x (some 2) i hi a (((j + 1 : ℕ) : ℤ) - 1) []) =
        f2_stripCfg x (some 2) i hi a ((j : ℤ) - 1) [] := by
      have hz : (((j + 1 : ℕ) : ℤ) - 1) = j := by omega
      rw [hz]
      unfold MultiTapeTM.step
      simp only [f2_rawStripTM, f2_stripCfg, Cfg.workTapeSymbols, bufferTape_nat,
        List.getElem?_eq_getElem (by omega : j < a.length)]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext k; simp [Action.apply, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Replay appends exactly the visited buffer prefix and preserves its tape.
**Proof sketch.** The same replay invariant as the shared extractor: induct
on the number of visited cells and use the next-prefix equation for lists. -/
private lemma f2_rawStrip_replay (x a : List Bool) (i : ℕ) (hi : i ≤ x.length) :
    ∀ j (_hj : j ≤ a.length),
    f2_rawStripTM.tm.runFrom (f2_stripCfg x (some 3) i hi a 0 []) j =
      f2_stripCfg x (some 3) i hi a j (a.take j) := by
  intro j
  induction j with
  | zero => intro hj; rfl
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    unfold MultiTapeTM.step
    simp only [f2_rawStripTM, f2_stripCfg, Cfg.workTapeSymbols, bufferTape_nat,
      List.getElem?_eq_getElem (by omega : j < a.length)]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ ?_
    · funext k; simp [Action.apply]
    · change a.take j ++ [a[j]'(by omega)] = a.take (j + 1)
      rw [List.take_succ, List.getElem?_eq_getElem (by omega)]
      rfl

/-- Rewind followed by replay halts with exactly the retained buffer.
**Proof sketch.** The rewind costs `|a|+1`; replay and its final blank test
cost another `|a|+1`, and no earlier phase has emitted anything. -/
private lemma f2_rawStrip_finish (x a : List Bool) (i : ℕ) (hi : i ≤ x.length) :
    (f2_rawStripTM.tm.runFrom (f2_stripCfg x (some 2) i hi a (a.length - 1) [])
      (2 * (a.length + 1))).state = none ∧
    (f2_rawStripTM.tm.runFrom (f2_stripCfg x (some 2) i hi a (a.length - 1) [])
      (2 * (a.length + 1))).output = a := by
  have htime : 2 * (a.length + 1) = (a.length + 1) + (a.length + 1) := by omega
  rw [htime, MultiTapeTM.runFrom_add, f2_rawStrip_rewind x a i hi a.length (le_refl _),
    MultiTapeTM.runFrom_succ_eq_step', f2_rawStrip_replay x a i hi a.length (le_refl _)]
  simp [MultiTapeTM.step, f2_rawStripTM, f2_stripCfg, Cfg.workTapeSymbols, Action.apply]

/-- The reverse phase erases the last cell and moves left, branching to
replay preparation precisely when the erased bit is true. -/
private lemma f2_rawStrip_erase (x w : List Bool) (i : ℕ) (hi : i ≤ x.length) (b : Bool) :
    f2_rawStripTM.tm.step
      (f2_stripCfg x (some 1) i hi (w ++ [b]) ((w ++ [b]).length - 1) []) =
      f2_stripCfg x (some (if b then 2 else 1)) i hi w (w.length - 1) [] := by
  have hz : (((w ++ [b]).length : ℕ) : ℤ) - 1 = w.length := by simp
  rw [hz]
  unfold MultiTapeTM.step
  simp only [f2_stripCfg, f2_rawStripTM, Cfg.workTapeSymbols, bufferTape_nat,
    List.getElem?_append_right (by omega : w.length ≤ w.length), Nat.sub_self,
    List.getElem?_cons_zero]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
  · funext k; exact f2_catalogBuffer_erase w b
  · funext k; simp [Action.apply, sub_eq_add_neg]

/-- Reverse erasure implements `splitAtLastTrue` exactly, including rejection
of every all-false word.
**Proof sketch.** Induct from the right. A final false is erased and the
induction continues. A final true is erased and the retained prefix is
rewound and replayed. These are exactly the `reverse.dropWhile` equations. -/
private lemma f2_rawStrip_trim (x w : List Bool) (i : ℕ) (hi : i ≤ x.length) :
    ∃ t ≤ 3 * (w.length + 1),
      (f2_rawStripTM.tm.runFrom (f2_stripCfg x (some 1) i hi w (w.length - 1) []) t).state = none ∧
      (f2_rawStripTM.tm.runFrom (f2_stripCfg x (some 1) i hi w (w.length - 1) []) t).output =
        (splitAtLastTrue w).getD [] := by
  induction w using List.reverseRecOn with
  | nil =>
    refine ⟨1, by simp, ?_⟩
    simp [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.step, f2_rawStripTM, f2_stripCfg,
      Cfg.workTapeSymbols, Action.apply, splitAtLastTrue]
  | append_singleton w b ih =>
    cases b with
    | false =>
      obtain ⟨t, ht, hs, ho⟩ := ih
      refine ⟨t + 1, by simp only [List.length_append, List.length_singleton]; omega, ?_⟩
      rw [MultiTapeTM.runFrom_succ_eq_step, f2_rawStrip_erase]
      exact ⟨hs, by simpa [splitAtLastTrue] using ho⟩
    | true =>
      refine ⟨2 * (w.length + 1) + 1,
        by simp only [List.length_append, List.length_singleton]; omega, ?_⟩
      rw [MultiTapeTM.runFrom_succ_eq_step, f2_rawStrip_erase]
      simpa [splitAtLastTrue] using f2_rawStrip_finish x w i hi

/-- Raw marker stripping runs in linear time, with physical output delayed
until the last true has been located and removed.
**Proof sketch.** Copy in `|x|+1` steps, including the right-blank turn;
the reverse/replay ledger uses at most another `3(|x|+1)` steps. -/
private lemma f2_rawStrip_computes : f2_rawStripTM.ComputesFunInTime
    (fun x => (splitAtLastTrue x).getD []) (fun n => 4 * (n + 1)) := by
  intro x
  have hstart : f2_rawStripTM.tm.runFrom (f2_rawStripTM.tm.initCfg x) (x.length + 1) =
      f2_stripCfg x (some 1) x.length (le_refl _) x (x.length - 1) [] := by
    rw [MultiTapeTM.runFrom_succ_eq_step', f2_rawStrip_copy x x.length (le_refl _)]
    have hin : (f2_stripCfg x (some 0) x.length (le_refl _) (x.take x.length) x.length []).inputSymbol =
        none := by simp [f2_stripCfg, Cfg.inputSymbol]
    unfold MultiTapeTM.step
    change (f2_rawStripTM.tm.tr (0 : Fin 4) _ _).apply _ = _
    rw [hin]
    apply Cfg.ext <;> simp [f2_rawStripTM, f2_stripCfg, Action.apply, sub_eq_add_neg]
  obtain ⟨t, ht, hs, ho⟩ := f2_rawStrip_trim x x x.length (le_refl _)
  have hc : f2_rawStripTM.ComputesInTime x ((splitAtLastTrue x).getD []) (x.length + 1 + t) := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_add, hstart]
    exact ⟨hs, ho⟩
  exact hc.mono (by dsimp only; omega)

/-- A finite scanner emits whether its input contains a true bit. -/
private def f2_anyTrueTM : FinTM Bool where
  k := 0
  State := Unit
  tm := {
    q₀ := ()
    tr := fun _ inp _ => match inp with
      | some false => ⟨.pos, fun i => i.elim0, none, some ()⟩
      | some true => ⟨0, fun i => i.elim0, some true, none⟩
      | none => ⟨0, fun i => i.elim0, some false, none⟩ }

/-- The marker-existence scan halts within one more than the remaining length.
**Proof sketch.** False bits advance silently; a true or the right boundary
emits the corresponding verdict and halts. -/
private lemma f2_anyTrue_run (x rest : List Bool) : ∀ pre (hx : x = pre ++ rest),
    ∃ t ≤ rest.length + 1,
      (f2_anyTrueTM.tm.runFrom (f2_scanCfg x (some ()) pre.length (by simp [hx]) []) t).state = none ∧
      (f2_anyTrueTM.tm.runFrom (f2_scanCfg x (some ()) pre.length (by simp [hx]) []) t).output =
        [rest.any id] := by
  induction rest with
  | nil =>
    intro pre hx
    refine ⟨1, by simp, ?_⟩
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change ((f2_anyTrueTM.tm.tr () _ _).apply _).state = none ∧ _
    rw [f2_scanCfg_read]
    simp [hx, f2_anyTrueTM, Action.apply, f2_scanCfg]
  | cons b rest ih =>
    intro pre hx
    cases b with
    | true =>
      refine ⟨1, by simp, ?_⟩
      simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
      unfold MultiTapeTM.step
      change ((f2_anyTrueTM.tm.tr () _ _).apply _).state = none ∧ _
      rw [f2_scanCfg_read]
      simp [hx, f2_anyTrueTM, Action.apply, f2_scanCfg]
    | false =>
      have hs := f2_scanStep_right f2_anyTrueTM.tm x () (some ()) pre.length (by simp [hx]) [] none
        (by intro work; simp [hx, f2_anyTrueTM])
      obtain ⟨t, ht, hh, ho⟩ := ih (pre ++ [false]) (by simpa [List.append_assoc] using hx)
      refine ⟨t + 1, by simp only [List.length_cons]; omega, ?_⟩
      rw [MultiTapeTM.runFrom_succ_eq_step, hs]
      simpa using And.intro hh ho

/-- The true-bit scanner starts at the first input cell and uses a linear bound. -/
private lemma f2_anyTrue_computes : f2_anyTrueTM.ComputesFunInTime
    (fun x => [x.any id]) (fun n => n + 1) := by
  intro x
  obtain ⟨t, ht, hs, ho⟩ := f2_anyTrue_run x x [] rfl
  have hinit : f2_anyTrueTM.tm.initCfg x = f2_scanCfg x (some ()) 0 (by omega) [] := by
    apply Cfg.ext_zero_tapes <;> rfl
  have hc : f2_anyTrueTM.ComputesInTime x [x.any id] t := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [hinit]
    exact ⟨hs, ho⟩
  exact hc.mono ht

/-- Marker absence is exactly the false verdict; a present marker can be
stripped after any fixed prefix without disturbing that prefix.
**Proof sketch.** Right induction follows `reverse.dropWhile`: append-false
preserves the previous result, and append-true selects the whole old word. -/
private lemma f2_catalogMarker_cases (v : List Bool) :
    (v.any id = false ∧ splitAtLastTrue v = none) ∨
      ∃ u, v.any id = true ∧ splitAtLastTrue v = some u ∧
        ∀ pre, splitAtLastTrue (pre ++ v) = some (pre ++ u) := by
  induction v using List.reverseRecOn with
  | nil => left; simp [splitAtLastTrue]
  | append_singleton v b ih =>
    cases b with
    | false =>
      rcases ih with ⟨ha, hs⟩ | ⟨u, ha, hs, hp⟩
      · left; simpa [splitAtLastTrue] using And.intro ha hs
      · right
        refine ⟨u, by simpa using ha, by simpa [splitAtLastTrue] using hs, ?_⟩
        intro pre
        simpa [splitAtLastTrue, List.append_assoc] using hp pre
    | true =>
      right
      refine ⟨v, by simp, by simp [splitAtLastTrue], ?_⟩
      intro pre
      simp [splitAtLastTrue]

private lemma f2_strip_linear :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun x => match pairDecode x with
          | some (a, v) =>
            match splitAtLastTrue v with
            | some u => pairEncode a u
            | none => []
          | none => [])
        fun n => c * (n + 1) := by
  obtain ⟨S, a, hS, _⟩ := computesFunInTime_pairSnd_spaceUsed
  obtain ⟨D, b, hD⟩ := computesFunInTime_comp hS f2_anyTrue_computes
    (by intro m n h; exact Nat.add_le_add_right h 1)
  have hD' : D.ComputesFunInTime
      (fun x => [((pairDecode x).map Prod.snd |>.getD []).any id])
      (fun n => b * (a * (n + 1) + (a * (n + 1) + 1) + 1)) := by
    simpa only [Function.comp_apply] using hD
  obtain ⟨E, c, hE, _⟩ := computesFunInTime_const_spaceUsed ([] : List Bool)
  obtain ⟨M, d, hM⟩ := computesFunInTime_cond hD' f2_rawStrip_computes hE
  refine ⟨M, d * (2 * b * (a + 1) + (4 + c) + 1), fun x => ?_⟩
  have hh : M.ComputesInTime x
      (match pairDecode x with
        | some (u, v) => match splitAtLastTrue v with
          | some w => pairEncode u w
          | none => []
        | none => [])
      (d * (b * (a * (x.length + 1) + (a * (x.length + 1) + 1) + 1) +
        max (4 * (x.length + 1)) (c * (x.length + 1)) + 1)) := by
    have hm := hM x
    cases hd : pairDecode x with
    | none => simpa [hd] using hm
    | some uv =>
      rcases uv with ⟨u, v⟩
      rcases f2_catalogMarker_cases v with ⟨ha, hs⟩ | ⟨w, ha, hs, hp⟩
      · simpa [hd, ha, hs] using hm
      · have hx : splitAtLastTrue x = some (pairEncode u w) := by
          rw [f2_catalogPair_inverse x u v hd]
          exact hp _
        simpa [hd, ha, hs, hx] using hm
  apply hh.mono
  have hbase : a * (x.length + 1) + 1 ≤ (a + 1) * (x.length + 1) := by
    simp only [Nat.add_mul, Nat.one_mul]; omega
  have hg : b * (a * (x.length + 1) + (a * (x.length + 1) + 1) + 1) ≤
      (2 * b * (a + 1)) * (x.length + 1) := by
    calc
      _ = (2 * b) * (a * (x.length + 1) + 1) := by ring
      _ ≤ (2 * b) * ((a + 1) * (x.length + 1)) := Nat.mul_le_mul_left _ hbase
      _ = _ := by ring
  have hm : max (4 * (x.length + 1)) (c * (x.length + 1)) ≤
      (4 + c) * (x.length + 1) := by
    apply max_le
    · exact Nat.mul_le_mul_right _ (by omega)
    · exact Nat.mul_le_mul_right _ (by omega)
  have hb : b * (a * (x.length + 1) + (a * (x.length + 1) + 1) + 1) +
      max (4 * (x.length + 1)) (c * (x.length + 1)) + 1 ≤
      (2 * b * (a + 1) + (4 + c) + 1) * (x.length + 1) := by
    calc
      _ ≤ (2 * b * (a + 1)) * (x.length + 1) +
          (4 + c) * (x.length + 1) + (x.length + 1) :=
        Nat.add_le_add (Nat.add_le_add hg hm) (by omega)
      _ = _ := by ring
  calc
    _ ≤ d * ((2 * b * (a + 1) + (4 + c) + 1) * (x.length + 1)) := Nat.mul_le_mul_left d hb
    _ = _ := by ring

/-- **P9 space row, marker stripping** (spec, fill pending — design §12
R3; annotates `Turing.FinTM.computesFunInTime_stripLast`). The marker
stripper runs in linear work-tape space: the raw buffer and the guard
banks are each linear, and the quadratic **time** contract is deliberate
slack over the construction's actual linear-derived bound (round-1
finding/note 8 — the attached witness proves a linear intermediate
before weakening; no replay story is needed).

**Proof sketch.** The witness's guard/extraction banks and the raw-strip
buffer are each at most linear (`O(n + 1)` cells); the timed conditional
keeps them disjoint; every head stays inside linear intervals, and the
retained `(n+1)²` time clause is slack, not a resource actually spent on
space. -/
theorem computesFunInTime_stripLast_spaceUsed :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun x => match pairDecode x with
          | some (a, v) =>
            match splitAtLastTrue v with
            | some u => pairEncode a u
            | none => []
          | none => [])
        (fun n => c * (n + 1) ^ 2) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c * (x.length + 1) := by
  obtain ⟨M, a, hM⟩ := f2_strip_linear
  refine ⟨M, a + M.k * (a + 1), ?_, ?_⟩
  · intro x
    apply (hM x).mono
    have hn : x.length + 1 ≤ (x.length + 1) ^ 2 := by
      simpa only [Nat.pow_one] using Nat.pow_le_pow_right (Nat.succ_pos x.length)
        (show 1 ≤ 2 by omega)
    exact (Nat.mul_le_mul_left a hn).trans
      (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
  · intro x t
    have h := f2_space_of_time (hM x) t
    have hb : a * (x.length + 1) + 1 ≤ (a + 1) * (x.length + 1) := by
      simp only [Nat.add_mul, Nat.one_mul]
      omega
    exact h.trans ((Nat.mul_le_mul_left M.k hb).trans (by
      rw [← Nat.mul_assoc]
      exact Nat.mul_le_mul_right _ (Nat.le_add_left _ _)))

/-- **P11 space row, fixed-width increment** (spec, fill pending — design
§12 R3; annotates `Turing.FinTM.computesFunInTime_incFixed`; the
string-function counterpart of `Turing.incrementTM`). The incrementer
runs in constant work-tape space: it validates and emits from two native
input scans with the carry resident in control.

**Proof sketch.** The existing witness `incFixedTM` has no work tapes
(`k = 0`), so `spaceUsed` is identically `0`. -/
theorem computesFunInTime_incFixed_spaceUsed :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => (incFixed x).getD [])
        (fun n => c * (n + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c := by
  refine ⟨f2_incFixedTM, 3, f2_incFixed_computes, ?_⟩
  intro x t
  rw [MultiTapeTM.spaceUsed_zero_tapes_eq_zero _ _ rfl]
  omega

/-- Control of the forwarding map: silent pair validation and buffering,
separate buffer rewinds, doubled-prefix emission, and clamped virtual input. -/
private inductive a2_MapState (Q : Type) where
  | parse (pending : Option Bool)
  | copyB | backB | backA | emitA | emitAgain (b : Bool) | separator
  | run (q : Q) (tag : Bool)
  deriving DecidableEq

private instance a2_mapStateFintype (Q : Type) [Fintype Q] : Fintype (a2_MapState Q) :=
  derive_fintype% _

/-- Administration touches only the two input buffers, and never a payload tape. -/
private def a2_mapAct (M : FinTM Bool) (inp : SignType)
    (a b : Option (Option Bool) × SignType) (out : Option Bool)
    (next : Option (a2_MapState M.State)) : Action (1 + (1 + M.k)) Bool (a2_MapState M.State) :=
  ⟨inp, tapeBlocks (fun _ => a) b (fun _ => (none, 0)), out, next⟩

/-- The commissioned forwarding controller. The two buffers contain the
components, never the payload output. In setup mode the payload entry is a
stationary live seam, used only to certify its first arrival. In forwarding
mode each payload step has exactly its original work actions and emission;
`virtualMove` clamps both virtual-input boundaries, including empty input. -/
private def a2_mapTM (M : FinTM Bool) (forward : Bool) : FinTM Bool where
  k := 1 + (1 + M.k)
  State := a2_MapState M.State
  tm := {
    q₀ := .parse none
    tr := fun q inp work =>
      let act := a2_mapAct M
      let first := work (Fin.castAdd (1 + M.k) (0 : Fin 1))
      let second := work (Fin.natAdd 1 (Fin.castAdd M.k (0 : Fin 1)))
      match q with
      | .parse none => match inp with
        | none => act 0 (none, 0) (none, 0) none none
        | some b => act .pos (none, 0) (none, 0) none (some (.parse (some b)))
      | .parse (some b) => match inp with
        | none => act 0 (none, 0) (none, 0) none none
        | some d => if b = d then
            act .pos (some (some b), .pos) (none, 0) none (some (.parse none))
          else if b then act .pos (none, 0) (none, 0) none none
          else act .pos (none, .neg) (none, 0) none (some .copyB)
      | .copyB => match inp with
        | some b => act .pos (none, 0) (some (some b), .pos) none (some .copyB)
        | none => act 0 (none, 0) (none, .neg) none (some .backB)
      | .backB => match second with
        | some _ => act 0 (none, 0) (none, .neg) none (some .backB)
        | none => act 0 (none, 0) (none, .pos) none (some .backA)
      | .backA => match first with
        | some _ => act 0 (none, .neg) (none, 0) none (some .backA)
        | none => act 0 (none, .pos) (none, 0) none (some .emitA)
      | .emitA => match first with
        | some b => act 0 (none, 0) (none, 0) (some b) (some (.emitAgain b))
        | none => act 0 (none, 0) (none, 0) (some false) (some .separator)
      | .emitAgain b => act 0 (none, .pos) (none, 0) (some b) (some .emitA)
      | .separator => act 0 (none, 0) (none, 0) (some true) (some (.run M.tm.q₀ true))
      | .run q b => if forward then
          let a := M.tm.tr q second (fun i => work (Fin.natAdd 1 (Fin.natAdd 1 i)))
          let m := virtualMove b second a.inputTape
          ⟨0, tapeBlocks (fun _ => (none, 0)) (none, m) a.workTapes,
            a.output, a.state.map (fun q => .run q (virtualNextTag b m))⟩
        else controlAction 0 (some (.run q b)) }

/-- Administrative configurations have two buffered words and an untouched
blank payload bank. The physical output is explicit. -/
private def a2_mapCfg (M : FinTM Bool) (x : List Bool) (q : Option (a2_MapState M.State))
    (p : Fin (x.length + 2)) (a b : List Bool) (ha hb : ℤ) (out : List Bool) :
    Cfg (1 + (1 + M.k)) Bool (a2_MapState M.State) x where
  state := q
  inputPos := p
  workTapes := tapeBlocks (fun _ => bufferTape a) (bufferTape b) (fun _ _ => none)
  workTapePos := tapeBlocks (fun _ => ha) hb (fun _ => 0)
  output := out

/-- The forwarding configuration retains the physical input, first buffer,
and already emitted prefix; the second buffer is the source's virtual input. -/
private def a2_mapVirtual (M : FinTM Bool) {x y : List Bool}
    (c : Cfg M.k Bool M.State y) (tag : Bool) (p : Fin (x.length + 2))
    (a pre : List Bool) : Cfg (1 + (1 + M.k)) Bool (a2_MapState M.State) x where
  state := c.state.map (fun q => .run q tag)
  inputPos := p
  workTapes := tapeBlocks (fun _ => bufferTape a) (bufferTape y) c.workTapes
  workTapePos := tapeBlocks (fun _ => (a.length : ℤ)) ((c.inputPos.val : ℤ) - 1) c.workTapePos
  output := pre ++ c.output

/-- The parser reads its native input independently of both buffers. -/
private lemma a2_mapCfg_read (M : FinTM Bool) (x : List Bool) (q : Option (a2_MapState M.State))
    (i : ℕ) (hi : i ≤ x.length) (a b : List Bool) (ha hb : ℤ) (out : List Bool) :
    (a2_mapCfg M x q ⟨i + 1, by omega⟩ a b ha hb out).inputSymbol = x[i]? :=
  inputSymbol_at _ i hi rfl

/-- Administrative actions with no writes only change the two buffer heads,
control, input position, and the physical output. -/
private lemma a2_map_move (M : FinTM Bool) (x : List Bool)
    (q q' : Option (a2_MapState M.State)) (p : Fin (x.length + 2))
    (a b : List Bool) (ha hb : ℤ) (out : List Bool)
    (mi ma mb : SignType) (emit : Option Bool) :
    (a2_mapAct M mi (none, ma) (none, mb) emit q').apply
      (a2_mapCfg M x q p a b ha hb out) =
      a2_mapCfg M x q' (moveInputPos p mi) a b (ha + ma.cast) (hb + mb.cast)
        (out ++ emit.toList) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [a2_mapAct, a2_mapCfg, Action.apply]
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
        simp [a2_mapAct, a2_mapCfg, Action.apply]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [a2_mapAct, a2_mapCfg, Action.apply]
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
        simp [a2_mapAct, a2_mapCfg, Action.apply]

/-- Reading the first half of an aligned block changes only finite control
and the native input head. No physical output is emitted. -/
private lemma a2_map_first (M : FinTM Bool) (x pre rest a : List Bool) (b : Bool)
    (hx : x = pre ++ b :: rest) :
    (a2_mapTM M false).tm.step
      (a2_mapCfg M x (some (.parse none)) ⟨pre.length + 1, by simp [hx] <;> omega⟩
        a [] a.length 0 []) =
      a2_mapCfg M x (some (.parse (some b))) ⟨pre.length + 2, by simp [hx] <;> omega⟩
        a [] a.length 0 [] := by
  unfold MultiTapeTM.step
  change ((a2_mapTM M false).tm.tr (.parse none) _ _).apply _ = _
  rw [a2_mapCfg_read M x _ pre.length (by simp [hx])]
  have hr : x[pre.length]? = some b := by simp [hx]
  rw [hr]
  change (a2_mapAct M .pos (none, 0) (none, 0) none _).apply _ = _
  rw [a2_map_move]
  simp only [SignType.cast, add_zero, Option.toList_none,
    List.append_nil]
  congr 1
  exact moveInputPos_pos_of_ne_right _ (by simp [hx])

/-- Doubled blocks append one bit to the first buffer. `01` starts suffix
buffering; `10` rejects before emitting. Both missing-bit cases are handled
by the surrounding parser induction. -/
private lemma a2_map_block (M : FinTM Bool) (x pre rest a : List Bool) (b c : Bool)
    (hx : x = pre ++ b :: c :: rest) :
    (a2_mapTM M false).tm.runFrom
      (a2_mapCfg M x (some (.parse none)) ⟨pre.length + 1, by simp [hx] <;> omega⟩
        a [] a.length 0 []) 2 =
      if b = c then a2_mapCfg M x (some (.parse none))
        ⟨pre.length + 3, by simp [hx] <;> omega⟩ (a ++ [b]) [] (a ++ [b]).length 0 []
      else if b then a2_mapCfg M x none
        ⟨pre.length + 3, by simp [hx] <;> omega⟩ a [] a.length 0 []
      else a2_mapCfg M x (some .copyB)
        ⟨pre.length + 3, by simp [hx] <;> omega⟩ a [] (a.length - 1) 0 [] := by
  change (a2_mapTM M false).tm.step ((a2_mapTM M false).tm.step _) = _
  rw [a2_map_first M x pre (c :: rest) a b hx]
  unfold MultiTapeTM.step
  change ((a2_mapTM M false).tm.tr (.parse (some b)) _ _).apply _ = _
  rw [a2_mapCfg_read M x _ (pre.length + 1) (by simp [hx])]
  have hr : x[pre.length + 1]? = some c := by simp [hx]
  rw [hr]
  have hm : moveInputPos (⟨pre.length + 2, by simp [hx] <;> omega⟩ : Fin (x.length + 2)) .pos =
      ⟨pre.length + 3, by simp [hx] <;> omega⟩ :=
    moveInputPos_pos_of_ne_right _ (by simp [hx])
  cases b <;> cases c <;> simp only [a2_mapTM, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
  all_goals refine Cfg.ext rfl hm ?_ ?_ rfl
  all_goals first
    | (funext i
       refine Fin.addCases (fun j => ?_) (fun j => ?_) i
       · simpa only [a2_mapAct, a2_mapCfg, Action.apply, tapeBlocks_left] using (bufferTape_append a _).symm
       · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
           simp [a2_mapAct, a2_mapCfg, Action.apply])
    | (funext i
       refine Fin.addCases (fun j => ?_) (fun j => ?_) i
       · simp [a2_mapAct, a2_mapCfg, Action.apply, sub_eq_add_neg]
       · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
           simp [a2_mapAct, a2_mapCfg, Action.apply])

/-- After validation, the complete suffix is buffered silently. Its right
blank is turned left exactly once, including when the suffix is empty. -/
private lemma a2_map_suffix (M : FinTM Bool) (x rest a : List Bool) :
    ∀ pre b (hx : x = pre ++ rest),
    (a2_mapTM M false).tm.runFrom
      (a2_mapCfg M x (some .copyB) ⟨pre.length + 1, by simp [hx] <;> omega⟩
        a b (a.length - 1) b.length []) (rest.length + 1) =
      a2_mapCfg M x (some .backB) ⟨x.length + 1, by omega⟩
        a (b ++ rest) (a.length - 1) ((b ++ rest).length - 1) [] := by
  induction rest with
  | nil =>
    intro pre b hx
    simp only [List.length_nil, Nat.zero_add, MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change ((a2_mapTM M false).tm.tr .copyB _ _).apply _ = _
    rw [a2_mapCfg_read M x _ pre.length (by simp [hx])]
    have hr : x[pre.length]? = none := by simp [hx]
    rw [hr]
    change (a2_mapAct M 0 (none, 0) (none, .neg) none _).apply _ = _
    rw [a2_map_move]
    simp [hx, sub_eq_add_neg]
  | cons d rest ih =>
    intro pre b hx
    have hs : (a2_mapTM M false).tm.step
        (a2_mapCfg M x (some .copyB) ⟨pre.length + 1, by simp [hx] <;> omega⟩
          a b (a.length - 1) b.length []) =
        a2_mapCfg M x (some .copyB) ⟨(pre ++ [d]).length + 1, by simp [hx] <;> omega⟩
          a (b ++ [d]) (a.length - 1) (b ++ [d]).length [] := by
      unfold MultiTapeTM.step
      change ((a2_mapTM M false).tm.tr .copyB _ _).apply _ = _
      rw [a2_mapCfg_read M x _ pre.length (by simp [hx])]
      have hr : x[pre.length]? = some d := by simp [hx]
      rw [hr]
      refine Cfg.ext rfl ?_ ?_ ?_ rfl
      · simpa only [List.length_append, List.length_singleton] using
          moveInputPos_pos_of_ne_right
            (⟨pre.length + 1, by simp [hx] <;> omega⟩ : Fin (x.length + 2)) (by simp [hx])
      · funext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simp [a2_mapTM, a2_mapAct, a2_mapCfg, Action.apply]
        · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
          · simpa only [a2_mapTM, a2_mapAct, a2_mapCfg, Action.apply, tapeBlocks_buffer] using
              (bufferTape_append b d).symm
          · simp [a2_mapTM, a2_mapAct, a2_mapCfg, Action.apply]
      · funext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simp [a2_mapTM, a2_mapAct, a2_mapCfg, Action.apply]
        · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
            simp [a2_mapTM, a2_mapAct, a2_mapCfg, Action.apply]
    simp only [List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    simpa only [List.append_assoc, List.singleton_append] using
      ih (pre ++ [d]) (b ++ [d]) (by simpa [List.append_assoc] using hx)

/-- Rewind the second buffer to zero, preserving the first buffer and the
blank payload bank. The left-blank step is present even at width zero. -/
private lemma a2_map_backB (M : FinTM Bool) (x a b : List Bool)
    (p : Fin (x.length + 2)) : ∀ j, j ≤ b.length →
    (a2_mapTM M false).tm.runFrom
      (a2_mapCfg M x (some .backB) p a b (a.length - 1) ((j : ℤ) - 1) []) (j + 1) =
      a2_mapCfg M x (some .backA) p a b (a.length - 1) 0 [] := by
  intro j
  induction j with
  | zero =>
    intro hj
    simp only [List.length_nil, Nat.zero_add, MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    simp only [a2_mapTM, a2_mapCfg, Cfg.workTapeSymbols, tapeBlocks_buffer,
      Nat.cast_zero, zero_sub, bufferTape_left]
    change (a2_mapAct M 0 (none, 0) (none, .pos) none _).apply
      (a2_mapCfg M x (some .backB) p a b (a.length - 1) (-1) []) = _
    rw [a2_map_move]
    simp [a2_mapCfg]
  | succ j ih =>
    intro hj
    have hr : bufferTape b (((j + 1 : ℕ) : ℤ) - 1) = some b[j] := by
      rw [show (((j + 1 : ℕ) : ℤ) - 1) = (j : ℤ) by omega,
        bufferTape_nat, List.getElem?_eq_getElem (by omega)]
    have hs : (a2_mapTM M false).tm.step
        (a2_mapCfg M x (some .backB) p a b (a.length - 1) (((j + 1 : ℕ) : ℤ) - 1) []) =
        a2_mapCfg M x (some .backB) p a b (a.length - 1) ((j : ℤ) - 1) [] := by
      unfold MultiTapeTM.step
      simp only [a2_mapTM, a2_mapCfg, Cfg.workTapeSymbols, tapeBlocks_buffer, hr]
      change (a2_mapAct M 0 (none, 0) (none, .neg) none _).apply
        (a2_mapCfg M x (some .backB) p a b (a.length - 1) (((j + 1 : ℕ) : ℤ) - 1) []) = _
      rw [a2_map_move]
      simp [a2_mapCfg, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- The corresponding first-buffer rewind, leaving virtual input at zero. -/
private lemma a2_map_backA (M : FinTM Bool) (x a b : List Bool)
    (p : Fin (x.length + 2)) : ∀ j, j ≤ a.length →
    (a2_mapTM M false).tm.runFrom
      (a2_mapCfg M x (some .backA) p a b ((j : ℤ) - 1) 0 []) (j + 1) =
      a2_mapCfg M x (some .emitA) p a b 0 0 [] := by
  intro j
  induction j with
  | zero =>
    intro hj
    simp only [List.length_nil, Nat.zero_add, MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    simp only [a2_mapTM, a2_mapCfg, Cfg.workTapeSymbols, tapeBlocks_left,
      Nat.cast_zero, zero_sub, bufferTape_left]
    change (a2_mapAct M 0 (none, .pos) (none, 0) none _).apply
      (a2_mapCfg M x (some .backA) p a b (-1) 0 []) = _
    rw [a2_map_move]
    simp [a2_mapCfg]
  | succ j ih =>
    intro hj
    have hr : bufferTape a (((j + 1 : ℕ) : ℤ) - 1) = some a[j] := by
      rw [show (((j + 1 : ℕ) : ℤ) - 1) = (j : ℤ) by omega,
        bufferTape_nat, List.getElem?_eq_getElem (by omega)]
    have hs : (a2_mapTM M false).tm.step
        (a2_mapCfg M x (some .backA) p a b (((j + 1 : ℕ) : ℤ) - 1) 0 []) =
        a2_mapCfg M x (some .backA) p a b ((j : ℤ) - 1) 0 [] := by
      unfold MultiTapeTM.step
      simp only [a2_mapTM, a2_mapCfg, Cfg.workTapeSymbols, tapeBlocks_left, hr]
      change (a2_mapAct M 0 (none, .neg) (none, 0) none _).apply
        (a2_mapCfg M x (some .backA) p a b (((j + 1 : ℕ) : ℤ) - 1) 0 []) = _
      rw [a2_map_move]
      simp [a2_mapCfg, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Emit each retained first-component bit twice, then `01`, and enter the
payload seam. The second buffer and payload bank are unchanged.
**Proof sketch.** Each nonblank first-buffer cell takes two emission steps;
the second advances the head. At the right blank, two further transitions
emit the delimiter and enter the source's start state with right-arrival tag. -/
private lemma a2_map_emit (M : FinTM Bool) (x a b rest : List Bool)
    (p : Fin (x.length + 2)) : ∀ pre out, a = pre ++ rest →
    (a2_mapTM M false).tm.runFrom
      (a2_mapCfg M x (some .emitA) p a b pre.length 0 out) (2 * rest.length + 2) =
      a2_mapCfg M x (some (.run M.tm.q₀ true)) p a b a.length 0
        (out ++ rest.flatMap (fun d => [d, d]) ++ [false, true]) := by
  induction rest with
  | nil =>
    intro pre out he
    simp only [List.append_nil] at he
    subst a
    have hs : (a2_mapTM M false).tm.step
        (a2_mapCfg M x (some .emitA) p pre b pre.length 0 out) =
        a2_mapCfg M x (some .separator) p pre b pre.length 0 (out ++ [false]) := by
      unfold MultiTapeTM.step
      simp only [a2_mapTM, a2_mapCfg, Cfg.workTapeSymbols, tapeBlocks_left,
        bufferTape_nat, List.getElem?_length]
      change (a2_mapAct M 0 (none, 0) (none, 0) (some false) _).apply
        (a2_mapCfg M x (some .emitA) p pre b pre.length 0 out) = _
      rw [a2_map_move]
      simp [a2_mapCfg]
    change (a2_mapTM M false).tm.step ((a2_mapTM M false).tm.step _) = _
    rw [hs]
    change (a2_mapAct M 0 (none, 0) (none, 0) (some true) _).apply _ = _
    rw [a2_map_move]
    simp [List.append_assoc]
  | cons d rest ih =>
    intro pre out he
    have hr : bufferTape a pre.length = some d := by simp [he]
    have hs : (a2_mapTM M false).tm.runFrom
        (a2_mapCfg M x (some .emitA) p a b pre.length 0 out) 2 =
        a2_mapCfg M x (some .emitA) p a b (pre ++ [d]).length 0 (out ++ [d, d]) := by
      change (a2_mapTM M false).tm.step ((a2_mapTM M false).tm.step _) = _
      have hfirst : (a2_mapTM M false).tm.step
          (a2_mapCfg M x (some .emitA) p a b pre.length 0 out) =
          a2_mapCfg M x (some (.emitAgain d)) p a b pre.length 0 (out ++ [d]) := by
        unfold MultiTapeTM.step
        simp only [a2_mapTM, a2_mapCfg, Cfg.workTapeSymbols, tapeBlocks_left, hr]
        change (a2_mapAct M 0 (none, 0) (none, 0) (some d) _).apply
          (a2_mapCfg M x (some .emitA) p a b pre.length 0 out) = _
        rw [a2_map_move]
        simp [a2_mapCfg]
      rw [hfirst]
      change (a2_mapAct M 0 (none, .pos) (none, 0) (some d) _).apply _ = _
      rw [a2_map_move]
      simp [List.append_assoc]
    rw [show 2 * (d :: rest).length + 2 = 2 + (2 * rest.length + 2) by simp; omega,
      MultiTapeTM.runFrom_add, hs]
    simpa only [List.flatMap_cons, List.append_assoc, List.cons_append, List.nil_append] using
      ih (pre ++ [d]) (out ++ [d, d]) (by simpa [List.append_assoc] using he)

/-- Successful suffix buffering, two rewinds, and encoded-prefix emission
reach the initialized payload seam within `3|a|+2|b|+5` transitions. -/
private lemma a2_map_finish (M : FinTM Bool) (x pre a b : List Bool)
    (hx : x = pre ++ b) :
    (a2_mapTM M false).tm.runFrom
      (a2_mapCfg M x (some .copyB) ⟨pre.length + 1, by simp [hx] <;> omega⟩
        a [] (a.length - 1) 0 []) (3 * a.length + 2 * b.length + 5) =
      a2_mapVirtual M (M.tm.initCfg b) true ⟨x.length + 1, by omega⟩ a (pairEncode a []) := by
  rw [show 3 * a.length + 2 * b.length + 5 =
      ((b.length + 1) + (b.length + 1) + (a.length + 1)) + (2 * a.length + 2) by omega,
    MultiTapeTM.runFrom_add (a := (b.length + 1) + (b.length + 1) + (a.length + 1)) (b := 2 * a.length + 2),
    MultiTapeTM.runFrom_add (a := (b.length + 1) + (b.length + 1)) (b := a.length + 1),
    MultiTapeTM.runFrom_add (a := b.length + 1) (b := b.length + 1)]
  have hcopy := a2_map_suffix M x b a pre [] hx
  simp only [List.nil_append, List.length_nil, Nat.cast_zero] at hcopy
  rw [hcopy]
  rw [a2_map_backB M x a b _ _ (le_refl _), a2_map_backA M x a b _ _ (le_refl _)]
  have he := a2_map_emit M x a b a (⟨x.length + 1, by omega⟩) [] [] (by simp)
  simp only [List.length_nil, Nat.cast_zero, List.nil_append] at he
  rw [he]
  refine Cfg.ext rfl rfl rfl ?_ ?_
  · funext i
    simp [a2_mapCfg, a2_mapVirtual, MultiTapeTM.initCfg, Cfg.init]
  · simp [a2_mapCfg, a2_mapVirtual, MultiTapeTM.initCfg, Cfg.init, pairEncode]

/-- The validating setup either halts silently on malformed input or reaches
exactly the required payload seam with the encoded first component emitted.
**Proof sketch.** Induct on aligned pairs. Equal bits add one buffered bit;
`10`, a missing bit, or a missing delimiter reject. At `01`, buffer the entire
suffix and apply the rewind/emission ledger. No payload transition is used. -/
private lemma a2_map_parse (M : FinTM Bool) (x rest : List Bool) :
    ∀ pre a (hx : x = pre ++ rest), ∃ t ≤ 3 * rest.length + 3 * a.length + 5,
      match pairDecode rest with
      | some (d, b) => (a2_mapTM M false).tm.runFrom
          (a2_mapCfg M x (some (.parse none)) ⟨pre.length + 1, by simp [hx] <;> omega⟩
            a [] a.length 0 []) t =
          a2_mapVirtual M (M.tm.initCfg b) true ⟨x.length + 1, by omega⟩
            (a ++ d) (pairEncode (a ++ d) [])
      | none =>
          ((a2_mapTM M false).tm.runFrom
            (a2_mapCfg M x (some (.parse none)) ⟨pre.length + 1, by simp [hx] <;> omega⟩
              a [] a.length 0 []) t).state = none ∧
          ((a2_mapTM M false).tm.runFrom
            (a2_mapCfg M x (some (.parse none)) ⟨pre.length + 1, by simp [hx] <;> omega⟩
              a [] a.length 0 []) t).output = [] := by
  induction rest using List.twoStepInduction with
  | nil =>
    intro pre a hx
    refine ⟨1, by simp, ?_⟩
    simp only [pairDecode, MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change (((a2_mapTM M false).tm.tr (.parse none) _ _).apply _).state = none ∧ _
    rw [a2_mapCfg_read M x _ pre.length (by simp [hx])]
    simp [hx, a2_mapTM, a2_mapAct, Action.apply, a2_mapCfg]
  | singleton b =>
    intro pre a hx
    refine ⟨2, by simp, ?_⟩
    have hd : pairDecode [b] = none := by cases b <;> rfl
    rw [hd]
    change ((a2_mapTM M false).tm.step ((a2_mapTM M false).tm.step _)).state = none ∧
      ((a2_mapTM M false).tm.step ((a2_mapTM M false).tm.step _)).output = []
    rw [a2_map_first M x pre [] a b hx]
    unfold MultiTapeTM.step
    change (((a2_mapTM M false).tm.tr (.parse (some b)) _ _).apply _).state = none ∧ _
    rw [a2_mapCfg_read M x _ (pre.length + 1) (by simp [hx])]
    cases b <;> simp [hx, a2_mapTM, a2_mapAct, Action.apply, a2_mapCfg, pairDecode]
  | cons_cons b c rest ih _ =>
    intro pre a hx
    by_cases h : b = c
    · subst c
      obtain ⟨t, ht, he⟩ := ih (pre ++ [b, b]) (a ++ [b])
        (by simpa [List.append_assoc] using hx)
      refine ⟨2 + t, by simp only [List.length_append, List.length_cons, List.length_nil] at *; omega, ?_⟩
      have hr := a2_map_block M x pre rest a b b hx
      simp only [if_pos rfl] at hr
      simp only [List.length_append, List.length_cons, List.length_nil] at he
      cases b <;> cases hd : pairDecode rest with
      | none =>
        simp only [pairDecode, hd] at he ⊢
        rw [MultiTapeTM.runFrom_add, hr]
        simpa [List.append_assoc, Nat.add_assoc] using he
      | some p =>
        rcases p with ⟨d, v⟩
        simp only [pairDecode, hd] at he ⊢
        rw [MultiTapeTM.runFrom_add, hr]
        simpa [List.append_assoc, Nat.add_assoc] using he
    · cases b <;> cases c
      · exact False.elim (h rfl)
      · refine ⟨2 + (3 * a.length + 2 * rest.length + 5), by simp only [List.length_cons]; omega, ?_⟩
        simp only [pairDecode, List.append_nil]
        rw [MultiTapeTM.runFrom_add, a2_map_block M x pre rest a false true hx]
        simp only [Bool.false_eq_true, ↓reduceIte]
        simpa only [List.length_append, List.length_cons, List.length_nil] using
          a2_map_finish M x (pre ++ [false, true]) a rest (by simpa [List.append_assoc] using hx)
      · refine ⟨2, by simp, ?_⟩
        rw [a2_map_block M x pre rest a true false hx]
        simp [a2_mapCfg, pairDecode]
      · exact False.elim (h rfl)

/-- Starting with empty buffers gives a uniform linear setup budget on every
input, including malformed encodings. -/
private lemma a2_map_setup (M : FinTM Bool) (x : List Bool) :
    ∃ t ≤ 5 * (x.length + 1),
      match pairDecode x with
      | some (a, b) => (a2_mapTM M false).tm.runFrom ((a2_mapTM M false).tm.initCfg x) t =
          a2_mapVirtual M (M.tm.initCfg b) true ⟨x.length + 1, by omega⟩ a (pairEncode a [])
      | none => ((a2_mapTM M false).tm.runFrom ((a2_mapTM M false).tm.initCfg x) t).state = none ∧
          ((a2_mapTM M false).tm.runFrom ((a2_mapTM M false).tm.initCfg x) t).output = [] := by
  obtain ⟨t, ht, he⟩ := a2_map_parse M x x [] [] rfl
  have hi : (a2_mapTM M false).tm.initCfg x =
      a2_mapCfg M x (some (.parse none)) ⟨1, by omega⟩ [] [] 0 0 [] := by
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    · funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp [a2_mapCfg, MultiTapeTM.initCfg, Cfg.init]
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
          simp [a2_mapCfg, MultiTapeTM.initCfg, Cfg.init]
    · funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp [a2_mapCfg, MultiTapeTM.initCfg, Cfg.init]
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
          simp [a2_mapCfg, MultiTapeTM.initCfg, Cfg.init]
  refine ⟨t, by simp only [List.length_nil, mul_zero, add_zero] at ht; omega, ?_⟩
  rw [hi]
  simpa only [List.nil_append, List.length_nil, Nat.cast_zero] using he

/-- One forwarded payload step has exactly the source work actions and
emission. `virtualMove_correct` proves both boundary clamps and preserves
its arrival tag, without a nonempty-input assumption. -/
private lemma a2_mapVirtual_step (M : FinTM Bool) {x y : List Bool}
    (c : Cfg M.k Bool M.State y) (tag : Bool) (hb : VirtualTag c.inputPos tag)
    (p : Fin (x.length + 2)) (a pre : List Bool) :
    ∃ tag', VirtualTag (M.tm.step c).inputPos tag' ∧
      (a2_mapTM M true).tm.step (a2_mapVirtual M c tag p a pre) =
        a2_mapVirtual M (M.tm.step c) tag' p a pre := by
  cases hq : c.state with
  | none =>
    refine ⟨tag, ?_, ?_⟩
    · simpa only [MultiTapeTM.step_of_halt hq] using hb
    · rw [MultiTapeTM.step_of_halt hq, MultiTapeTM.step_of_halt]
      simp [a2_mapVirtual, hq]
  | some q =>
    let act := M.tm.tr q c.inputSymbol c.workTapeSymbols
    let mv := virtualMove tag c.inputSymbol act.inputTape
    have hm := virtualMove_correct c tag hb act.inputTape
    have hc : M.tm.step c = act.apply c := by simp only [MultiTapeTM.step, hq, act]
    refine ⟨virtualNextTag tag mv, ?_, ?_⟩
    · simpa only [hc, Action.apply] using hm.2
    · have hs : (a2_mapVirtual M c tag p a pre).state = some (.run q tag) := by
        simp [a2_mapVirtual, hq]
      have hv : (a2_mapVirtual M c tag p a pre).workTapeSymbols
          (Fin.natAdd 1 (Fin.castAdd M.k (0 : Fin 1))) = c.inputSymbol := by
        simp [a2_mapVirtual, Cfg.workTapeSymbols, bufferTape_inputSymbol]
      have hr : (fun i => (a2_mapVirtual M c tag p a pre).workTapeSymbols
          (Fin.natAdd 1 (Fin.natAdd 1 i))) = c.workTapeSymbols := by
        funext i
        simp [a2_mapVirtual, Cfg.workTapeSymbols]
      unfold MultiTapeTM.step
      rw [hs]
      dsimp only [a2_mapTM]
      rw [hv, hr, hq]
      change (Action.apply _ _) = a2_mapVirtual M (act.apply c) _ p a pre
      refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ ?_
      · funext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simp [a2_mapVirtual, Action.apply, act]
        · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
            simp [a2_mapVirtual, Action.apply, act]
      · funext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simp [a2_mapVirtual, Action.apply, act]
        · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
          · simpa only [a2_mapVirtual, Action.apply, tapeBlocks_buffer, ↓reduceIte] using hm.1
          · simp [a2_mapVirtual, Action.apply, act]
      · exact List.append_assoc pre c.output act.output.toList

/-- Payload forwarding preserves its entire source trajectory at all times,
including the final halting action and the stationary halted tail. -/
private lemma a2_mapVirtual_run (M : FinTM Bool) {x y : List Bool}
    (c : Cfg M.k Bool M.State y) (tag : Bool) (hb : VirtualTag c.inputPos tag)
    (p : Fin (x.length + 2)) (a pre : List Bool) (t : ℕ) :
    ∃ tag', VirtualTag (M.tm.runFrom c t).inputPos tag' ∧
      (a2_mapTM M true).tm.runFrom (a2_mapVirtual M c tag p a pre) t =
        a2_mapVirtual M (M.tm.runFrom c t) tag' p a pre := by
  induction t with
  | zero => exact ⟨tag, hb, rfl⟩
  | succ t ih =>
    obtain ⟨b, hb, he⟩ := ih
    obtain ⟨d, hd, hs⟩ := a2_mapVirtual_step M _ b hb p a pre
    refine ⟨d, ?_, ?_⟩
    · simpa only [MultiTapeTM.runFrom_succ_eq_step'] using hd
    · rw [MultiTapeTM.runFrom_succ_eq_step', he, hs, MultiTapeTM.runFrom_succ_eq_step']

/-- A setup configuration is at the payload seam if its control is a
payload state; this includes the source start state on empty virtual input. -/
private def a2_mapEntered (M : FinTM Bool) {x : List Bool}
    (c : Cfg (1 + (1 + M.k)) Bool (a2_MapState M.State) x) : Prop :=
  ∃ q tag, c.state = some (.run q tag)

/-- Setup mode freezes every field once it reaches a payload state. -/
private lemma a2_mapSetup_stationary (M : FinTM Bool) {x : List Bool}
    (c : Cfg (1 + (1 + M.k)) Bool (a2_MapState M.State) x)
    (h : a2_mapEntered M c) (t : ℕ) : (a2_mapTM M false).tm.runFrom c t = c := by
  obtain ⟨q, tag, hs⟩ := h
  have he : (a2_mapTM M false).tm.step c = c := by
    simp only [MultiTapeTM.step, hs, a2_mapTM, Bool.false_eq_true, ↓reduceIte,
      controlAction_apply, moveInputPos_zero]
    cases c
    simp_all
  induction t with
  | zero => rfl
  | succ t ih => rw [MultiTapeTM.runFrom_succ_eq_step', ih, he]

/-- Before the payload seam the operational and setup transition tables
coincide, on all configurations rather than just well-formed buffers. -/
private lemma a2_mapSetup_step (M : FinTM Bool) {x : List Bool}
    (c : Cfg (1 + (1 + M.k)) Bool (a2_MapState M.State) x)
    (h : ¬a2_mapEntered M c) :
    (a2_mapTM M true).tm.step c = (a2_mapTM M false).tm.step c := by
  cases hs : c.state with
  | none => simp only [MultiTapeTM.step, hs]
  | some q =>
    cases q with
    | run q tag => exact (h ⟨q, tag, hs⟩).elim
    | parse pending => cases pending <;> simp only [MultiTapeTM.step, hs, a2_mapTM]
    | _ => simp only [MultiTapeTM.step, hs, a2_mapTM]

/-- Transfer an entire setup prefix through the final entry action. -/
private lemma a2_mapSetup_run (M : FinTM Bool) (x : List Bool) (t : ℕ)
    (h : ∀ u < t, ¬a2_mapEntered M
      ((a2_mapTM M false).tm.runFrom ((a2_mapTM M false).tm.initCfg x) u)) :
    (a2_mapTM M true).tm.runFrom ((a2_mapTM M true).tm.initCfg x) t =
      (a2_mapTM M false).tm.runFrom ((a2_mapTM M false).tm.initCfg x) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (fun u hu => h u (by omega)),
      a2_mapSetup_step M _ (h t (by omega)), MultiTapeTM.runFrom_succ_eq_step']

/-- Every setup action leaves each payload work head fixed. -/
private lemma a2_mapSetup_head_step (M : FinTM Bool) {x : List Bool}
    (c : Cfg (1 + (1 + M.k)) Bool (a2_MapState M.State) x) (i : Fin M.k) :
    ((a2_mapTM M false).tm.step c).workTapePos (Fin.natAdd 1 (Fin.natAdd 1 i)) =
      c.workTapePos (Fin.natAdd 1 (Fin.natAdd 1 i)) := by
  have ha (q : a2_MapState M.State) (inp : Option Bool)
      (work : Fin (1 + (1 + M.k)) → Option Bool) :
      ((a2_mapTM M false).tm.tr q inp work).workTapes (Fin.natAdd 1 (Fin.natAdd 1 i)) =
        (none, 0) := by
    cases q with
    | parse pending =>
      cases pending with
      | none => cases inp <;> simp [a2_mapTM, a2_mapAct]
      | some b =>
        cases inp with
        | none => simp [a2_mapTM, a2_mapAct]
        | some d =>
          by_cases he : b = d
          · simp [a2_mapTM, he, a2_mapAct]
          · cases b <;> simp [a2_mapTM, he, a2_mapAct]
    | copyB => cases inp <;> simp [a2_mapTM, a2_mapAct]
    | backB =>
      cases h : work (Fin.natAdd 1 (Fin.castAdd M.k (0 : Fin 1))) <;>
        simp only [a2_mapTM, h, a2_mapAct, tapeBlocks_right]
    | backA =>
      cases h : work (Fin.castAdd (1 + M.k) (0 : Fin 1)) <;>
        simp only [a2_mapTM, h, a2_mapAct, tapeBlocks_right]
    | emitA =>
      cases h : work (Fin.castAdd (1 + M.k) (0 : Fin 1)) <;>
        simp only [a2_mapTM, h, a2_mapAct, tapeBlocks_right]
    | emitAgain b => simp [a2_mapTM, a2_mapAct]
    | separator => simp [a2_mapTM, a2_mapAct]
    | run q tag => rfl
  unfold MultiTapeTM.step
  cases hs : c.state with
  | none => rfl
  | some q => simp only [Action.apply, ha]; simp

/-- The payload bank stays at its initial origin throughout setup, with no
condition on grammar validity, buffer widths, or elapsed time. -/
private lemma a2_mapSetup_heads (M : FinTM Bool) (x : List Bool) (t : ℕ) (i : Fin M.k) :
    ((a2_mapTM M false).tm.runFrom ((a2_mapTM M false).tm.initCfg x) t).workTapePos
      (Fin.natAdd 1 (Fin.natAdd 1 i)) = 0 := by
  induction t with
  | zero => rfl
  | succ t ih => rw [MultiTapeTM.runFrom_succ_eq_step', a2_mapSetup_head_step, ih]

/-- Choose the first payload entry, then transfer every prefix to the
operational host. The stationary setup seam identifies this first entry
with the complete validating/buffering/emission endpoint, so no payload
work is hidden in the administrative time bound. -/
private lemma a2_map_launch (M : FinTM Bool) (x a b : List Bool)
    (hd : pairDecode x = some (a, b)) :
    ∃ u ≤ 5 * (x.length + 1),
      (a2_mapTM M true).tm.runFrom ((a2_mapTM M true).tm.initCfg x) u =
        a2_mapVirtual M (M.tm.initCfg b) true ⟨x.length + 1, by omega⟩ a (pairEncode a []) ∧
      ∀ v ≤ u, (a2_mapTM M true).tm.runFrom ((a2_mapTM M true).tm.initCfg x) v =
        (a2_mapTM M false).tm.runFrom ((a2_mapTM M false).tm.initCfg x) v := by
  classical
  obtain ⟨t, ht, he⟩ := a2_map_setup M x
  simp only [hd] at he
  have hex : ∃ u, a2_mapEntered M
      ((a2_mapTM M false).tm.runFrom ((a2_mapTM M false).tm.initCfg x) u) := by
    refine ⟨t, M.tm.q₀, true, ?_⟩
    rw [he]
    rfl
  let u := Nat.find hex
  have hu : u ≤ t := Nat.find_min' hex (by rw [he]; exact ⟨M.tm.q₀, true, rfl⟩)
  have hg : ∀ v < u, ¬a2_mapEntered M
      ((a2_mapTM M false).tm.runFrom ((a2_mapTM M false).tm.initCfg x) v) :=
    fun v hv => Nat.find_min hex hv
  have hprefix (v : ℕ) (hv : v ≤ u) := a2_mapSetup_run M x v
    (fun w hw => hg w (by omega))
  refine ⟨u, hu.trans ht, ?_, hprefix⟩
  rw [hprefix u (le_refl _)]
  have hs := a2_mapSetup_stationary M _ (Nat.find_spec hex) (t - u)
  have hh : (a2_mapTM M false).tm.runFrom ((a2_mapTM M false).tm.initCfg x) t =
      (a2_mapTM M false).tm.runFrom ((a2_mapTM M false).tm.initCfg x) u := by
    rw [show t = u + (t - u) by omega, MultiTapeTM.runFrom_add]
    exact hs
  rw [← hh, he]

/-- A malformed encoding never reaches a payload state, since such a setup
state would remain live forever. Hence its entire operational trajectory
agrees with setup, including the silent halt and every later time. -/
private lemma a2_map_reject (M : FinTM Bool) (x : List Bool)
    (hd : pairDecode x = none) :
    ∃ u ≤ 5 * (x.length + 1),
      ((a2_mapTM M true).tm.runFrom ((a2_mapTM M true).tm.initCfg x) u).state = none ∧
      ((a2_mapTM M true).tm.runFrom ((a2_mapTM M true).tm.initCfg x) u).output = [] ∧
      ∀ v, (a2_mapTM M true).tm.runFrom ((a2_mapTM M true).tm.initCfg x) v =
        (a2_mapTM M false).tm.runFrom ((a2_mapTM M false).tm.initCfg x) v := by
  obtain ⟨u, hu, he⟩ := a2_map_setup M x
  simp only [hd] at he
  have hn (v : ℕ) : ¬a2_mapEntered M
      ((a2_mapTM M false).tm.runFrom ((a2_mapTM M false).tm.initCfg x) v) := by
    intro hv
    obtain ⟨q, tag, hq⟩ := hv
    by_cases h : v ≤ u
    · have hrun : (a2_mapTM M false).tm.runFrom ((a2_mapTM M false).tm.initCfg x) u =
          (a2_mapTM M false).tm.runFrom ((a2_mapTM M false).tm.initCfg x) v := by
        rw [show u = v + (u - v) by omega, MultiTapeTM.runFrom_add]
        exact a2_mapSetup_stationary M _ ⟨q, tag, hq⟩ _
      have hh := he.1
      rw [hrun, hq] at hh
      contradiction
    · have hh : (a2_mapTM M false).tm.runFrom ((a2_mapTM M false).tm.initCfg x) v =
          (a2_mapTM M false).tm.runFrom ((a2_mapTM M false).tm.initCfg x) u := by
        rw [show v = u + (v - u) by omega, MultiTapeTM.runFrom_add,
          MultiTapeTM.runFrom_of_halt _ he.1]
      rw [hh, he.1] at hq
      contradiction
  have heq (v : ℕ) := a2_mapSetup_run M x v (fun w _ => hn w)
  refine ⟨u, hu, ?_, ?_, heq⟩ <;> rw [heq u]
  · exact he.1
  · exact he.2

/-- Explicit equivalence between a disjoint pair of banks and their concatenation. -/
private def a2_mapSumEquiv (a b : ℕ) : Fin a ⊕ Fin b ≃ Fin (a + b) where
  toFun := Sum.elim (Fin.castAdd b) (Fin.natAdd a)
  invFun := fun i => if h : (i : ℕ) < a then Sum.inl ⟨i, h⟩
    else Sum.inr ⟨i - a, by have := i.isLt; omega⟩
  left_inv := by
    intro i
    cases i with
    | inl i => simp [i.isLt]
    | inr i =>
      simp only [Sum.elim_inr, Fin.coe_natAdd, not_lt.mpr (Nat.le_add_right _ _), ↓reduceDIte]
      congr 1
      apply Fin.ext
      simp
  right_inv := by
    intro i
    dsimp only
    split
    · rfl
    · apply Fin.ext
      dsimp only [Sum.elim_inr, Fin.coe_natAdd]
      omega

/-- Sum a finite tape bank by its two disjoint blocks. -/
private lemma a2_map_sum {a b : ℕ} (f : Fin (a + b) → ℕ) :
    (∑ i : Fin (a + b), f i) =
      (∑ i : Fin a, f (Fin.castAdd b i)) + ∑ i : Fin b, f (Fin.natAdd a i) := by
  rw [Fintype.sum_equiv (a2_mapSumEquiv a b).symm f (fun i => f ((a2_mapSumEquiv a b).toFun i))]
  · exact Finset.sum_disjSum Finset.univ Finset.univ _
  · intro x
    simp only [Equiv.toFun_as_coe, Equiv.apply_symm_apply]

/-- Count the two administrative tapes by fixed integer intervals, and the
payload bank by containment in one source trajectory. No coefficient is
introduced on the source-bank sum. -/
private lemma a2_map_space (M : FinTM Bool) (x y : List Bool) (t D S : ℕ)
    (hfirst : ∀ u ≤ t, -(D : ℤ) ≤
        ((a2_mapTM M true).tm.runFrom ((a2_mapTM M true).tm.initCfg x) u).workTapePos
          (Fin.castAdd (1 + M.k) (0 : Fin 1)) ∧
      ((a2_mapTM M true).tm.runFrom ((a2_mapTM M true).tm.initCfg x) u).workTapePos
          (Fin.castAdd (1 + M.k) (0 : Fin 1)) ≤ D)
    (hsecond : ∀ u ≤ t, -(D : ℤ) ≤
        ((a2_mapTM M true).tm.runFrom ((a2_mapTM M true).tm.initCfg x) u).workTapePos
          (Fin.natAdd 1 (Fin.castAdd M.k (0 : Fin 1))) ∧
      ((a2_mapTM M true).tm.runFrom ((a2_mapTM M true).tm.initCfg x) u).workTapePos
          (Fin.natAdd 1 (Fin.castAdd M.k (0 : Fin 1))) ≤ D)
    (hsource : ∀ i, (a2_mapTM M true).tm.visitedByTapeHead ((a2_mapTM M true).tm.initCfg x) t
        (Fin.natAdd 1 (Fin.natAdd 1 i)) ⊆ M.tm.visitedByTapeHead (M.tm.initCfg y) t i)
    (hs : M.tm.spaceUsed (M.tm.initCfg y) t ≤ S) :
    (a2_mapTM M true).tm.spaceUsed ((a2_mapTM M true).tm.initCfg x) t ≤ S + 2 * (2 * D + 1) := by
  have hc (i : Fin (1 + (1 + M.k)))
      (h : ∀ u ≤ t, -(D : ℤ) ≤
          ((a2_mapTM M true).tm.runFrom ((a2_mapTM M true).tm.initCfg x) u).workTapePos i ∧
        ((a2_mapTM M true).tm.runFrom ((a2_mapTM M true).tm.initCfg x) u).workTapePos i ≤ D) :
      (a2_mapTM M true).tm.spaceUsedByTape ((a2_mapTM M true).tm.initCfg x) t i ≤ 2 * D + 1 := by
    have hsub : (a2_mapTM M true).tm.visitedByTapeHead ((a2_mapTM M true).tm.initCfg x) t i ⊆
        Finset.Icc (-(D : ℤ)) (D : ℤ) := by
      intro z hz
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_Icc.mpr (h u (by have := Finset.mem_range.mp hu; omega))
    exact (Finset.card_le_card hsub).trans (by rw [Int.card_Icc]; omega)
  have ha := hc _ hfirst
  have hb := hc _ hsecond
  have hp : (∑ i : Fin M.k, (a2_mapTM M true).tm.spaceUsedByTape
      ((a2_mapTM M true).tm.initCfg x) t (Fin.natAdd 1 (Fin.natAdd 1 i))) ≤ S := by
    exact (Finset.sum_le_sum (fun i _ => Finset.card_le_card (hsource i))).trans hs
  change (∑ i : Fin (1 + (1 + M.k)),
    (a2_mapTM M true).tm.spaceUsedByTape ((a2_mapTM M true).tm.initCfg x) t i) ≤ _
  rw [a2_map_sum, a2_map_sum]
  simp only [Fintype.sum_unique]
  simp only [show (default : Fin 1) = 0 from Subsingleton.elim _ _]
  omega

/-- **Threaded-map space row** (spec, fill pending — design §12 R3;
annotates `Turing.FinTM.computesFunInTime_pairMapSnd`, the round-2
catalog addition). Given a payload machine with its own space bound
`Sg` (monotone, since the payload runs on the second component, which is
no longer than the whole input), the threaded-map controller's space is
the payload's plus linear administration. **The witness is a new
forwarding controller, not the received captured-payload machine**
(round-1 finding 4, the witness-honesty refutation: `pairMapTM`'s
capture tape visits `|g b| + 1` cells — the unary-square payload defeats
any linear administrative claim about it; output length is not bounded
by the payload's work space).

**Proof sketch.** The commissioned controller: validate and buffer the
input pair (`O(n + 1)` cells), emit the encoded first component, then
simulate `Mg` on the buffered second component **forwarding its output**
(the E2/`embedEmitTM` discipline — emissions go to the physical output,
never to a work bank), leaving the payload's work-head trajectories
unchanged — coefficient `1` on `Sg` — plus the linear buffer and
administration; the `Monotone Sg` hypothesis transports the payload
bound from `|b|` to `n`. Named construction obligations for the brief:
the validating buffer stage, the forwarding payload stage, and their
seam. -/
theorem computesFunInTime_pairMapSnd_spaceUsed {Mg : FinTM Bool}
    {g : List Bool → List Bool} {Tg : ℕ → ℕ} (Sg : ℕ → ℕ)
    (hg : Mg.ComputesFunInTime g Tg) (hTg : Monotone Tg)
    (hgs : ∀ (y : List Bool) (t : ℕ),
      Mg.tm.spaceUsed (Mg.tm.initCfg y) t ≤ Sg y.length)
    (hSg : Monotone Sg) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun z => match pairDecode z with
          | some (a, b) => pairEncode a (g b)
          | none => [])
        (fun n => c * (n + 1 + Tg n)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t
          ≤ Sg x.length + c * (x.length + 1) := by
  let M := a2_mapTM Mg true
  refine ⟨M, 22, ?_, ?_⟩
  · intro x
    cases hd : pairDecode x with
    | none =>
      obtain ⟨u, hu, hh, ho, _⟩ := a2_map_reject Mg x hd
      have ht : M.ComputesInTime x [] u := ⟨_, hh, ho, rfl⟩
      simpa only [hd] using ht.mono (show u ≤ 22 * (x.length + 1 + Tg x.length) by omega)
    | some ab =>
      rcases ab with ⟨a, b⟩
      obtain ⟨u, hu, hinit, _⟩ := a2_map_launch Mg x a b hd
      have hlen : b.length ≤ x.length := by
        have h := congrArg List.length (eq_pairEncode_of_pairDecode x a b hd)
        rw [length_pairEncode] at h
        omega
      obtain ⟨tag, _, hr⟩ := a2_mapVirtual_run Mg (x := x) (Mg.tm.initCfg b) true
        (by simp [VirtualTag, MultiTapeTM.initCfg, Cfg.init])
        (⟨x.length + 1, by omega⟩) a (pairEncode a []) (Tg b.length)
      obtain ⟨space, hh, ho, _⟩ := hg b
      have hrun : M.tm.runFrom (M.tm.initCfg x) (u + Tg b.length) =
          a2_mapVirtual Mg (Mg.tm.runFrom (Mg.tm.initCfg b) (Tg b.length)) tag
            ⟨x.length + 1, by omega⟩ a (pairEncode a []) := by
        rw [MultiTapeTM.runFrom_add, hinit]
        exact hr
      have ht : M.ComputesInTime x (pairEncode a (g b)) (u + Tg b.length) := by
        refine ⟨_, ?_, ?_, rfl⟩
        · rw [hrun]
          change Option.map (fun q => a2_MapState.run q tag)
            (Mg.tm.runFrom (Mg.tm.initCfg b) (Tg b.length)).state = none
          rw [hh]
          rfl
        · rw [hrun]
          change pairEncode a [] ++
            (Mg.tm.runFrom (Mg.tm.initCfg b) (Tg b.length)).output = pairEncode a (g b)
          rw [ho]
          simp [pairEncode, List.append_assoc]
      have hT := hTg hlen
      simpa only [hd] using ht.mono
        (show u + Tg b.length ≤ 22 * (x.length + 1 + Tg x.length) by omega)
  · intro x t
    let D := 5 * (x.length + 1)
    have hshort (v : ℕ) (hv : v ≤ D) (i : Fin M.k) :
        -(D : ℤ) ≤ (M.tm.runFrom (M.tm.initCfg x) v).workTapePos i ∧
        (M.tm.runFrom (M.tm.initCfg x) v).workTapePos i ≤ D := by
      have h := f2_head_steps M.tm (M.tm.initCfg x) v i
      rw [show (M.tm.initCfg x).workTapePos i = 0 from rfl, zero_sub, zero_add] at h
      constructor <;> omega
    cases hd : pairDecode x with
    | none =>
      obtain ⟨u, hu, hh, _, heq⟩ := a2_map_reject Mg x hd
      have hheads (v : ℕ) (i : Fin M.k) :
          -(D : ℤ) ≤ (M.tm.runFrom (M.tm.initCfg x) v).workTapePos i ∧
          (M.tm.runFrom (M.tm.initCfg x) v).workTapePos i ≤ D := by
        by_cases hv : v ≤ u
        · exact hshort v (hv.trans hu) i
        · rw [show v = u + (v - u) by omega, MultiTapeTM.runFrom_add,
            MultiTapeTM.runFrom_of_halt _ hh]
          exact hshort u hu i
      have hp (i : Fin Mg.k) : M.tm.visitedByTapeHead (M.tm.initCfg x) t
          (Fin.natAdd 1 (Fin.natAdd 1 i)) ⊆ Mg.tm.visitedByTapeHead (Mg.tm.initCfg x) t i := by
        intro z hz
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
        change ((a2_mapTM Mg true).tm.runFrom _ v).workTapePos _ ∈ _
        rw [heq v, a2_mapSetup_heads]
        exact Finset.mem_image.mpr ⟨0, by simp, rfl⟩
      have hs := a2_map_space Mg x x t D (Sg x.length)
        (fun v _ => hheads v _) (fun v _ => hheads v _) hp (hgs x t)
      change M.tm.spaceUsed (M.tm.initCfg x) t ≤ _ at hs
      dsimp only [D] at hs
      omega
    | some ab =>
      rcases ab with ⟨a, b⟩
      obtain ⟨u, hu, hinit, hprefix⟩ := a2_map_launch Mg x a b hd
      have hlen : a.length ≤ x.length ∧ b.length ≤ x.length := by
        have h := congrArg List.length (eq_pairEncode_of_pairDecode x a b hd)
        rw [length_pairEncode] at h
        omega
      have hrun (v : ℕ) : ∃ tag,
          M.tm.runFrom (M.tm.initCfg x) (u + v) =
            a2_mapVirtual Mg (Mg.tm.runFrom (Mg.tm.initCfg b) v) tag
              ⟨x.length + 1, by omega⟩ a (pairEncode a []) := by
        obtain ⟨tag, _, he⟩ := a2_mapVirtual_run Mg (x := x) (Mg.tm.initCfg b) true
          (by simp [VirtualTag, MultiTapeTM.initCfg, Cfg.init])
          (⟨x.length + 1, by omega⟩) a (pairEncode a []) v
        refine ⟨tag, ?_⟩
        rw [MultiTapeTM.runFrom_add, hinit]
        exact he
      have ha (v : ℕ) : -(D : ℤ) ≤
          (M.tm.runFrom (M.tm.initCfg x) v).workTapePos (Fin.castAdd (1 + Mg.k) (0 : Fin 1)) ∧
          (M.tm.runFrom (M.tm.initCfg x) v).workTapePos (Fin.castAdd (1 + Mg.k) (0 : Fin 1)) ≤ D := by
        by_cases hv : v ≤ u
        · exact hshort v (hv.trans hu) _
        · obtain ⟨tag, he⟩ := hrun (v - u)
          rw [show v = u + (v - u) by omega, he]
          simp only [a2_mapVirtual, tapeBlocks_left]
          dsimp only [D]
          constructor <;> omega
      have hb (v : ℕ) : -(D : ℤ) ≤
          (M.tm.runFrom (M.tm.initCfg x) v).workTapePos (Fin.natAdd 1 (Fin.castAdd Mg.k (0 : Fin 1))) ∧
          (M.tm.runFrom (M.tm.initCfg x) v).workTapePos (Fin.natAdd 1 (Fin.castAdd Mg.k (0 : Fin 1))) ≤ D := by
        by_cases hv : v ≤ u
        · exact hshort v (hv.trans hu) _
        · obtain ⟨tag, he⟩ := hrun (v - u)
          rw [show v = u + (v - u) by omega, he]
          simp only [a2_mapVirtual, tapeBlocks_buffer]
          have hp := (Mg.tm.runFrom (Mg.tm.initCfg b) (v - u)).inputPos.isLt
          dsimp only [D]
          constructor <;> omega
      -- Each payload-bank head is either still at its source origin or is
      -- exactly a source position at a time no greater than this horizon.
      have hp (i : Fin Mg.k) : M.tm.visitedByTapeHead (M.tm.initCfg x) t
          (Fin.natAdd 1 (Fin.natAdd 1 i)) ⊆ Mg.tm.visitedByTapeHead (Mg.tm.initCfg b) t i := by
        intro z hz
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
        have hvt : v ≤ t := by have := Finset.mem_range.mp hv; omega
        by_cases hvu : v ≤ u
        · change ((a2_mapTM Mg true).tm.runFrom _ v).workTapePos _ ∈ _
          rw [hprefix v hvu, a2_mapSetup_heads]
          exact Finset.mem_image.mpr ⟨0, by simp, rfl⟩
        · obtain ⟨tag, he⟩ := hrun (v - u)
          change (M.tm.runFrom (M.tm.initCfg x) v).workTapePos _ ∈ _
          rw [show v = u + (v - u) by omega, he]
          simp only [a2_mapVirtual, tapeBlocks_right]
          exact Finset.mem_image.mpr ⟨v - u, Finset.mem_range.mpr (by omega), rfl⟩
      have hs := a2_map_space Mg x b t D (Sg x.length)
        (fun v _ => ha v) (fun v _ => hb v) hp ((hgs b t).trans (hSg hlen.2))
      change M.tm.spaceUsed (M.tm.initCfg x) t ≤ _ at hs
      dsimp only [D] at hs
      omega

/-- A live endpoint rules out a halt anywhere in its preceding run. -/
private lemma f2_loop_live_prefix {k : ℕ} {S : Type*} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (cfg : Cfg k Bool S x) (t : ℕ)
    (ht : (tm.runFrom cfg t).state ≠ none) :
    ∀ u ≤ t, (tm.runFrom cfg u).state ≠ none := by
  intro u hu hh
  have he : tm.runFrom cfg t = tm.runFrom cfg u := by
    rw [← Nat.add_sub_of_le hu, MultiTapeTM.runFrom_add,
      MultiTapeTM.runFrom_of_halt _ hh]
  exact ht (by rw [he]; exact hh)

/-- An empty final output forces every earlier output to be empty. -/
private lemma f2_loop_silent_prefix {k : ℕ} {S : Type*} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (cfg : Cfg k Bool S x) (t : ℕ)
    (ht : (tm.runFrom cfg t).output = []) :
    ∀ u ≤ t, (tm.runFrom cfg u).output = [] := by
  intro u hu
  have hp := tm.output_prefix cfg hu
  rw [ht] at hp
  simpa using hp

/-- Replace a possibly padded halting-time witness by its first halt,
retaining the entire endpoint configuration.
**Proof sketch.** Choose the least halting time. Minimality supplies the
strict liveness guard; the absorbing-halt law identifies its endpoint
with the original, possibly later, witness. -/
private lemma f2_loop_first_halt {k : ℕ} {S : Type*} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (cfg : Cfg k Bool S x) (t : ℕ)
    (hstart : cfg.state ≠ none) (hhalt : (tm.runFrom cfg t).state = none) :
    ∃ u, 0 < u ∧ u ≤ t ∧
      (∀ v < u, ¬(tm.runFrom cfg v).Halted) ∧
      (tm.runFrom cfg u).state = none ∧ tm.runFrom cfg u = tm.runFrom cfg t := by
  classical
  let h : ∃ u, (tm.runFrom cfg u).state = none := ⟨t, hhalt⟩
  have hu := Nat.find_spec h
  have hle := Nat.find_min' h hhalt
  refine ⟨Nat.find h, ?_, hle, ?_, hu, ?_⟩
  · by_contra hn
    have hz : Nat.find h = 0 := by omega
    rw [hz, MultiTapeTM.runFrom_zero] at hu
    exact hstart hu
  · intro v hv
    exact Nat.find_min h hv
  · symm
    rw [← Nat.add_sub_of_le hle, MultiTapeTM.runFrom_add,
      MultiTapeTM.runFrom_of_halt _ hu]

/-- The declared invariant holds at each orbit word, including unreachable
rounds after an earlier acceptance. -/
private lemma f2_loop_orbit_inv (Inv : List Bool → List Bool → Prop)
    (stepF : List Bool → List Bool → List Bool) (s0 : List Bool → List Bool)
    (hInv0 : ∀ x, Inv x (s0 x))
    (hInvStep : ∀ x s, Inv x s → Inv x (stepF x s)) (x : List Bool) (i : ℕ) :
    Inv x ((stepF x)^[i] (s0 x)) := by
  induction i with
  | zero => exact hInv0 x
  | succ i ih => rw [Function.iterate_succ_apply']; exact hInvStep x _ ih

/-- The fuel run bounds the fixed counter width on each actual input. -/
private lemma f2_loop_fuel_width (F : FinTM Bool) (R T : ℕ → ℕ)
    (hF : F.ComputesFunInTime (fun x => Nat.bits (R x.length)) T) (x : List Bool) :
    (Nat.bits (R x.length)).length ≤ T x.length := by
  obtain ⟨s, hhalt, hout, hspace⟩ := hF x
  simpa only [hout] using F.tm.output_length_le x (T x.length)

/-- One native input-head move increases its position by at most one. -/
private lemma f2_loop_input_move_le {n : ℕ} (p : Fin (n + 2)) (m : SignType) :
    (moveInputPos p m).val ≤ p.val + 1 := by
  cases m with
  | zero => simp
  | neg => rw [moveInputPos_neg_val]; omega
  | pos =>
    by_cases hp : p.val = n + 1
    · have he : p = ⟨n + 1, by omega⟩ := Fin.ext hp
      rw [he]
      simp only [SignType.pos_eq_one, moveInputPos_rightBoundary]
      omega
    · rw [moveInputPos_pos_of_ne_right p hp]

/-- Input displacement is bounded by elapsed time, even for sublinear budgets. -/
private lemma f2_loop_input_run_le {k : ℕ} {S : Type*} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (c : Cfg k Bool S x) (t : ℕ) :
    (tm.runFrom c t).inputPos.val ≤ c.inputPos.val + t := by
  have stepBound (d : Cfg k Bool S x) : (tm.step d).inputPos.val ≤ d.inputPos.val + 1 := by
    cases hd : d.state with
    | none => simp [MultiTapeTM.step, hd]
    | some q =>
      simpa only [MultiTapeTM.step, hd, Action.apply] using
        f2_loop_input_move_le d.inputPos (tm.tr q d.inputSymbol d.workTapeSymbols).inputTape
  induction t with
  | zero => simp
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step']
    exact (stepBound _).trans (by omega)

/-- A run appends at most one output bit per step, from any seam configuration. -/
private lemma f2_loop_output_length_le {k : ℕ} {S : Type*} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (c : Cfg k Bool S x) (t : ℕ) :
    (tm.runFrom c t).output.length ≤ c.output.length + t := by
  have stepBound (d : Cfg k Bool S x) : (tm.step d).output.length ≤ d.output.length + 1 := by
    rw [MultiTapeTM.step_output, List.length_append]
    cases tm.outputSymbol d <;> simp
  induction t with
  | zero => simp
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step']
    exact (stepBound _).trans (by omega)

/-- The input rewind has a bound in its starting position, so it can be
charged to the preceding run without scanning the entire input.
**Proof sketch.** Take the mandatory first left move and apply the proved
`rewind_scan` at the resulting position. Its exact scan time is position
plus one; the first left move never increases position. -/
private lemma f2_loop_rewind_bounded {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (start scan : S) (dest : Option S)
    (hstart : ∀ inp work, tm.tr start inp work = controlAction .neg (some scan))
    (hscan : ∀ inp work, tm.tr scan inp work =
      match inp with
      | some _ => controlAction .neg (some scan)
      | none => controlAction .pos dest)
    (cfg : Cfg k Bool S x) (hs : cfg.state = some start) :
    ∃ t ≤ cfg.inputPos.val + 2,
      tm.runFrom cfg t = {cfg with state := dest, inputPos := 1} := by
  have hstep : tm.step cfg =
      {cfg with state := some scan, inputPos := moveInputPos cfg.inputPos .neg} := by
    unfold MultiTapeTM.step
    rw [hs]
    dsimp only
    rw [hstart, controlAction_apply]
  let c := tm.step cfg
  have hc : c.state = some scan := by simp only [c, hstep]
  have hp : c.inputPos.val ≤ x.length := by
    simp only [c, hstep, moveInputPos_neg_val]
    have := cfg.inputPos.isLt
    omega
  refine ⟨1 + (c.inputPos.val + 1), ?_, ?_⟩
  · simp only [c, hstep, moveInputPos_neg_val]
    omega
  · rw [MultiTapeTM.runFrom_add]
    have hfirst : tm.runFrom cfg 1 = c := rfl
    rw [hfirst, rewind_scan tm scan dest hscan c hc hp]
    simp only [c, hstep]

/-- Fixed-width little-endian decrement and its success flag. Underflow
sets the existing cells to true and returns false, without extending the word. -/
private def f2_loopDebit : List Bool → List Bool × Bool
  | [] => ([], false)
  | true :: bs => (false :: bs, true)
  | false :: bs => (true :: (f2_loopDebit bs).1, (f2_loopDebit bs).2)

/-- Number of low zero bits traversed by a borrow. -/
private def f2_loopBorrowPos : List Bool → ℕ
  | false :: bs => f2_loopBorrowPos bs + 1
  | _ => 0

/-- The borrow scan cannot cross more cells than the fixed width. -/
private lemma f2_loopBorrowPos_le (u : List Bool) : f2_loopBorrowPos u ≤ u.length := by
  induction u with
  | nil => rfl
  | cons b u ih => cases b <;> simp only [f2_loopBorrowPos, List.length_cons] <;> omega

/-- Both successful decrements and underflow preserve the counter width. -/
private lemma f2_loopDebit_length (u : List Bool) : (f2_loopDebit u).1.length = u.length := by
  induction u with
  | nil => rfl
  | cons b u ih => cases b <;> simp [f2_loopDebit, ih]

/-- Little-endian counter value; high zero cells contribute nothing. -/
private def f2_loopValue : List Bool → ℕ
  | [] => 0
  | b :: bs => 2 * f2_loopValue bs + if b then 1 else 0

/-- The fuel machine's binary word has its declared numerical value. -/
private lemma f2_loopValue_bits (n : ℕ) : f2_loopValue n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [f2_loopValue]
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn]
    cases b <;> simp [f2_loopValue, ih, Nat.bit_val]

/-- A successful debit reduces value by one; underflow occurs only at zero.
**Proof sketch.** A low one is cleared immediately. A low zero becomes one
while the inductive debit reduces the higher part; doubling that equation
gives the successor equation for the full word. -/
private lemma f2_loopDebit_value (u : List Bool) :
    if (f2_loopDebit u).2 then f2_loopValue (f2_loopDebit u).1 + 1 = f2_loopValue u
    else f2_loopValue u = 0 := by
  induction u with
  | nil => rfl
  | cons b u ih =>
    cases b with
    | true => simp [f2_loopDebit, f2_loopValue]
    | false =>
      cases h : (f2_loopDebit u).2 <;>
        simp only [f2_loopDebit, h, Bool.false_eq_true, ↓reduceIte,
          f2_loopValue, Nat.add_zero] at ih ⊢ <;> omega

/-- The borrow returns success exactly for positive counter values. -/
private lemma f2_loopDebit_success (u : List Bool) :
    (f2_loopDebit u).2 = true ↔ 0 < f2_loopValue u := by
  have h := f2_loopDebit_value u
  cases hb : (f2_loopDebit u).2
  · simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
    simp [h]
  · simp only [hb, ↓reduceIte] at h
    simp only [true_iff]
    omega

/-- Iterating debit retains the original fixed width at every index. -/
private lemma f2_loopDebit_iterate_length (u : List Bool) (i : ℕ) :
    ((fun w => (f2_loopDebit w).1)^[i] u).length = u.length := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply', f2_loopDebit_length, ih]

/-- Before exhaustion, the counter after `i` debits has value `R-i`.
**Proof sketch.** Start from the fuel word's value. Before the last debit
the induction hypothesis gives a positive value, so the success equation
reduces it by exactly one. No representation is shortened. -/
private lemma f2_loopDebit_iterate_value (R i : ℕ) (hi : i ≤ R) :
    f2_loopValue ((fun w => (f2_loopDebit w).1)^[i] R.bits) = R - i := by
  induction i with
  | zero => simpa using f2_loopValue_bits R
  | succ i ih =>
    have hv := ih (by omega)
    have hs : (f2_loopDebit ((fun w => (f2_loopDebit w).1)^[i] R.bits)).2 = true :=
      (f2_loopDebit_success _).2 (by omega)
    have hd := f2_loopDebit_value ((fun w => (f2_loopDebit w).1)^[i] R.bits)
    simp only [hs, ↓reduceIte] at hd
    rw [Function.iterate_succ_apply']
    omega

/-- Read the first bit of a suffix, with the empty suffix represented by blank. -/
private lemma f2_loopBuffer_read (pre bs : List Bool) :
    bufferTape (pre ++ bs) pre.length = bs.head? := by
  simp only [bufferTape_nat, List.getElem?_append_right (le_refl _), Nat.sub_self]
  cases bs <;> rfl

/-- Writing at the start of a nonempty suffix preserves the prefix and width.
**Proof sketch.** At the write position use the new bit. Before and after
that position both tapes read the same unchanged entries. -/
private lemma f2_loopBuffer_write (pre bs : List Bool) (old new : Bool) :
    Function.update (bufferTape (pre ++ old :: bs)) (pre.length : ℤ) (some new) =
      bufferTape (pre ++ new :: bs) := by
  funext z
  by_cases hz : z = (pre.length : ℤ)
  · subst z; simp
  · rw [Function.update_of_ne hz]
    unfold bufferTape
    by_cases hn : 0 ≤ z
    · simp only [if_pos hn]
      by_cases hl : z.toNat < pre.length
      · rw [List.getElem?_append_left hl, List.getElem?_append_left hl]
      · have hg : pre.length < z.toNat := by omega
        rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
        simp only [List.getElem?_cons, if_neg (by omega : z.toNat - pre.length ≠ 0)]
    · simp only [if_neg hn]

/-- One-tape fixed-width decrement, followed by a rewind. The live states are
borrow (`inl none`), rewind with success flag (`inl (some b)`), and return
(`inr b`). No transition emits physical output. Return states wait for a
surrounding controller. This privately re-derives the counter template. -/
private def f2_loopDebitTM : FinTM Bool where
  k := 1
  State := Option Bool ⊕ Bool
  tm :=
    { q₀ := .inl none
      tr := fun q _ work => match q with
        | .inl none => match work 0 with
          | some false => ⟨0, fun _ => (some (some true), .pos), none, some (.inl none)⟩
          | some true => ⟨0, fun _ => (some (some false), .neg), none, some (.inl (some true))⟩
          | none => ⟨0, fun _ => (none, .neg), none, some (.inl (some false))⟩
        | .inl (some b) => match work 0 with
          | some _ => ⟨0, fun _ => (none, .neg), none, some (.inl (some b))⟩
          | none => ⟨0, fun _ => (none, .pos), none, some (.inr b)⟩
        | .inr b => controlAction 0 (some (.inr b)) }

/-- A candidate on the borrow tape, with arbitrary native input-head position. -/
private def f2_loopDebitCfg (x : List Bool) (p : Fin (x.length + 2))
    (q : Option Bool ⊕ Bool) (z : ℤ) (u : List Bool) :
    Cfg f2_loopDebitTM.k Bool f2_loopDebitTM.State x :=
  ⟨some q, p, fun _ => bufferTape u, fun _ => z, []⟩

/-- One borrow transition writes only inside the fixed-width word, or detects
the right blank without writing to it. -/
private lemma f2_loopBorrow_step (x : List Bool) (p : Fin (x.length + 2))
    (pre bs : List Bool) :
    f2_loopDebitTM.tm.step (f2_loopDebitCfg x p (.inl none) pre.length (pre ++ bs)) =
      match bs with
      | [] => f2_loopDebitCfg x p (.inl (some false)) (pre.length - 1) pre
      | true :: us => f2_loopDebitCfg x p (.inl (some true)) (pre.length - 1) (pre ++ false :: us)
      | false :: us => f2_loopDebitCfg x p (.inl none) (pre.length + 1) (pre ++ true :: us) := by
  unfold MultiTapeTM.step
  change (f2_loopDebitTM.tm.tr (.inl none) _ _).apply _ = _
  simp only [f2_loopDebitTM, f2_loopDebitCfg, Cfg.workTapeSymbols, f2_loopBuffer_read]
  cases bs with
  | nil =>
    refine Cfg.ext rfl (moveInputPos_zero p) ?_ ?_ rfl
    · simp
    · funext i; simp [Action.apply, sub_eq_add_neg]
  | cons b bs =>
    cases b <;> refine Cfg.ext rfl (moveInputPos_zero p) ?_ ?_ rfl
    all_goals first
      | (funext i; exact f2_loopBuffer_write pre bs _ _)
      | (funext i; simp [Action.apply, sub_eq_add_neg])

/-- The borrow phase takes one step beyond the leading false prefix, including
one blank test on underflow.
**Proof sketch.** Induct on the remaining candidate. Each false bit is set
and added to the processed prefix. A true bit or the right blank starts
rewind without changing the width. -/
private lemma f2_loopBorrow_run (x : List Bool) (p : Fin (x.length + 2))
    (u : List Bool) : ∀ pre : List Bool,
    f2_loopDebitTM.tm.runFrom (f2_loopDebitCfg x p (.inl none) pre.length (pre ++ u))
        (f2_loopBorrowPos u + 1) =
      f2_loopDebitCfg x p (.inl (some (f2_loopDebit u).2))
        ((pre.length : ℤ) + f2_loopBorrowPos u - 1) (pre ++ (f2_loopDebit u).1) := by
  induction u with
  | nil =>
    intro pre
    simpa [f2_loopBorrowPos, f2_loopDebit, MultiTapeTM.runFrom_succ_eq_step] using
      f2_loopBorrow_step x p pre []
  | cons b u ih =>
    intro pre
    cases b with
    | true =>
      simpa [f2_loopBorrowPos, f2_loopDebit, MultiTapeTM.runFrom_succ_eq_step] using
        f2_loopBorrow_step x p pre (true :: u)
    | false =>
      simp only [f2_loopBorrowPos]
      rw [MultiTapeTM.runFrom_succ_eq_step, f2_loopBorrow_step]
      simpa [f2_loopDebit, List.append_assoc, Nat.cast_add, Nat.cast_one,
        add_assoc, add_comm, add_left_comm] using ih (pre ++ [true])

/-- Rewind over `j` known candidate cells to the left blank, then return at
cell zero in exactly `j+1` steps, retaining the candidate and success flag. -/
private lemma f2_loopBorrow_rewind (x : List Bool) (p : Fin (x.length + 2))
    (u : List Bool) (b : Bool) : ∀ j, j ≤ u.length →
    f2_loopDebitTM.tm.runFrom (f2_loopDebitCfg x p (.inl (some b)) ((j : ℤ) - 1) u)
        (j + 1) = f2_loopDebitCfg x p (.inr b) 0 u := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    simp only [Nat.cast_zero, zero_sub]
    unfold MultiTapeTM.step
    simp only [f2_loopDebitTM, f2_loopDebitCfg, Cfg.workTapeSymbols, bufferTape_left]
    refine Cfg.ext rfl (moveInputPos_zero p) rfl ?_ rfl
    funext i; simp [Action.apply]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hstep : f2_loopDebitTM.tm.step
        (f2_loopDebitCfg x p (.inl (some b)) ((j + 1 : ℕ) - 1) u) =
          f2_loopDebitCfg x p (.inl (some b)) ((j : ℤ) - 1) u := by
      have hz : ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) := by omega
      rw [hz]
      unfold MultiTapeTM.step
      simp only [f2_loopDebitTM, f2_loopDebitCfg, Cfg.workTapeSymbols, bufferTape_nat,
        List.getElem?_eq_getElem (by omega : j < u.length)]
      refine Cfg.ext rfl (moveInputPos_zero p) rfl ?_ rfl
      funext i; simp [Action.apply, sub_eq_add_neg]
    rw [hstep]
    exact ih (by omega)

/-- A complete fixed-width decrement and rewind costs `2j+2 ≤ 2|u|+2`,
where `j` is the leading false-prefix length. It returns live at cell zero,
retains the input head, and emits nothing. Width zero returns underflow only
when this subroutine is called, so enumeration can process `[]` first. -/
private lemma f2_loopBorrow_correct (x : List Bool) (p : Fin (x.length + 2))
    (u : List Bool) :
    2 * f2_loopBorrowPos u + 2 ≤ 2 * u.length + 2 ∧
      f2_loopDebitTM.tm.runFrom (f2_loopDebitCfg x p (.inl none) 0 u)
          (2 * f2_loopBorrowPos u + 2) =
        f2_loopDebitCfg x p (.inr (f2_loopDebit u).2) 0 (f2_loopDebit u).1 := by
  refine ⟨by have := f2_loopBorrowPos_le u; omega, ?_⟩
  have hr := f2_loopBorrow_run x p u []
  simp only [List.length_nil, Nat.cast_zero, List.nil_append, zero_add] at hr
  rw [show 2 * f2_loopBorrowPos u + 2 = (f2_loopBorrowPos u + 1) + (f2_loopBorrowPos u + 1) by omega,
    MultiTapeTM.runFrom_add, hr]
  exact f2_loopBorrow_rewind x p (f2_loopDebit u).1 (f2_loopDebit u).2 _
    (by rw [f2_loopDebit_length]; exact f2_loopBorrowPos_le u)

/-- Stop the body at the next anchor entry, distinguishing that return from
a genuine source halt on an extra one-cell flag tape. A true release bit
forces one source action, even at the anchor; every source successor clears
the release bit. The body's full output is retained for subsequent capture. -/
private def f2_loopBodyTM (body : FinTM Bool) (anchor : body.State) : FinTM Bool where
  k := body.k + 1
  State := body.State × Bool
  tm :=
    { q₀ := (body.tm.q₀, false)
      tr := fun q inp work =>
        if q.1 = anchor ∧ q.2 = false then
          { inputTape := 0
            workTapes := fun i =>
              if (i : ℕ) < body.k then (none, 0) else (some (some false), 0)
            output := none
            state := none }
        else
          let a := body.tm.tr q.1 inp (fun i => work i.castSucc)
          { inputTape := a.inputTape
            workTapes := fun i =>
              if h : (i : ℕ) < body.k then a.workTapes ⟨i, h⟩
              else (if a.state = none then some (some true) else none, 0)
            output := a.output
            state := a.state.map (fun s => (s, false)) } }

/-- Embed a source configuration with its release bit and the one-cell
halt-kind flag. The flag head stays at the origin throughout a body call. -/
private def f2_loopBodyCfg (body : FinTM Bool) (anchor : body.State) {x : List Bool}
    (c : Cfg body.k Bool body.State x) (release : Bool) (flag : Option Bool) :
    Cfg (f2_loopBodyTM body anchor).k Bool (f2_loopBodyTM body anchor).State x where
  state := c.state.map (fun s => (s, release))
  inputPos := c.inputPos
  workTapes := fun i => if h : (i : ℕ) < body.k then c.workTapes ⟨i, h⟩
    else fun z => if z = 0 then flag else none
  workTapePos := fun i => if h : (i : ℕ) < body.k then c.workTapePos ⟨i, h⟩ else 0
  output := c.output

/-- At an unreleased anchor the stop wrapper takes one silent step and
records rejection, without changing the body's configuration data. -/
private lemma f2_loopBody_stop (body : FinTM Bool) (anchor : body.State) {x : List Bool}
    (c : Cfg body.k Bool body.State x) (hc : c.state = some anchor) (flag : Option Bool) :
    (f2_loopBodyTM body anchor).tm.step (f2_loopBodyCfg body anchor c false flag) =
      f2_loopBodyCfg body anchor {c with state := none} false (some false) := by
  unfold MultiTapeTM.step
  simp only [f2_loopBodyCfg, hc, Option.map_some, f2_loopBodyTM, and_self, ↓reduceIte]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ ?_
  · funext i z
    by_cases hi : (i : ℕ) < body.k
    · simp [Action.apply, hi]
    · simp only [Action.apply, hi, ↓reduceIte]
      by_cases hz : z = 0 <;> simp [hz, hi, Function.update]
  · funext i
    by_cases hi : (i : ℕ) < body.k <;> simp [Action.apply, hi]
  · simp [Action.apply]

/-- Away from an unreleased anchor, the wrapper executes exactly one body
action and records a true flag precisely on a genuine halting transition. -/
private lemma f2_loopBody_step (body : FinTM Bool) (anchor : body.State) {x : List Bool}
    (c : Cfg body.k Bool body.State x) (q : body.State) (release : Bool)
    (flag : Option Bool) (hc : c.state = some q)
    (hgo : ¬(q = anchor ∧ release = false)) :
    (f2_loopBodyTM body anchor).tm.step (f2_loopBodyCfg body anchor c release flag) =
      f2_loopBodyCfg body anchor (body.tm.step c) false
        (if (body.tm.step c).state = none then some true else flag) := by
  let a := body.tm.tr q c.inputSymbol c.workTapeSymbols
  have hb : body.tm.step c = a.apply c := by simp only [MultiTapeTM.step, hc, a]
  rw [hb]
  unfold MultiTapeTM.step
  simp only [f2_loopBodyCfg, hc, Option.map_some, f2_loopBodyTM, hgo, ↓reduceIte]
  have hr : (fun i : Fin body.k =>
      (f2_loopBodyCfg body anchor c release flag).workTapeSymbols i.castSucc) =
        c.workTapeSymbols := by
    funext i
    simp [f2_loopBodyCfg, Cfg.workTapeSymbols, i.isLt]
  change (let a' : Action body.k Bool body.State :=
            body.tm.tr q c.inputSymbol (fun i : Fin body.k =>
              (f2_loopBodyCfg body anchor c release flag).workTapeSymbols i.castSucc);
    ({
      inputTape := a'.inputTape
      workTapes := fun i => if h : (i : ℕ) < body.k then a'.workTapes ⟨i, h⟩
        else (if a'.state = none then some (some true) else none, 0)
      output := a'.output
      state := a'.state.map (fun s => (s, false)) } :
        Action (body.k + 1) Bool (body.State × Bool))).apply _ = _
  rw [hr]
  dsimp only
  dsimp only [a] at *
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i z
    by_cases hi : (i : ℕ) < body.k
    · simp [Action.apply, hi]
    · by_cases ha : (body.tm.tr q c.inputSymbol c.workTapeSymbols).state = none
      · simp only [Action.apply, hi, ↓reduceDIte, ha, ↓reduceIte]
        by_cases hz : z = 0 <;> simp [hz, hi, Function.update]
      · simp [Action.apply, hi, ha]
  · funext i
    by_cases hi : (i : ℕ) < body.k <;> simp [Action.apply, hi]

/-- Up to the first halt or anchor return, the stop wrapper simulates the
body exactly. The release flag is consumed by the first action.
**Proof sketch.** Induct on elapsed time. Strict liveness supplies a source
state; the no-anchor condition, except for the released first action,
enables the one-step lemma. Its flag update records a halting emission's
transition without discarding that emission. -/
private lemma f2_loopBody_run (body : FinTM Bool) (anchor : body.State) {x : List Bool}
    (c : Cfg body.k Bool body.State x) (release : Bool) (hc : c.state ≠ none)
    (t : ℕ) (hlive : ∀ u < t, (body.tm.runFrom c u).state ≠ none)
    (hanchor : ∀ u < t, (u = 0 ∧ release = true) ∨
      (body.tm.runFrom c u).state ≠ some anchor) :
    (f2_loopBodyTM body anchor).tm.runFrom (f2_loopBodyCfg body anchor c release none) t =
      f2_loopBodyCfg body anchor (body.tm.runFrom c t) (if t = 0 then release else false)
        (if (body.tm.runFrom c t).state = none then some true else none) := by
  induction t with
  | zero => simp [hc]
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step']
    rw [ih (fun u hu => hlive u (by omega)) (fun u hu => hanchor u (by omega))]
    have ht := hlive t (by omega)
    obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp ht
    have hgo : ¬(q = anchor ∧ (if t = 0 then release else false) = false) := by
      rcases hanchor t (by omega) with ⟨hz, hr⟩ | hn
      · simp [hz, hr]
      · rintro ⟨rfl, _⟩
        exact hn hq
    rw [if_neg ht, f2_loopBody_step body anchor _ q _ none hq hgo]
    simp only [Nat.succ_ne_zero, ↓reduceIte, MultiTapeTM.runFrom_succ_eq_step']

/-- W1 captures the stopped body's complete trace in any agreeing controller.
This includes an output bit emitted by the halting transition.
**Proof sketch.** The preceding simulation gives strict liveness of the
stop wrapper before the endpoint. Apply the audited capture contract with
the supplied controller as host, then substitute the simulated endpoint. -/
private lemma f2_loopBody_capture (body : FinTM Bool) (anchor : body.State)
    {H : Type*} {x : List Bool} (host : MultiTapeTM (body.k + 1 + 1) Bool H)
    (emb : body.State × Bool → H) (ret : H)
    (hagree : ∀ s inp work, host.tr (emb s) inp work =
      captureAction emb ret ((f2_loopBodyTM body anchor).tm.tr s inp fun i => work i.castSucc))
    (c : Cfg body.k Bool body.State x) (release : Bool) (hc : c.state ≠ none)
    (t : ℕ) (hlive : ∀ u < t, (body.tm.runFrom c u).state ≠ none)
    (hanchor : ∀ u < t, (u = 0 ∧ release = true) ∨
      (body.tm.runFrom c u).state ≠ some anchor) :
    host.runFrom (captureCfg emb ret [] [] (f2_loopBodyCfg body anchor c release none)) t =
      captureCfg emb ret [] []
        (f2_loopBodyCfg body anchor (body.tm.runFrom c t) (if t = 0 then release else false)
          (if (body.tm.runFrom c t).state = none then some true else none)) := by
  have hguard : ∀ u < t,
      ¬((f2_loopBodyTM body anchor).tm.runFrom (f2_loopBodyCfg body anchor c release none) u).Halted := by
    intro u hu
    rw [f2_loopBody_run body anchor c release hc u
      (fun v hv => hlive v (by omega)) (fun v hv => hanchor v (by omega))]
    simpa [Cfg.Halted, f2_loopBodyCfg] using hlive u hu
  rw [capture_run (f2_loopBodyTM body anchor).tm host emb ret hagree [] [] _ t hguard,
    f2_loopBody_run body anchor c release hc t hlive hanchor]

/-- Disjoint finite control for fuel, body calls, and fourteen controller phases. -/
private abbrev f2_LoopHostState (body F : FinTM Bool) :=
  F.State ⊕ ((Bool × (body.State × Bool)) ⊕ Fin 14)

/-- Relocate the fuel machine past the untouched body, flag, and counter tapes. -/
private def f2_loopFuelSource (body F : FinTM Bool) :
    MultiTapeTM (body.k + 1 + (1 + F.k)) Bool F.State where
  q₀ := F.tm.q₀
  tr := fun q inp work =>
    rightAction (body.k + 1) id (rightAction 1 id
      (F.tm.tr q inp fun i => work (Fin.natAdd (body.k + 1) (Fin.natAdd 1 i))))

/-- Extend the stopped body with a preserved counter and the fuel-phase residue. -/
private def f2_loopBodySource (body F : FinTM Bool) (anchor : body.State) :
    MultiTapeTM (body.k + 1 + (1 + F.k)) Bool (body.State × Bool) where
  q₀ := (body.tm.q₀, false)
  tr := fun q inp work => leftAction (1 + F.k) id
    ((f2_loopBodyTM body anchor).tm.tr q inp fun i => work (Fin.castAdd (1 + F.k) i))

/-- A controller action touches only the flag, counter, and capture tapes. -/
private def f2_loopControlAction (body F : FinTM Bool) (inp : SignType)
    (flag : Option (Option Bool)) (counter payload : Option (Option Bool) × SignType)
    (out : Option Bool) (next : Option (f2_LoopHostState body F)) :
    Action (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) where
  inputTape := inp
  workTapes := fun i =>
    if (i : ℕ) = body.k then (flag, 0)
    else if (i : ℕ) = body.k + 1 then counter
    else if (i : ℕ) = body.k + 1 + (1 + F.k) then payload
    else (none, 0)
  output := out
  state := next

/-- Concrete loop controller, with fixed-verdict and payload-replay modes.
Fuel is captured, rewound, copied into the fixed-width counter while the
capture tape is cleared, and both heads are rewound together. Two further
phases rewind the native input before starting the body. Body startup and
active rounds have disjoint return states; only an active rejection debits.
The release bit forces one body action before another anchor is recognized.

Control phases: 0/1 fuel rewind; 2 counter copy; 3 counter/capture rewind;
4/5 input rewind; 6 startup return; 7 round return; 8 borrow; 9/10 successful
and underflow rewinds; 11 exhaustion; 12/13 payload rewind and replay.
The fuel work tapes are never cleared or reused after the fuel phase. -/
private def f2_loopHost (body F : FinTM Bool) (anchor : body.State) (findMode : Bool) :
    FinTM Bool where
  k := body.k + 1 + (1 + F.k) + 1
  State := f2_LoopHostState body F
  tm :=
    { q₀ := .inl F.tm.q₀
      tr := fun q inp work =>
        let ctrl (j : Fin 14) : f2_LoopHostState body F := .inr (.inr j)
        let call (startup : Bool) (s : body.State × Bool) : f2_LoopHostState body F :=
          .inr (.inl (startup, s))
        let flag : Fin (body.k + 1 + (1 + F.k) + 1) := ⟨body.k, by omega⟩
        let counter : Fin (body.k + 1 + (1 + F.k) + 1) := ⟨body.k + 1, by omega⟩
        let payload := Fin.last (body.k + 1 + (1 + F.k))
        let act := f2_loopControlAction body F
        match q with
        | .inl s => captureAction Sum.inl (ctrl 0)
            ((f2_loopFuelSource body F).tr s inp fun i => work i.castSucc)
        | .inr (.inl (startup, s)) =>
            captureAction (call startup) (ctrl (if startup then 6 else 7))
              ((f2_loopBodySource body F anchor).tr s inp fun i => work i.castSucc)
        | .inr (.inr phase) =>
            if phase = 0 then act 0 none (none, 0) (none, .neg) none (some (ctrl 1))
            else if phase = 1 then
              match work payload with
              | some _ => act 0 none (none, 0) (none, .neg) none (some (ctrl 1))
              | none => act 0 none (none, 0) (none, .pos) none (some (ctrl 2))
            else if phase = 2 then
              match work payload with
              | some b => act 0 none (some (some b), .pos) (some none, .pos) none
                  (some (ctrl 2))
              | none => act 0 none (none, .neg) (none, .neg) none (some (ctrl 3))
            else if phase = 3 then
              match work counter with
              | some _ => act 0 none (none, .neg) (none, .neg) none (some (ctrl 3))
              | none => act 0 none (none, .pos) (none, .pos) none (some (ctrl 4))
            else if phase = 4 then act .neg none (none, 0) (none, 0) none (some (ctrl 5))
            else if phase = 5 then
              match inp with
              | some _ => act .neg none (none, 0) (none, 0) none (some (ctrl 5))
              | none => act .pos none (none, 0) (none, 0) none
                  (some (call true (body.tm.q₀, false)))
            else if phase = 6 then act 0 (some none) (none, 0) (none, 0) none
              (some (call false (anchor, true)))
            else if phase = 7 then
              if work flag = some true then
                if findMode then act 0 none (none, 0) (none, .neg) none (some (ctrl 12))
                else act 0 none (none, 0) (none, 0) (some true) none
              else act 0 (some none) (none, 0) (none, 0) none (some (ctrl 8))
            else if phase = 8 then
              match work counter with
              | some false => act 0 none (some (some true), .pos) (none, 0) none
                  (some (ctrl 8))
              | some true => act 0 none (some (some false), .neg) (none, 0) none
                  (some (ctrl 9))
              | none => act 0 none (none, .neg) (none, 0) none (some (ctrl 10))
            else if phase = 9 then
              match work counter with
              | some _ => act 0 none (none, .neg) (none, 0) none (some (ctrl 9))
              | none => act 0 none (none, .pos) (none, 0) none
                  (some (call false (anchor, true)))
            else if phase = 10 then
              match work counter with
              | some _ => act 0 none (none, .neg) (none, 0) none (some (ctrl 10))
              | none => act 0 none (none, .pos) (none, 0) none (some (ctrl 11))
            else if phase = 11 then
              act 0 none (none, 0) (none, 0) (if findMode then none else some false) none
            else if phase = 12 then
              match work payload with
              | some _ => act 0 none (none, 0) (none, .neg) none (some (ctrl 12))
              | none => act 0 none (none, 0) (none, .pos) none (some (ctrl 13))
            else
              match work payload with
              | some b => act 0 none (none, 0) (none, .pos) (some b) (some (ctrl 13))
              | none => act 0 none (none, 0) (none, 0) none none }

/-- The concrete host's body states agree with W1 on the entire source table;
startup and active calls return to distinct controller phases. -/
private lemma f2_loopHost_body_capture (body F : FinTM Bool) (anchor : body.State)
    (findMode startup : Bool) {x : List Bool}
    (c : Cfg (body.k + 1 + (1 + F.k)) Bool (body.State × Bool) x) (t : ℕ)
    (hlive : ∀ u < t, ¬((f2_loopBodySource body F anchor).runFrom c u).Halted) :
    (f2_loopHost body F anchor findMode).tm.runFrom
        (captureCfg (fun s => Sum.inr (Sum.inl (startup, s)))
          (Sum.inr (Sum.inr (if startup then 6 else 7 : Fin 14))) [] [] c) t =
      captureCfg (fun s => Sum.inr (Sum.inl (startup, s)))
        (Sum.inr (Sum.inr (if startup then 6 else 7 : Fin 14))) [] []
        ((f2_loopBodySource body F anchor).runFrom c t) := by
  exact capture_run (f2_loopBodySource body F anchor) (f2_loopHost body F anchor findMode).tm
    _ _ (by intro s inp work; rfl) [] [] c t hlive

/-- The fuel states capture all fuel emissions directly in the concrete host. -/
private lemma f2_loopHost_fuel_capture (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (c : Cfg (body.k + 1 + (1 + F.k)) Bool F.State x) (t : ℕ)
    (hlive : ∀ u < t, ¬((f2_loopFuelSource body F).runFrom c u).Halted) :
    (f2_loopHost body F anchor findMode).tm.runFrom
        (captureCfg Sum.inl (Sum.inr (Sum.inr (0 : Fin 14))) [] [] c) t =
      captureCfg Sum.inl (Sum.inr (Sum.inr (0 : Fin 14))) [] []
        ((f2_loopFuelSource body F).runFrom c t) := by
  exact capture_run (f2_loopFuelSource body F) (f2_loopHost body F anchor findMode).tm
    _ _ (by intro s inp work; rfl) [] [] c t hlive

/-- The fuel capture starts at the host's genuine blank initial configuration. -/
private lemma f2_loopHost_init (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) (x : List Bool) :
    (f2_loopHost body F anchor findMode).tm.initCfg x =
      captureCfg Sum.inl (Sum.inr (Sum.inr (0 : Fin 14))) [] []
        ((f2_loopFuelSource body F).initCfg x) := by
  rw [initCfg_ofWords, initCfg_ofWords]
  simp [Cfg.ofWords, captureCfg, f2_loopHost, f2_loopFuelSource]

/-- With no track operations, a controller action is the standard input-only action. -/
private lemma f2_loopControl_idle (body F : FinTM Bool) (inp : SignType)
    (next : Option (f2_LoopHostState body F)) :
    f2_loopControlAction body F inp none (none, 0) (none, 0) none next =
      controlAction inp next := by
  simp [f2_loopControlAction, controlAction]

/-- Host phases 4 and 5 rewind the native input in bounded time, retaining
all tapes, heads, and output, then dispatch to genuine body startup. -/
private lemma f2_loopHost_input_rewind (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (cfg : Cfg (f2_loopHost body F anchor findMode).k Bool (f2_loopHost body F anchor findMode).State x)
    (hs : cfg.state = some (.inr (.inr (4 : Fin 14)))) :
    ∃ t ≤ cfg.inputPos.val + 2,
      (f2_loopHost body F anchor findMode).tm.runFrom cfg t =
        {cfg with state := some (.inr (.inl (true, (body.tm.q₀, false)))), inputPos := 1} := by
  apply f2_loop_rewind_bounded (f2_loopHost body F anchor findMode).tm
    (.inr (.inr 4)) (.inr (.inr 5)) (.some (.inr (.inl (true, (body.tm.q₀, false)))))
    ?_ ?_ cfg hs
  · intro inp work
    exact f2_loopControl_idle body F .neg _
  · intro inp work
    cases inp <;> exact f2_loopControl_idle body F _ _

/-- A controller configuration with arbitrary preserved body/fuel residue.
Only the flag, counter, and capture tracks are replaced by the parameters. -/
private def f2_loopFrame (body F : FinTM Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x)
    (q : Option (f2_LoopHostState body F)) (p : Fin (x.length + 2))
    (flag counter payload : ℤ → Option Bool) (ch ph : ℤ) (out : List Bool) :
    Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x where
  state := q
  inputPos := p
  workTapes := fun i =>
    if (i : ℕ) = body.k then flag
    else if (i : ℕ) = body.k + 1 then counter
    else if (i : ℕ) = body.k + 1 + (1 + F.k) then payload
    else base.workTapes i
  workTapePos := fun i =>
    if (i : ℕ) = body.k then 0
    else if (i : ℕ) = body.k + 1 then ch
    else if (i : ℕ) = body.k + 1 + (1 + F.k) then ph
    else base.workTapePos i
  output := out

/-- Optional writes update exactly their current cell. -/
private def f2_loopWrite (tape : ℤ → Option Bool) (head : ℤ) :
    Option (Option Bool) → ℤ → Option Bool
  | none => tape
  | some symbol => Function.update tape head symbol

/-- Controller actions preserve the inactive frame and perform precisely
the three declared track operations. -/
private lemma f2_loopControl_apply (body F : FinTM Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x)
    (q : Option (f2_LoopHostState body F)) (p : Fin (x.length + 2))
    (flag counter payload : ℤ → Option Bool) (ch ph : ℤ) (out : List Bool)
    (inp : SignType) (fw : Option (Option Bool))
    (ca pa : Option (Option Bool) × SignType) (emit : Option Bool)
    (next : Option (f2_LoopHostState body F)) :
    (f2_loopControlAction body F inp fw ca pa emit next).apply
        (f2_loopFrame body F base q p flag counter payload ch ph out) =
      f2_loopFrame body F base next (moveInputPos p inp)
        (f2_loopWrite flag 0 fw) (f2_loopWrite counter ch ca.1) (f2_loopWrite payload ph pa.1)
        (ch + ca.2) (ph + pa.2) (out ++ emit.toList) := by
  have hcf : body.k + 1 ≠ body.k := by omega
  have hpf : body.k + 1 + (1 + F.k) ≠ body.k := by omega
  have hpc : body.k + 1 + (1 + F.k) ≠ body.k + 1 := by omega
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    by_cases hf : (i : ℕ) = body.k
    · simp only [Action.apply, f2_loopControlAction, f2_loopFrame, hf, ↓reduceIte]
      cases fw <;> rfl
    · by_cases hc : (i : ℕ) = body.k + 1
      · simp only [Action.apply, f2_loopControlAction, f2_loopFrame, hc, hcf, ↓reduceIte]
        cases ca.1 <;> rfl
      · by_cases hp : (i : ℕ) = body.k + 1 + (1 + F.k)
        · simp only [Action.apply, f2_loopControlAction, f2_loopFrame, hp, hpf, hpc, ↓reduceIte]
          cases pa.1 <;> rfl
        · simp [Action.apply, f2_loopControlAction, f2_loopFrame, hf, hc, hp]
  · funext i
    by_cases hf : (i : ℕ) = body.k
    · simp [Action.apply, f2_loopControlAction, f2_loopFrame, hf]
    · by_cases hc : (i : ℕ) = body.k + 1
      · simp [Action.apply, f2_loopControlAction, f2_loopFrame, hc]
      · by_cases hp : (i : ℕ) = body.k + 1 + (1 + F.k) <;>
          simp [Action.apply, f2_loopControlAction, f2_loopFrame, hf, hc, hp, hpf]

/-- One-tape payload replay: emit each stored bit, then halt on the right blank. -/
private def f2_loopReplayTM : FinTM Bool where
  k := 1
  State := Unit
  tm :=
    { q₀ := ()
      tr := fun _ _ work => match work 0 with
        | some b => ⟨0, fun _ => (none, .pos), some b, some ()⟩
        | none => ⟨0, fun _ => (none, 0), none, none⟩ }

/-- Replay configuration with arbitrary input position and output prefix. -/
private def f2_loopReplayCfg (x : List Bool) (p : Fin (x.length + 2))
    (q : Option Unit) (z : ℤ) (word out : List Bool) : Cfg 1 Bool Unit x :=
  ⟨q, p, fun _ => bufferTape word, fun _ => z, out⟩

/-- A replay step emits the current bit without modifying the captured word;
at the right blank it halts without an additional bit. -/
private lemma f2_loopReplay_step (x : List Bool) (p : Fin (x.length + 2))
    (pre rest out : List Bool) :
    f2_loopReplayTM.tm.step (f2_loopReplayCfg x p (some ()) pre.length (pre ++ rest) out) =
      match rest with
      | [] => f2_loopReplayCfg x p none pre.length pre out
      | b :: bs => f2_loopReplayCfg x p (some ()) (pre.length + 1) (pre ++ b :: bs) (out ++ [b]) := by
  unfold MultiTapeTM.step
  change (f2_loopReplayTM.tm.tr () _ _).apply _ = _
  simp only [f2_loopReplayTM, f2_loopReplayCfg, Cfg.workTapeSymbols, f2_loopBuffer_read]
  cases rest with
  | nil =>
    refine Cfg.ext rfl (moveInputPos_zero p) ?_ ?_ ?_
    · simp
    · funext i; simp [Action.apply]
    · simp [Action.apply]
  | cons b rest =>
    refine Cfg.ext rfl (moveInputPos_zero p) rfl ?_ rfl
    funext i; simp [Action.apply]

/-- Replay emits exactly the remaining payload in its length plus one steps,
including an empty payload.
**Proof sketch.** Induct on the unprocessed suffix. The step lemma emits
one bit and moves the frontier; the empty suffix supplies the final blank
test. Concatenation associativity preserves the exact output order. -/
private lemma f2_loopReplay_run (x : List Bool) (p : Fin (x.length + 2))
    (rest : List Bool) : ∀ pre out : List Bool,
    f2_loopReplayTM.tm.runFrom (f2_loopReplayCfg x p (some ()) pre.length (pre ++ rest) out)
        (rest.length + 1) =
      f2_loopReplayCfg x p none (pre ++ rest).length (pre ++ rest) (out ++ rest) := by
  induction rest with
  | nil =>
    intro pre out
    simpa [MultiTapeTM.runFrom_succ_eq_step] using f2_loopReplay_step x p pre [] out
  | cons b rest ih =>
    intro pre out
    rw [List.length_cons, MultiTapeTM.runFrom_succ_eq_step, f2_loopReplay_step]
    simpa [List.append_assoc, List.length_append, List.length_cons, Nat.cast_add,
      Nat.cast_one, add_assoc, add_comm, add_left_comm] using ih (pre ++ [b]) (out ++ [b])

/-- A payload-only controller action is the right-block action extension. -/
private lemma f2_loopControl_payload (body F : FinTM Bool) (d : SignType)
    (out : Option Bool) (next : Option (f2_LoopHostState body F)) :
    f2_loopControlAction body F 0 none (none, 0) (none, d) out next =
      rightAction (body.k + 1 + (1 + F.k)) id
        (⟨0, fun _ : Fin 1 => (none, d), out, next⟩ : Action 1 Bool (f2_LoopHostState body F)) := by
  simp only [f2_loopControlAction, rightAction, Option.map_id]
  congr 1
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    have hj : (j : ℕ) ≠ body.k + 1 + (1 + F.k) := Nat.ne_of_lt j.isLt
    simp [hj]
  · intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    have hf : body.k + 1 + (1 + F.k) ≠ body.k := by omega
    simp [hf]

/-- Phase 13 replays the captured payload in the actual host, preserving
the arbitrary completed body/fuel tapes. -/
private lemma f2_loopHost_replay (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) (x : List Bool) (p : Fin (x.length + 2)) (word out : List Bool)
    (tapes : Fin (body.k + 1 + (1 + F.k)) → ℤ → Option Bool)
    (heads : Fin (body.k + 1 + (1 + F.k)) → ℤ) :
    (f2_loopHost body F anchor findMode).tm.runFrom
        (rightCfg (fun _ : Unit => Sum.inr (Sum.inr (13 : Fin 14)))
          (f2_loopReplayCfg x p (some ()) 0 word out) tapes heads) (word.length + 1) =
      rightCfg (fun _ : Unit => Sum.inr (Sum.inr (13 : Fin 14)))
        (f2_loopReplayCfg x p none word.length word (out ++ word)) tapes heads := by
  have htr : ∀ q inp work,
      (f2_loopHost body F anchor findMode).tm.tr (.inr (.inr (13 : Fin 14))) inp work =
        rightAction (body.k + 1 + (1 + F.k))
          (fun _ : Unit => Sum.inr (Sum.inr (13 : Fin 14)))
          (f2_loopReplayTM.tm.tr q inp fun i => work (Fin.natAdd (body.k + 1 + (1 + F.k)) i)) := by
    intro q inp work
    cases q
    change (match work (Fin.last (body.k + 1 + (1 + F.k))) with
      | some b => f2_loopControlAction body F 0 none (none, 0) (none, .pos) (some b)
          (some (.inr (.inr 13)))
      | none => f2_loopControlAction body F 0 none (none, 0) (none, 0) none none) = _
    cases hw : work (Fin.last (body.k + 1 + (1 + F.k)))
    · simpa only [f2_loopReplayTM, show Fin.natAdd (body.k + 1 + (1 + F.k)) (0 : Fin 1) =
          Fin.last (body.k + 1 + (1 + F.k)) from rfl, hw] using
        f2_loopControl_payload body F 0 none none
    · simpa only [f2_loopReplayTM, show Fin.natAdd (body.k + 1 + (1 + F.k)) (0 : Fin 1) =
          Fin.last (body.k + 1 + (1 + F.k)) from rfl, hw] using
        f2_loopControl_payload body F .pos _ _
  refine (rightCfg_run (k := body.k + 1 + (1 + F.k)) (l := 1)
    f2_loopReplayTM.tm (f2_loopHost body F anchor findMode).tm
    (fun _ : Unit => Sum.inr (Sum.inr (13 : Fin 14))) htr
    (f2_loopReplayCfg x p (some ()) 0 word out) tapes heads (word.length + 1)).trans ?_
  have hr := f2_loopReplay_run x p word [] out
  simpa using congrArg
    (fun c => rightCfg (fun _ : Unit => Sum.inr (Sum.inr (13 : Fin 14))) c tapes heads) hr

/-- The fuel configuration on its relocated block, with the body, flag, and
counter still blank. The completed fuel residue is retained by this embedding. -/
private def f2_loopFuelCfg (body F : FinTM Bool) {x : List Bool}
    (c : Cfg F.k Bool F.State x) :
    Cfg (body.k + 1 + (1 + F.k)) Bool F.State x :=
  rightCfg id (rightCfg id c (fun (_ : Fin 1) _ => none) (fun _ => 0))
    (fun (_ : Fin (body.k + 1)) _ => none) (fun _ => 0)

/-- Relocating fuel through the counter and body blocks preserves every run.
**Proof sketch.** Apply the right-block simulation twice. Each inactive block
has its own blank tapes and origin heads, retained throughout the source run. -/
private lemma f2_loopFuel_run (body F : FinTM Bool) {x : List Bool}
    (c : Cfg F.k Bool F.State x) (t : ℕ) :
    (f2_loopFuelSource body F).runFrom (f2_loopFuelCfg body F c) t =
      f2_loopFuelCfg body F (F.tm.runFrom c t) := by
  let pad : MultiTapeTM (1 + F.k) Bool F.State :=
    { q₀ := F.tm.q₀
      tr := fun q inp work => rightAction 1 id
        (F.tm.tr q inp (fun i => work (Fin.natAdd 1 i))) }
  unfold f2_loopFuelCfg
  rw [rightCfg_run pad (f2_loopFuelSource body F) id (fun _ _ _ => rfl),
    rightCfg_run F.tm pad id (fun _ _ _ => rfl)]

/-- The relocated fuel source begins at its genuine blank configuration. -/
private lemma f2_loopFuel_init (body F : FinTM Bool) (x : List Bool) :
    (f2_loopFuelSource body F).initCfg x = f2_loopFuelCfg body F (F.tm.initCfg x) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [f2_loopFuelCfg, rightCfg, MultiTapeTM.initCfg, Cfg.init]
    · intro j
      refine Fin.addCases ?_ ?_ j <;> intro k <;>
        simp [f2_loopFuelCfg, rightCfg, MultiTapeTM.initCfg, Cfg.init]
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [f2_loopFuelCfg, rightCfg, MultiTapeTM.initCfg, Cfg.init]
    · intro j
      refine Fin.addCases ?_ ?_ j <;> intro k <;>
        simp [f2_loopFuelCfg, rightCfg, MultiTapeTM.initCfg, Cfg.init]

/-- The capture track of a frame reads precisely its parameterized tape. -/
private lemma f2_loopFrame_payload (body F : FinTM Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x)
    (q : Option (f2_LoopHostState body F)) (p : Fin (x.length + 2))
    (flag counter payload : ℤ → Option Bool) (ch ph : ℤ) (out : List Bool) :
    (f2_loopFrame body F base q p flag counter payload ch ph out).workTapeSymbols
        (Fin.last (body.k + 1 + (1 + F.k))) = payload ph := by
  have hf : body.k + 1 + (1 + F.k) ≠ body.k := by omega
  simp [f2_loopFrame, Cfg.workTapeSymbols, hf]

/-- The counter track of a frame reads precisely its parameterized tape. -/
private lemma f2_loopFrame_counter (body F : FinTM Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x)
    (q : Option (f2_LoopHostState body F)) (p : Fin (x.length + 2))
    (flag counter payload : ℤ → Option Bool) (ch ph : ℤ) (out : List Bool) :
    (f2_loopFrame body F base q p flag counter payload ch ph out).workTapeSymbols
        ⟨body.k + 1, by omega⟩ = counter ch := by
  simp [f2_loopFrame, Cfg.workTapeSymbols]

/-- Fuel-rewind phase 1 scans to the left blank and returns at the origin.
**Proof sketch.** Induct on the number of stored cells to the left. At zero,
the head is on the left blank; otherwise its cell is nonblank and the left
move reduces that number. All other tracks and the native input are retained. -/
private lemma f2_loopHost_fuel_rewind (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x)
    (p : Fin (x.length + 2)) (flag counter : ℤ → Option Bool)
    (ch : ℤ) (word out : List Bool) : ∀ j, j ≤ word.length →
    (f2_loopHost body F anchor findMode).tm.runFrom
        (f2_loopFrame body F base (some (.inr (.inr 1))) p flag counter
          (bufferTape word) ch ((j : ℤ) - 1) out) (j + 1) =
      f2_loopFrame body F base (some (.inr (.inr 2))) p flag counter
        (bufferTape word) ch 0 out := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    change (match (f2_loopFrame body F base (some (.inr (.inr 1))) p flag counter
        (bufferTape word) ch ((0 : ℤ) - 1) out).workTapeSymbols
          (Fin.last (body.k + 1 + (1 + F.k))) with
      | some _ => f2_loopControlAction body F 0 none (none, 0) (none, .neg) none
          (some (.inr (.inr 1)))
      | none => f2_loopControlAction body F 0 none (none, 0) (none, .pos) none
          (some (.inr (.inr 2)))).apply _ = _
    rw [f2_loopFrame_payload]
    simp only [zero_sub, bufferTape_left]
    rw [f2_loopControl_apply]
    simp [f2_loopWrite]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hs : (f2_loopHost body F anchor findMode).tm.step
        (f2_loopFrame body F base (some (.inr (.inr 1))) p flag counter
          (bufferTape word) ch (((j + 1 : ℕ) : ℤ) - 1) out) =
        f2_loopFrame body F base (some (.inr (.inr 1))) p flag counter
          (bufferTape word) ch ((j : ℤ) - 1) out := by
      change (match (f2_loopFrame body F base (some (.inr (.inr 1))) p flag counter
          (bufferTape word) ch (((j + 1 : ℕ) : ℤ) - 1) out).workTapeSymbols
            (Fin.last (body.k + 1 + (1 + F.k))) with
        | some _ => f2_loopControlAction body F 0 none (none, 0) (none, .neg) none
            (some (.inr (.inr 1)))
        | none => f2_loopControlAction body F 0 none (none, 0) (none, .pos) none
            (some (.inr (.inr 2)))).apply _ = _
      rw [f2_loopFrame_payload]
      rw [show ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) by omega,
        bufferTape_nat, List.getElem?_eq_getElem (by omega : j < word.length)]
      rw [f2_loopControl_apply]
      simp [f2_loopWrite, sub_eq_add_neg]
    rw [hs]
    exact ih (by omega)

/-- During fuel copying, the processed prefix of the capture tape is blank. -/
private def f2_loopCopyTape (pre rest : List Bool) (z : ℤ) : Option Bool :=
  if z < pre.length then none else bufferTape (pre ++ rest) z

/-- The copying frontier reads the first bit of the remaining suffix. -/
private lemma f2_loopCopy_read (pre rest : List Bool) :
    f2_loopCopyTape pre rest pre.length = rest.head? := by
  simp only [f2_loopCopyTape, lt_self_iff_false, ↓reduceIte, f2_loopBuffer_read]

/-- Clearing one fuel cell extends the already-cleared prefix by that bit. -/
private lemma f2_loopCopy_erase (pre rest : List Bool) (b : Bool) :
    Function.update (f2_loopCopyTape pre (b :: rest)) (pre.length : ℤ) none =
      f2_loopCopyTape (pre ++ [b]) rest := by
  funext z
  by_cases hz : z = pre.length
  · subst z; simp [f2_loopCopyTape]
  · rw [Function.update_of_ne hz]
    have hlt : z < (pre.length : ℤ) ↔ z < ((pre ++ [b]).length : ℤ) := by
      simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
      omega
    simp only [f2_loopCopyTape, hlt, List.append_assoc, List.singleton_append]

/-- Before copying begins the capture tape is the original fuel buffer. -/
private lemma f2_loopCopy_initial (word : List Bool) :
    f2_loopCopyTape [] word = bufferTape word := by
  funext z
  by_cases hz : z < 0
  · simp [f2_loopCopyTape, bufferTape, hz, show ¬0 ≤ z by omega]
  · simp [f2_loopCopyTape, hz]

/-- After copying ends the capture tape is completely blank. -/
private lemma f2_loopCopy_final (word : List Bool) :
    f2_loopCopyTape word [] = bufferTape [] := by
  funext z
  by_cases hz : z < word.length
  · simp [f2_loopCopyTape, hz]
  · have hn : 0 ≤ z := by omega
    simp [f2_loopCopyTape, hz, bufferTape, hn]

/-- Phase 2 copies the remaining fuel bits to the counter, clearing each
captured bit, then starts the synchronized rewind.
**Proof sketch.** Induct on the uncopied suffix. A nonempty suffix writes
its head at the counter's right blank, clears the corresponding payload
cell, and advances both heads. The empty suffix detects the right blank
and moves both heads left once, including when the original word is empty. -/
private lemma f2_loopHost_fuel_copy (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x)
    (p : Fin (x.length + 2)) (flag : ℤ → Option Bool) (out : List Bool)
    (rest : List Bool) : ∀ pre,
    (f2_loopHost body F anchor findMode).tm.runFrom
        (f2_loopFrame body F base (some (.inr (.inr 2))) p flag (bufferTape pre)
          (f2_loopCopyTape pre rest) pre.length pre.length out) (rest.length + 1) =
      f2_loopFrame body F base (some (.inr (.inr 3))) p flag (bufferTape (pre ++ rest))
        (bufferTape []) ((pre ++ rest).length - 1) ((pre ++ rest).length - 1) out := by
  induction rest with
  | nil =>
    intro pre
    rw [List.length_nil, MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    change (match (f2_loopFrame body F base (some (.inr (.inr 2))) p flag (bufferTape pre)
        (f2_loopCopyTape pre []) pre.length pre.length out).workTapeSymbols
          (Fin.last (body.k + 1 + (1 + F.k))) with
      | some b => f2_loopControlAction body F 0 none (some (some b), .pos)
          (some none, .pos) none (some (.inr (.inr 2)))
      | none => f2_loopControlAction body F 0 none (none, .neg) (none, .neg) none
          (some (.inr (.inr 3)))).apply _ = _
    rw [f2_loopFrame_payload, f2_loopCopy_read]
    dsimp only [List.head?]
    rw [f2_loopControl_apply]
    simp [f2_loopWrite, f2_loopCopy_final, sub_eq_add_neg]
  | cons b rest ih =>
    intro pre
    rw [List.length_cons, MultiTapeTM.runFrom_succ_eq_step]
    have hs : (f2_loopHost body F anchor findMode).tm.step
        (f2_loopFrame body F base (some (.inr (.inr 2))) p flag (bufferTape pre)
          (f2_loopCopyTape pre (b :: rest)) pre.length pre.length out) =
        f2_loopFrame body F base (some (.inr (.inr 2))) p flag (bufferTape (pre ++ [b]))
          (f2_loopCopyTape (pre ++ [b]) rest) (pre ++ [b]).length (pre ++ [b]).length out := by
      change (match (f2_loopFrame body F base (some (.inr (.inr 2))) p flag (bufferTape pre)
          (f2_loopCopyTape pre (b :: rest)) pre.length pre.length out).workTapeSymbols
            (Fin.last (body.k + 1 + (1 + F.k))) with
        | some bit => f2_loopControlAction body F 0 none (some (some bit), .pos)
            (some none, .pos) none (some (.inr (.inr 2)))
        | none => f2_loopControlAction body F 0 none (none, .neg) (none, .neg) none
            (some (.inr (.inr 3)))).apply _ = _
      rw [f2_loopFrame_payload, f2_loopCopy_read]
      dsimp only [List.head?]
      rw [f2_loopControl_apply]
      simp [f2_loopWrite, f2_loopCopy_erase, bufferTape_append]
    rw [hs]
    simpa [List.append_assoc] using ih (pre ++ [b])

/-- Phase 3 rewinds counter and cleared capture heads together.
**Proof sketch.** Induct on the number of counter cells to the left. Both
heads take the same moves; only the counter is read, so the already-cleared
capture tape stays blank. The final left-blank test moves both heads to zero. -/
private lemma f2_loopHost_fuel_return (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x)
    (p : Fin (x.length + 2)) (flag : ℤ → Option Bool) (word out : List Bool) :
    ∀ j, j ≤ word.length →
    (f2_loopHost body F anchor findMode).tm.runFrom
        (f2_loopFrame body F base (some (.inr (.inr 3))) p flag (bufferTape word)
          (bufferTape []) ((j : ℤ) - 1) ((j : ℤ) - 1) out) (j + 1) =
      f2_loopFrame body F base (some (.inr (.inr 4))) p flag (bufferTape word)
        (bufferTape []) 0 0 out := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    change (match (f2_loopFrame body F base (some (.inr (.inr 3))) p flag (bufferTape word)
        (bufferTape []) ((0 : ℤ) - 1) ((0 : ℤ) - 1) out).workTapeSymbols
          ⟨body.k + 1, by omega⟩ with
      | some _ => f2_loopControlAction body F 0 none (none, .neg) (none, .neg) none
          (some (.inr (.inr 3)))
      | none => f2_loopControlAction body F 0 none (none, .pos) (none, .pos) none
          (some (.inr (.inr 4)))).apply _ = _
    rw [f2_loopFrame_counter]
    simp only [zero_sub, bufferTape_left]
    rw [f2_loopControl_apply]
    simp [f2_loopWrite]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hs : (f2_loopHost body F anchor findMode).tm.step
        (f2_loopFrame body F base (some (.inr (.inr 3))) p flag (bufferTape word)
          (bufferTape []) (((j + 1 : ℕ) : ℤ) - 1) (((j + 1 : ℕ) : ℤ) - 1) out) =
        f2_loopFrame body F base (some (.inr (.inr 3))) p flag (bufferTape word)
          (bufferTape []) ((j : ℤ) - 1) ((j : ℤ) - 1) out := by
      change (match (f2_loopFrame body F base (some (.inr (.inr 3))) p flag (bufferTape word)
          (bufferTape []) (((j + 1 : ℕ) : ℤ) - 1) (((j + 1 : ℕ) : ℤ) - 1) out).workTapeSymbols
            ⟨body.k + 1, by omega⟩ with
        | some _ => f2_loopControlAction body F 0 none (none, .neg) (none, .neg) none
            (some (.inr (.inr 3)))
        | none => f2_loopControlAction body F 0 none (none, .pos) (none, .pos) none
            (some (.inr (.inr 4)))).apply _ = _
      rw [f2_loopFrame_counter]
      rw [show ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) by omega,
        bufferTape_nat, List.getElem?_eq_getElem (by omega : j < word.length)]
      rw [f2_loopControl_apply]
      simp [f2_loopWrite, sub_eq_add_neg]
    rw [hs]
    exact ih (by omega)

/-- Fuel setup phases 0--3 copy the complete fuel word to the counter,
clear the capture track, and return both heads to zero in exactly `3|word|+4`
steps. This includes the empty word, with no counter debit.
**Proof sketch.** Compose the mandatory left move, the fuel rewind, the
copy/clear scan, and the synchronized rewind. Their costs are respectively
one and three copies of the word length plus one. -/
private lemma f2_loopHost_fuel_setup (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x)
    (p : Fin (x.length + 2)) (flag : ℤ → Option Bool) (word out : List Bool) :
    (f2_loopHost body F anchor findMode).tm.runFrom
        (f2_loopFrame body F base (some (.inr (.inr 0))) p flag (bufferTape [])
          (bufferTape word) 0 word.length out) (3 * word.length + 4) =
      f2_loopFrame body F base (some (.inr (.inr 4))) p flag (bufferTape word)
        (bufferTape []) 0 0 out := by
  have hs : (f2_loopHost body F anchor findMode).tm.step
      (f2_loopFrame body F base (some (.inr (.inr 0))) p flag (bufferTape [])
        (bufferTape word) 0 word.length out) =
      f2_loopFrame body F base (some (.inr (.inr 1))) p flag (bufferTape [])
        (bufferTape word) 0 ((word.length : ℤ) - 1) out := by
    change (f2_loopControlAction body F 0 none (none, 0) (none, .neg) none
      (some (.inr (.inr 1)))).apply _ = _
    rw [f2_loopControl_apply]
    simp [f2_loopWrite, sub_eq_add_neg]
  rw [show 3 * word.length + 4 =
      ((word.length + 1) + (word.length + 1) + (word.length + 1)) + 1 by omega,
    MultiTapeTM.runFrom_succ_eq_step, hs]
  rw [MultiTapeTM.runFrom_add,
    MultiTapeTM.runFrom_add (a := word.length + 1) (b := word.length + 1),
    f2_loopHost_fuel_rewind body F anchor findMode base p flag (bufferTape []) 0 word out
      word.length (le_refl _)]
  have hc := f2_loopHost_fuel_copy body F anchor findMode base p flag out word []
  simp only [List.length_nil, Nat.cast_zero, List.nil_append, f2_loopCopy_initial] at hc
  rw [hc, f2_loopHost_fuel_return body F anchor findMode base p flag word out
    word.length (le_refl _)]

/-- The host's captured fuel endpoint, retaining all completed fuel residue. -/
private def f2_loopFuelCaptured (body F : FinTM Bool) {x : List Bool}
    (c : Cfg F.k Bool F.State x) :
    Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x :=
  captureCfg Sum.inl (Sum.inr (Sum.inr (0 : Fin 14))) [] [] (f2_loopFuelCfg body F c)

/-- The prepared startup configuration: fuel copied, capture blank, input
and active heads at their origins, and completed fuel work retained. -/
private def f2_loopReady (body F : FinTM Bool) {x : List Bool}
    (c : Cfg F.k Bool F.State x) :
    Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x :=
  f2_loopFrame body F (f2_loopFuelCaptured body F c)
    (some (.inr (.inl (true, (body.tm.q₀, false))))) 1
    (bufferTape []) (bufferTape c.output) (bufferTape []) 0 0 []

/-- At a genuine fuel halt the capture endpoint has the frame expected by
phase 0, with the flag and counter still blank.
**Proof sketch.** Split the physical tape index into capture, body/flag,
counter, and fuel blocks. The three active controller tracks agree with
their explicit parameters; every inactive track is retained from the base. -/
private lemma f2_loopFuelCaptured_frame (body F : FinTM Bool) {x : List Bool}
    (c : Cfg F.k Bool F.State x) (hc : c.state = none) :
    f2_loopFuelCaptured body F c =
      f2_loopFrame body F (f2_loopFuelCaptured body F c) (some (.inr (.inr 0))) c.inputPos
        (bufferTape []) (bufferTape []) (bufferTape c.output) 0 c.output.length [] := by
  refine Cfg.ext ?_ rfl ?_ ?_ rfl
  · simp [f2_loopFuelCaptured, captureCfg, f2_loopFuelCfg, rightCfg, f2_loopFrame, hc]
  · funext i
    refine Fin.lastCases ?_ ?_ i
    · have hf : body.k + 1 + (1 + F.k) ≠ body.k := by omega
      simp [f2_loopFuelCaptured, captureCfg, f2_loopFuelCfg, rightCfg, f2_loopFrame, hf]
    · intro j
      have hj : (j : ℕ) ≠ body.k + 1 + (1 + F.k) := Nat.ne_of_lt j.isLt
      refine Fin.addCases ?_ ?_ j
      · intro a
        have ha : (a : ℕ) < body.k + 1 + (1 + F.k) := by omega
        have han : (a : ℕ) ≠ body.k + 1 := by omega
        have hap : (a : ℕ) ≠ body.k + 1 + (1 + F.k) := by omega
        simp [f2_loopFuelCaptured, captureCfg, f2_loopFuelCfg, rightCfg, f2_loopFrame, ha, han, hap, Fin.addCases, a.isLt]
      · intro a
        refine Fin.addCases ?_ ?_ a
        · intro b
          have hb : b = 0 := Subsingleton.elim _ _
          subst b
          simp [f2_loopFuelCaptured, captureCfg, f2_loopFuelCfg, rightCfg, f2_loopFrame, Fin.addCases]
        · intro b
          have hbf : body.k + 1 + (1 + (b : ℕ)) ≠ body.k := by omega
          have hbc : body.k + 1 + (1 + (b : ℕ)) ≠ body.k + 1 := by omega
          have hbp : body.k + 1 + (1 + (b : ℕ)) ≠ body.k + 1 + (1 + F.k) := by omega
          simp [f2_loopFrame, hbf, Nat.ne_of_lt b.isLt]
  · funext i
    refine Fin.lastCases ?_ ?_ i
    · have hf : body.k + 1 + (1 + F.k) ≠ body.k := by omega
      simp [f2_loopFuelCaptured, captureCfg, f2_loopFuelCfg, rightCfg, f2_loopFrame, hf]
    · intro j
      refine Fin.addCases ?_ ?_ j
      · intro a
        have ha : (a : ℕ) < body.k + 1 + (1 + F.k) := by omega
        have han : (a : ℕ) ≠ body.k + 1 := by omega
        have hap : (a : ℕ) ≠ body.k + 1 + (1 + F.k) := by omega
        simp [f2_loopFuelCaptured, captureCfg, f2_loopFuelCfg, rightCfg, f2_loopFrame, ha, han, hap, Fin.addCases, a.isLt]
      · intro a
        refine Fin.addCases ?_ ?_ a
        · intro b
          have hb : b = 0 := Subsingleton.elim _ _
          subst b
          simp [f2_loopFuelCaptured, captureCfg, f2_loopFuelCfg, rightCfg, f2_loopFrame, Fin.addCases]
        · intro b
          have hbf : body.k + 1 + (1 + (b : ℕ)) ≠ body.k := by omega
          have hbc : body.k + 1 + (1 + (b : ℕ)) ≠ body.k + 1 := by omega
          have hbp : body.k + 1 + (1 + (b : ℕ)) ≠ body.k + 1 + (1 + F.k) := by omega
          simp [f2_loopFrame, hbf, Nat.ne_of_lt b.isLt]

/-- Fuel execution, setup, and input rewind reach prepared body startup
within `5*T+7` steps, retaining the actual fuel endpoint.
**Proof sketch.** Replace the supplied padded fuel run by its first halt,
relocate it twice, and capture it in the actual host. Setup costs `3L+4`,
where `L ≤ T`; the input rewind costs at most the first run's displacement
plus two, hence at most `T+3`. No bound in the input length is used. -/
private lemma f2_loopHost_prepare (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) (R T : ℕ → ℕ)
    (hF : F.ComputesFunInTime (fun x => Nat.bits (R x.length)) T) (x : List Bool) :
    ∃ (c : Cfg F.k Bool F.State x) (t : ℕ),
      c.state = none ∧ c.output = Nat.bits (R x.length) ∧ t ≤ 5 * T x.length + 7 ∧
      (f2_loopHost body F anchor findMode).tm.runFrom
        ((f2_loopHost body F anchor findMode).tm.initCfg x) t = f2_loopReady body F c ∧
      ∀ i, -(T x.length : ℤ) ≤ c.workTapePos i ∧ c.workTapePos i ≤ T x.length := by
  obtain ⟨space, hhalt, hout, hspace⟩ := hF x
  obtain ⟨u, hu, hut, hlive, huh, hue⟩ :=
    f2_loop_first_halt F.tm (F.tm.initCfg x) (T x.length) (by simp [MultiTapeTM.initCfg, Cfg.init]) hhalt
  let c := F.tm.runFrom (F.tm.initCfg x) u
  have hc : c.state = none := huh
  have ho : c.output = Nat.bits (R x.length) := by dsimp only [c]; rw [hue]; exact hout
  have hcap : (f2_loopHost body F anchor findMode).tm.runFrom
      ((f2_loopHost body F anchor findMode).tm.initCfg x) u = f2_loopFuelCaptured body F c := by
    rw [f2_loopHost_init, f2_loopFuel_init]
    rw [f2_loopHost_fuel_capture]
    · rw [f2_loopFuel_run]; rfl
    · intro v hv
      rw [f2_loopFuel_run]
      simpa [Cfg.Halted, f2_loopFuelCfg, rightCfg] using hlive v hv
  let prepared := f2_loopFrame body F (f2_loopFuelCaptured body F c)
    (some (.inr (.inr 4))) c.inputPos (bufferTape []) (bufferTape c.output)
    (bufferTape []) 0 0 []
  have hsetup : (f2_loopHost body F anchor findMode).tm.runFrom
      (f2_loopFuelCaptured body F c) (3 * c.output.length + 4) = prepared := by
    conv_lhs => arg 1; rw [f2_loopFuelCaptured_frame body F c hc]
    exact f2_loopHost_fuel_setup body F anchor findMode _ _ _ _ _
  obtain ⟨v, hv, hrew⟩ := f2_loopHost_input_rewind body F anchor findMode prepared rfl
  have hw : c.output.length ≤ T x.length := by rw [ho]; exact f2_loop_fuel_width F R T hF x
  have hp : c.inputPos.val ≤ 1 + u := f2_loop_input_run_le F.tm (F.tm.initCfg x) u
  refine ⟨c, u + (3 * c.output.length + 4) + v, hc, ho, ?_, ?_, ?_⟩
  · change v ≤ c.inputPos.val + 2 at hv
    omega
  · rw [MultiTapeTM.runFrom_add,
      MultiTapeTM.runFrom_add (a := u) (b := 3 * c.output.length + 4), hcap, hsetup, hrew]
    rfl

  · intro i
    have h := f2_head_steps F.tm (F.tm.initCfg x) u i
    have hh : -(u : ℤ) ≤ c.workTapePos i ∧ c.workTapePos i ≤ u := by
      simpa [c, MultiTapeTM.initCfg, Cfg.init, Cfg.ofWords] using h
    omega

/-- The stopped body's padded source configuration, preserving the counter
word and the complete fuel residue through every call. -/
private def f2_loopBodyPadded (body F : FinTM Bool) (anchor : body.State) {x : List Bool}
    (c : Cfg body.k Bool body.State x) (release : Bool) (flag : Option Bool)
    (word : List Bool) (fuel : Cfg F.k Bool F.State x) :
    Cfg (body.k + 1 + (1 + F.k)) Bool (body.State × Bool) x :=
  leftCfg id (f2_loopBodyCfg body anchor c release flag)
    (Fin.addCases (fun (_ : Fin 1) => bufferTape word) fuel.workTapes)
    (Fin.addCases (fun (_ : Fin 1) => 0) fuel.workTapePos)

/-- A body call viewed inside the concrete capturing host. A halted stopped
body is represented by the corresponding startup/active return phase. -/
private def f2_loopCall (body F : FinTM Bool) (anchor : body.State) {x : List Bool}
    (startup : Bool) (c : Cfg body.k Bool body.State x) (release : Bool)
    (flag : Option Bool) (word : List Bool) (fuel : Cfg F.k Bool F.State x) :
    Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x :=
  captureCfg (fun s => Sum.inr (Sum.inl (startup, s)))
    (Sum.inr (Sum.inr (if startup then 6 else 7 : Fin 14))) [] []
    (f2_loopBodyPadded body F anchor c release flag word fuel)

/-- The padded body source simulates the stopped body with arbitrary inactive
counter and fuel tracks. -/
private lemma f2_loopBodySource_run (body F : FinTM Bool) (anchor : body.State)
    {x : List Bool}
    (c : Cfg (body.k + 1) Bool (body.State × Bool) x)
    (tapes : Fin (1 + F.k) → ℤ → Option Bool) (heads : Fin (1 + F.k) → ℤ) (t : ℕ) :
    (f2_loopBodySource body F anchor).runFrom (leftCfg id c tapes heads) t =
      leftCfg id ((f2_loopBodyTM body anchor).tm.runFrom c t) tapes heads :=
  leftCfg_run (f2_loopBodyTM body anchor).tm (f2_loopBodySource body F anchor)
    id (fun _ _ _ => rfl) c tapes heads t

/-- A live anchor endpoint is captured after one additional stop step.
The exact endpoint keeps every inactive tape and carries the false stop flag.
**Proof sketch.** The live endpoint rules out earlier halts. Use the source
wrapper simulation up to that endpoint, take its silent anchor-stop step,
and lift the resulting run through the padded source and actual host capture.
The guard at time zero is supplied by the release bit for active calls. -/
private lemma f2_loopHost_anchor_return (body F : FinTM Bool) (anchor : body.State)
    (findMode startup : Bool) {x : List Bool}
    (c : Cfg body.k Bool body.State x) (release : Bool) (t : ℕ)
    (word : List Bool) (fuel : Cfg F.k Bool F.State x)
    (hend : (body.tm.runFrom c t).state = some anchor)
    (hreleased : t = 0 → release = false)
    (hanchor : ∀ u < t, (u = 0 ∧ release = true) ∨
      (body.tm.runFrom c u).state ≠ some anchor) :
    (f2_loopHost body F anchor findMode).tm.runFrom
        (f2_loopCall body F anchor startup c release none word fuel) (t + 1) =
      f2_loopCall body F anchor startup {body.tm.runFrom c t with state := none}
        false (some false) word fuel := by
  have hlive : ∀ u ≤ t, (body.tm.runFrom c u).state ≠ none :=
    f2_loop_live_prefix body.tm c t (by rw [hend]; simp)
  have hc : c.state ≠ none := by simpa using hlive 0 (Nat.zero_le _)
  have hr : (f2_loopBodyTM body anchor).tm.runFrom (f2_loopBodyCfg body anchor c release none) t =
      f2_loopBodyCfg body anchor (body.tm.runFrom c t) false none := by
    rw [f2_loopBody_run body anchor c release hc t
      (fun u hu => hlive u (by omega)) hanchor]
    have hn := hlive t (le_refl _)
    rw [if_neg hn]
    by_cases ht : t = 0
    · rw [if_pos ht, hreleased ht]
    · rw [if_neg ht]
  have hstop : (f2_loopBodyTM body anchor).tm.runFrom (f2_loopBodyCfg body anchor c release none)
      (t + 1) =
      f2_loopBodyCfg body anchor {body.tm.runFrom c t with state := none} false (some false) := by
    rw [MultiTapeTM.runFrom_succ_eq_step', hr, f2_loopBody_stop body anchor _ hend]
  unfold f2_loopCall f2_loopBodyPadded
  rw [f2_loopHost_body_capture]
  · rw [f2_loopBodySource_run, hstop]
  · intro u hu
    rw [f2_loopBodySource_run, f2_loopBody_run body anchor c release hc u
      (fun v hv => hlive v (by omega)) (fun v hv => hanchor v (by omega))]
    simpa [Cfg.Halted, leftCfg, f2_loopBodyCfg] using hlive u (by omega)

/-- Prepared fuel startup is the canonical captured body call on blank body
tapes; the counter and fuel residue are exactly the padded inactive block.
**Proof sketch.** Compare the four physical tape blocks. The input head and
all active heads are at their origins; only the completed fuel bank has
arbitrary contents and head positions. -/
private lemma f2_loopReady_call (body F : FinTM Bool) (anchor : body.State)
    {x : List Bool} (fuel : Cfg F.k Bool F.State x) :
    f2_loopReady body F fuel =
      f2_loopCall body F anchor true (body.tm.initCfg x) false none fuel.output fuel := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  all_goals
    funext i
    refine Fin.lastCases ?_ ?_ i
    · have hf : body.k + 1 + (1 + F.k) ≠ body.k := by omega
      simp [f2_loopReady, f2_loopFrame, f2_loopCall, captureCfg, f2_loopBodyPadded, leftCfg,
        f2_loopBodyCfg, MultiTapeTM.initCfg, Cfg.init, hf]
    · intro j
      refine Fin.addCases ?_ ?_ j
      · intro a
        have ha : (a : ℕ) < body.k + 1 + (1 + F.k) := by omega
        have han : (a : ℕ) ≠ body.k + 1 := by omega
        have hap : (a : ℕ) ≠ body.k + 1 + (1 + F.k) := by omega
        simp [f2_loopReady, f2_loopFrame, f2_loopCall, captureCfg, f2_loopBodyPadded, leftCfg,
          f2_loopBodyCfg, MultiTapeTM.initCfg, Cfg.init, f2_loopFuelCaptured, f2_loopFuelCfg,
          rightCfg, ha, han, hap, Fin.addCases, a.isLt]
      · intro a
        refine Fin.addCases ?_ ?_ a
        · intro b
          have hb : b = 0 := Subsingleton.elim _ _
          subst b
          simp [f2_loopReady, f2_loopFrame, f2_loopCall, captureCfg, f2_loopBodyPadded, leftCfg,
            f2_loopBodyCfg, MultiTapeTM.initCfg, Cfg.init, Fin.addCases]
        · intro b
          have hbf : body.k + 1 + (1 + (b : ℕ)) ≠ body.k := by omega
          have hb : (b : ℕ) < F.k := b.isLt
          simp [f2_loopReady, f2_loopFrame, f2_loopCall, captureCfg, f2_loopBodyPadded, leftCfg,
            f2_loopBodyCfg, MultiTapeTM.initCfg, Cfg.init, f2_loopFuelCaptured, f2_loopFuelCfg,
            rightCfg, hbf, hb, Nat.ne_of_lt hb, Fin.addCases]

/-- Phase 6 clears startup's false flag and releases the first anchor for
free. It changes no body, counter, or fuel data.
**Proof sketch.** The captured stopped body is in phase 6. Its sole write
clears the flag's origin cell. Comparing tape blocks identifies the result
with the active released call on the same body data. -/
private lemma f2_loopHost_release (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool} (c : Cfg body.k Bool body.State x)
    (word : List Bool) (fuel : Cfg F.k Bool F.State x) :
    (f2_loopHost body F anchor findMode).tm.step
        (f2_loopCall body F anchor true {c with state := none} false (some false) word fuel) =
      f2_loopCall body F anchor false {c with state := some anchor} true none word fuel := by
  change (f2_loopControlAction body F 0 (some none) (none, 0) (none, 0) none
    (some (.inr (.inl (false, (anchor, true)))))).apply _ = _
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ ?_
  · funext i z
    by_cases hf : (i : ℕ) = body.k
    · have hi : body.k < body.k + 1 + (1 + F.k) := by omega
      simp [Action.apply, f2_loopControlAction, f2_loopCall, captureCfg, f2_loopBodyPadded,
        leftCfg, f2_loopBodyCfg, hf, hi, Fin.addCases, Function.update]
    · by_cases hb : (i : ℕ) < body.k + 1
      · have hi : (i : ℕ) < body.k := by omega
        simp [Action.apply, f2_loopControlAction, f2_loopCall, captureCfg, f2_loopBodyPadded,
          leftCfg, f2_loopBodyCfg, hf, Fin.addCases, hb, hi]
      · simp [Action.apply, f2_loopControlAction, f2_loopCall, captureCfg, f2_loopBodyPadded,
          leftCfg, f2_loopBodyCfg, hf, Fin.addCases, hb]
  · funext i
    by_cases hf : (i : ℕ) = body.k <;>
      simp [Action.apply, f2_loopControlAction, f2_loopCall, captureCfg, f2_loopBodyPadded,
        leftCfg, f2_loopBodyCfg, hf]
  · simp [Action.apply, f2_loopControlAction, f2_loopCall, captureCfg]

/-- Genuine body startup reaches the released first candidate in at most
its source startup time plus two host steps.
**Proof sketch.** When the startup time is positive, the no-anchor prefix is
captured without a premature stop; a zero-time startup already occupies the
anchor (the no-anchor premise is vacuous) and takes the two administrative
steps directly. In either case the anchor endpoint yields the false flag;
one stop step and phase 6's flag-clear step release the initial candidate. -/
private lemma f2_loopHost_start (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool} (s : List Bool) (t : ℕ)
    (fuel : Cfg F.k Bool F.State x)
    (hguard : ∀ u < t, (body.tm.runFrom (body.tm.initCfg x) u).state ≠ some anchor)
    (hend : body.tm.runFrom (body.tm.initCfg x) t = Cfg.ofWords anchor (stateWord body.k s)) :
    (f2_loopHost body F anchor findMode).tm.runFrom (f2_loopReady body F fuel) (t + 2) =
      f2_loopCall body F anchor false (Cfg.ofWords anchor (stateWord body.k s))
        true none fuel.output fuel := by
  rw [f2_loopReady_call body F anchor, show t + 2 = (t + 1) + 1 by omega,
    MultiTapeTM.runFrom_succ_eq_step']
  rw [f2_loopHost_anchor_return body F anchor findMode true (body.tm.initCfg x) false t
    fuel.output fuel (by rw [hend]; rfl) (fun _ => rfl) (fun u hu => Or.inr (hguard u hu))]
  rw [hend, f2_loopHost_release body F anchor findMode _ _ _]
  rfl

/-- A genuine first halt returns to phase 7 with the true stop flag and the
entire source output captured, including its halting emission.
**Proof sketch.** Simulate the released body through its first halting action.
Strict liveness permits actual-host capture throughout; the positive duration
consumes the release bit and the halting action sets the true flag. -/
private lemma f2_loopHost_halt_return (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool} (c : Cfg body.k Bool body.State x)
    (t : ℕ) (word : List Bool) (fuel : Cfg F.k Bool F.State x)
    (ht : 0 < t) (hlive : ∀ u < t, (body.tm.runFrom c u).state ≠ none)
    (hanchor : ∀ u, 0 < u → u < t → (body.tm.runFrom c u).state ≠ some anchor)
    (hend : (body.tm.runFrom c t).state = none) :
    (f2_loopHost body F anchor findMode).tm.runFrom
        (f2_loopCall body F anchor false c true none word fuel) t =
      f2_loopCall body F anchor false (body.tm.runFrom c t) false (some true) word fuel := by
  have hc : c.state ≠ none := by simpa using hlive 0 ht
  have hg : ∀ u < t, (u = 0 ∧ true = true) ∨
      (body.tm.runFrom c u).state ≠ some anchor := by
    intro u hu
    by_cases hz : u = 0
    · exact Or.inl ⟨hz, rfl⟩
    · exact Or.inr (hanchor u (by omega) hu)
  unfold f2_loopCall f2_loopBodyPadded
  rw [f2_loopHost_body_capture]
  · rw [f2_loopBodySource_run, f2_loopBody_run body anchor c true hc t hlive hg]
    simp [hend, Nat.ne_of_gt ht]
  · intro u hu
    rw [f2_loopBodySource_run, f2_loopBody_run body anchor c true hc u
      (fun v hv => hlive v (by omega)) (fun v hv => hg v (by omega))]
    simpa [Cfg.Halted, leftCfg, f2_loopBodyCfg] using hlive u hu

/-- A captured body call has the explicit flag, counter, and payload tracks
used by the controller frame, with arbitrary inactive body and fuel residue. -/
private lemma f2_loopCall_frame (body F : FinTM Bool) (anchor : body.State)
    {x : List Bool} (startup : Bool) (c : Cfg body.k Bool body.State x)
    (release : Bool) (flag : Option Bool) (word : List Bool) (fuel : Cfg F.k Bool F.State x) :
    f2_loopCall body F anchor startup c release flag word fuel =
      f2_loopFrame body F (f2_loopCall body F anchor startup c release flag word fuel)
        (f2_loopCall body F anchor startup c release flag word fuel).state c.inputPos
        (fun z => if z = 0 then flag else none) (bufferTape word) (bufferTape c.output)
        0 c.output.length [] := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  all_goals
    funext i
    by_cases hf : (i : ℕ) = body.k
    · have hlt : body.k < body.k + 1 + (1 + F.k) := by omega
      simp [f2_loopFrame, f2_loopCall, captureCfg, f2_loopBodyPadded, leftCfg, f2_loopBodyCfg,
        hf, hlt, Fin.addCases]
    · by_cases hc : (i : ℕ) = body.k + 1
      · simp [f2_loopFrame, f2_loopCall, captureCfg, f2_loopBodyPadded, leftCfg, f2_loopBodyCfg,
          hc, Fin.addCases]
      · by_cases hp : (i : ℕ) = body.k + 1 + (1 + F.k)
        · have hpf : body.k + 1 + (1 + F.k) ≠ body.k := by omega
          simp [f2_loopFrame, f2_loopCall, captureCfg, f2_loopBodyPadded, leftCfg, f2_loopBodyCfg, hp, hpf]
        · simp [f2_loopFrame, hf, hc, hp]

/-- Reframing a body call changes precisely its control, flag, and counter.
**Proof sketch.** The source configuration changes only in state. Thus all
inactive body and fuel data coincide; compare the three explicitly replaced
tracks and retain every other physical tape and head. -/
private lemma f2_loopCall_reframe (body F : FinTM Bool) (anchor : body.State)
    {x : List Bool} (c : Cfg body.k Bool body.State x)
    (startup startup' release release' : Bool) (flag flag' : Option Bool)
    (word word' : List Bool) (fuel : Cfg F.k Bool F.State x) (q : Option body.State) :
    f2_loopFrame body F (f2_loopCall body F anchor startup c release flag word fuel)
        (f2_loopCall body F anchor startup' {c with state := q} release' flag' word' fuel).state
        c.inputPos (fun z => if z = 0 then flag' else none) (bufferTape word')
        (bufferTape c.output) 0 c.output.length [] =
      f2_loopCall body F anchor startup' {c with state := q} release' flag' word' fuel := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  all_goals
    funext i
    by_cases hf : (i : ℕ) = body.k
    · have hlt : body.k < body.k + 1 + (1 + F.k) := by omega
      simp [f2_loopFrame, f2_loopCall, captureCfg, f2_loopBodyPadded, leftCfg, f2_loopBodyCfg,
        hf, hlt, Fin.addCases]
    · by_cases hc : (i : ℕ) = body.k + 1
      · simp [f2_loopFrame, f2_loopCall, captureCfg, f2_loopBodyPadded, leftCfg, f2_loopBodyCfg,
          hc, Fin.addCases]
      · by_cases hp : (i : ℕ) = body.k + 1 + (1 + F.k)
        · have hpf : body.k + 1 + (1 + F.k) ≠ body.k := by omega
          simp [f2_loopFrame, f2_loopCall, captureCfg, f2_loopBodyPadded, leftCfg, f2_loopBodyCfg, hp, hpf]
        · by_cases hb : (i : ℕ) < body.k + 1
          · have hi : (i : ℕ) < body.k := by omega
            simp [f2_loopFrame, f2_loopCall, captureCfg, f2_loopBodyPadded, leftCfg, f2_loopBodyCfg,
              hf, hc, hp, Fin.addCases, hb, hi]
          · have hn : (i : ℕ) - (body.k + 1) ≠ 0 := by omega
            simp [f2_loopFrame, f2_loopCall, captureCfg, f2_loopBodyPadded, leftCfg, f2_loopBodyCfg,
              hf, hc, hp, Fin.addCases, hb, hn]

/-- One actual-host borrow step changes only the counter, recording success
or underflow in the rewind phase. -/
private lemma f2_loopHost_borrow_step (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x)
    (p : Fin (x.length + 2)) (pre rest : List Bool) :
    (f2_loopHost body F anchor findMode).tm.step
      (f2_loopFrame body F base (some (.inr (.inr 8))) p (bufferTape [])
        (bufferTape (pre ++ rest)) (bufferTape []) pre.length 0 []) =
      match rest with
      | [] => f2_loopFrame body F base (some (.inr (.inr 10))) p (bufferTape [])
          (bufferTape pre) (bufferTape []) (pre.length - 1) 0 []
      | true :: us => f2_loopFrame body F base (some (.inr (.inr 9))) p (bufferTape [])
          (bufferTape (pre ++ false :: us)) (bufferTape []) (pre.length - 1) 0 []
      | false :: us => f2_loopFrame body F base (some (.inr (.inr 8))) p (bufferTape [])
          (bufferTape (pre ++ true :: us)) (bufferTape []) (pre.length + 1) 0 [] := by
  change (match (f2_loopFrame body F base (some (.inr (.inr 8))) p (bufferTape [])
      (bufferTape (pre ++ rest)) (bufferTape []) pre.length 0 []).workTapeSymbols
        ⟨body.k + 1, by omega⟩ with
    | some false => f2_loopControlAction body F 0 none (some (some true), .pos) (none, 0)
        none (some (.inr (.inr 8)))
    | some true => f2_loopControlAction body F 0 none (some (some false), .neg) (none, 0)
        none (some (.inr (.inr 9)))
    | none => f2_loopControlAction body F 0 none (none, .neg) (none, 0) none
        (some (.inr (.inr 10)))).apply _ = _
  rw [f2_loopFrame_counter, f2_loopBuffer_read]
  cases rest with
  | nil =>
    simp only [List.head?]
    rw [f2_loopControl_apply]
    simp [f2_loopWrite, sub_eq_add_neg]
  | cons b rest =>
    cases b <;> simp only [List.head?]
    all_goals rw [f2_loopControl_apply]; simp [f2_loopWrite, f2_loopBuffer_write, sub_eq_add_neg]

/-- The actual host performs the borrow scan in the standalone scan's exact
time, preserving all non-counter tracks.
**Proof sketch.** Induct on the remaining word. Each false bit advances the
processed prefix. A true bit or the right blank starts the appropriate
rewind phase; no cell outside the original counter width is written. -/
private lemma f2_loopHost_borrow_run (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x)
    (p : Fin (x.length + 2)) (word : List Bool) : ∀ pre,
    (f2_loopHost body F anchor findMode).tm.runFrom
        (f2_loopFrame body F base (some (.inr (.inr 8))) p (bufferTape [])
          (bufferTape (pre ++ word)) (bufferTape []) pre.length 0 [])
        (f2_loopBorrowPos word + 1) =
      f2_loopFrame body F base (some (.inr (.inr (if (f2_loopDebit word).2 then 9 else 10)))) p
        (bufferTape []) (bufferTape (pre ++ (f2_loopDebit word).1)) (bufferTape [])
        ((pre.length : ℤ) + f2_loopBorrowPos word - 1) 0 [] := by
  induction word with
  | nil =>
    intro pre
    simpa [f2_loopBorrowPos, f2_loopDebit, MultiTapeTM.runFrom_succ_eq_step] using
      f2_loopHost_borrow_step body F anchor findMode base p pre []
  | cons b word ih =>
    intro pre
    cases b with
    | true =>
      simpa [f2_loopBorrowPos, f2_loopDebit, MultiTapeTM.runFrom_succ_eq_step] using
        f2_loopHost_borrow_step body F anchor findMode base p pre (true :: word)
    | false =>
      simp only [f2_loopBorrowPos]
      rw [MultiTapeTM.runFrom_succ_eq_step, f2_loopHost_borrow_step]
      simpa [f2_loopDebit, List.append_assoc, Nat.cast_add, Nat.cast_one,
        add_assoc, add_comm, add_left_comm] using ih (pre ++ [true])

/-- The host's success/underflow rewind returns the counter head to zero.
Success releases the next anchor; underflow enters phase 11 without yet
emitting. Both paths retain all inactive residue.
**Proof sketch.** Induct on the number of counter cells to the left. The
left-blank test dispatches according to the stored success bit. -/
private lemma f2_loopHost_borrow_rewind (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x)
    (p : Fin (x.length + 2)) (word : List Bool) (success : Bool) :
    ∀ j, j ≤ word.length →
    (f2_loopHost body F anchor findMode).tm.runFrom
        (f2_loopFrame body F base (some (.inr (.inr (if success then 9 else 10)))) p
          (bufferTape []) (bufferTape word) (bufferTape []) ((j : ℤ) - 1) 0 []) (j + 1) =
      f2_loopFrame body F base
        (some (if success then .inr (.inl (false, (anchor, true))) else .inr (.inr 11))) p
        (bufferTape []) (bufferTape word) (bufferTape []) 0 0 [] := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    cases success <;>
      (change (match (f2_loopFrame body F base _ p (bufferTape []) (bufferTape word)
          (bufferTape []) ((0 : ℤ) - 1) 0 []).workTapeSymbols ⟨body.k + 1, by omega⟩ with
        | some _ => f2_loopControlAction body F 0 none (none, .neg) (none, 0) none _
        | none => f2_loopControlAction body F 0 none (none, .pos) (none, 0) none _).apply _ = _)
    all_goals
      rw [f2_loopFrame_counter]
      simp only [zero_sub, bufferTape_left]
      rw [f2_loopControl_apply]
      simp [f2_loopWrite]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hs : (f2_loopHost body F anchor findMode).tm.step
        (f2_loopFrame body F base (some (.inr (.inr (if success then 9 else 10)))) p
          (bufferTape []) (bufferTape word) (bufferTape []) (((j + 1 : ℕ) : ℤ) - 1) 0 []) =
        f2_loopFrame body F base (some (.inr (.inr (if success then 9 else 10)))) p
          (bufferTape []) (bufferTape word) (bufferTape []) ((j : ℤ) - 1) 0 [] := by
      cases success <;>
        (change (match (f2_loopFrame body F base _ p (bufferTape []) (bufferTape word)
            (bufferTape []) (((j + 1 : ℕ) : ℤ) - 1) 0 []).workTapeSymbols
              ⟨body.k + 1, by omega⟩ with
          | some _ => f2_loopControlAction body F 0 none (none, .neg) (none, 0) none _
          | none => f2_loopControlAction body F 0 none (none, .pos) (none, 0) none _).apply _ = _)
      all_goals
        rw [f2_loopFrame_counter, show ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) by omega,
          bufferTape_nat, List.getElem?_eq_getElem (by omega : j < word.length)]
        rw [f2_loopControl_apply]
        simp [f2_loopWrite, sub_eq_add_neg]
    rw [hs]
    exact ih (by omega)

/-- The complete actual-host counter operation has the fixed-width
worst-case bound `2|word|+2`, covering underflow and width zero. -/
private lemma f2_loopHost_borrow (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x)
    (p : Fin (x.length + 2)) (word : List Bool) :
    2 * f2_loopBorrowPos word + 2 ≤ 2 * word.length + 2 ∧
    (f2_loopHost body F anchor findMode).tm.runFrom
        (f2_loopFrame body F base (some (.inr (.inr 8))) p (bufferTape [])
          (bufferTape word) (bufferTape []) 0 0 []) (2 * f2_loopBorrowPos word + 2) =
      f2_loopFrame body F base
        (some (if (f2_loopDebit word).2 then .inr (.inl (false, (anchor, true)))
          else .inr (.inr 11))) p
        (bufferTape []) (bufferTape (f2_loopDebit word).1) (bufferTape []) 0 0 [] := by
  refine ⟨by have := f2_loopBorrowPos_le word; omega, ?_⟩
  have hr := f2_loopHost_borrow_run body F anchor findMode base p word []
  simp only [List.length_nil, Nat.cast_zero, List.nil_append, zero_add] at hr
  rw [show 2 * f2_loopBorrowPos word + 2 =
      (f2_loopBorrowPos word + 1) + (f2_loopBorrowPos word + 1) by omega,
    MultiTapeTM.runFrom_add, hr]
  exact f2_loopHost_borrow_rewind body F anchor findMode base p (f2_loopDebit word).1
    (f2_loopDebit word).2 _ (by rw [f2_loopDebit_length]; exact f2_loopBorrowPos_le word)

/-- The flag read is at its fixed origin, independently of inactive residue. -/
private lemma f2_loopFrame_flag (body F : FinTM Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x)
    (q : Option (f2_LoopHostState body F)) (p : Fin (x.length + 2))
    (flag counter payload : ℤ → Option Bool) (ch ph : ℤ) (out : List Bool) :
    (f2_loopFrame body F base q p flag counter payload ch ph out).workTapeSymbols
        ⟨body.k, by omega⟩ = flag 0 := by
  simp [f2_loopFrame, Cfg.workTapeSymbols]

/-- Clearing the only flag cell leaves a completely blank flag tape. -/
private lemma f2_loopFlag_clear (flag : Option Bool) :
    f2_loopWrite (fun z : ℤ => if z = 0 then flag else none) 0 (some none) = bufferTape [] := by
  funext z
  by_cases hz : z = 0 <;> simp [f2_loopWrite, Function.update, hz]

/-- A rejecting stopped call clears its flag, debits in worst-case width
time, and either releases the next anchor or emits exhaustion and halts.
Underflow and its emission are included in this same segment.
**Proof sketch.** Phase 7 clears the false flag in one step. The proved host
borrow takes `2j+2` steps. Success is the reframed next body seam; underflow
takes one additional phase-11 step, for at most `2|word|+4` steps in total. -/
private lemma f2_loopHost_reject (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool} (c : Cfg body.k Bool body.State x)
    (word : List Bool) (fuel : Cfg F.k Bool F.State x)
    (hc : c.state = none) (ho : c.output = []) :
    ∃ t ≤ 2 * word.length + 4,
      if (f2_loopDebit word).2 then
        (f2_loopHost body F anchor findMode).tm.runFrom
            (f2_loopCall body F anchor false c false (some false) word fuel) t =
          f2_loopCall body F anchor false {c with state := some anchor} true none (f2_loopDebit word).1 fuel
      else
        ((f2_loopHost body F anchor findMode).tm.runFrom
          (f2_loopCall body F anchor false c false (some false) word fuel) t).state = none ∧
        ((f2_loopHost body F anchor findMode).tm.runFrom
          (f2_loopCall body F anchor false c false (some false) word fuel) t).output =
            (if findMode then [] else [false]) := by
  let base := f2_loopCall body F anchor false c false (some false) word fuel
  have hs : base.state = some (.inr (.inr (7 : Fin 14))) := by
    simp [base, f2_loopCall, captureCfg, f2_loopBodyPadded, leftCfg, f2_loopBodyCfg, hc]
  have hf : base = f2_loopFrame body F base (some (.inr (.inr 7))) c.inputPos
      (fun z => if z = 0 then some false else none) (bufferTape word) (bufferTape []) 0 0 [] := by
    have h := f2_loopCall_frame body F anchor false c false (some false) word fuel
    have hstate : (f2_loopCall body F anchor false c false (some false) word fuel).state =
        some (.inr (.inr (7 : Fin 14))) := hs
    simpa only [hstate, ho, List.length_nil, Nat.cast_zero] using h
  have hstep : (f2_loopHost body F anchor findMode).tm.step base =
      f2_loopFrame body F base (some (.inr (.inr 8))) c.inputPos
        (bufferTape []) (bufferTape word) (bufferTape []) 0 0 [] := by
    conv_lhs => arg 1; rw [hf]
    change (if (f2_loopFrame body F base (some (.inr (.inr 7))) c.inputPos
        (fun z => if z = 0 then some false else none) (bufferTape word) (bufferTape []) 0 0 []).workTapeSymbols
          ⟨body.k, by omega⟩ = some true then _
      else f2_loopControlAction body F 0 (some none) (none, 0) (none, 0) none
        (some (.inr (.inr 8)))).apply _ = _
    rw [f2_loopFrame_flag]
    change (f2_loopControlAction body F 0 (some none) (none, 0) (none, 0) none
      (some (.inr (.inr 8)))).apply _ = _
    rw [f2_loopControl_apply, f2_loopFlag_clear]
    simp [f2_loopWrite]
  have hrun : (f2_loopHost body F anchor findMode).tm.runFrom base (2 * f2_loopBorrowPos word + 3) =
      f2_loopFrame body F base
        (some (if (f2_loopDebit word).2 then .inr (.inl (false, (anchor, true)))
          else .inr (.inr 11))) c.inputPos
        (bufferTape []) (bufferTape (f2_loopDebit word).1) (bufferTape []) 0 0 [] := by
    rw [show 2 * f2_loopBorrowPos word + 3 = (2 * f2_loopBorrowPos word + 2) + 1 by omega,
      MultiTapeTM.runFrom_succ_eq_step, hstep]
    exact (f2_loopHost_borrow body F anchor findMode base c.inputPos word).2
  have hw := f2_loopBorrowPos_le word
  by_cases hb : (f2_loopDebit word).2 = true
  · refine ⟨2 * f2_loopBorrowPos word + 3, by omega, ?_⟩
    simp only [hb, if_true] at hrun ⊢
    rw [hrun]
    have h := f2_loopCall_reframe body F anchor c false false false true (some false) none
      word (f2_loopDebit word).1 fuel (some anchor)
    simpa [base, f2_loopCall, captureCfg, f2_loopBodyPadded, leftCfg, f2_loopBodyCfg, ho] using h
  · refine ⟨2 * f2_loopBorrowPos word + 4, by omega, ?_⟩
    simp only [hb] at hrun ⊢
    have hh : (f2_loopHost body F anchor findMode).tm.runFrom base (2 * f2_loopBorrowPos word + 4) =
        f2_loopFrame body F base none c.inputPos (bufferTape []) (bufferTape (f2_loopDebit word).1)
          (bufferTape []) 0 0 (if findMode then [] else [false]) := by
      rw [show 2 * f2_loopBorrowPos word + 4 = (2 * f2_loopBorrowPos word + 3) + 1 by omega,
        MultiTapeTM.runFrom_succ_eq_step', hrun]
      change (f2_loopControlAction body F 0 none (none, 0) (none, 0)
        (if findMode then none else some false) none).apply _ = _
      rw [f2_loopControl_apply]
      cases findMode <;> simp [f2_loopWrite]
    rw [hh]
    exact ⟨rfl, rfl⟩

/-- Accepting-payload phase 12 scans to the left blank and returns at the origin.
**Proof sketch.** Induct on the number of stored cells to the left. At zero,
the head is on the left blank; otherwise its cell is nonblank and the left
move reduces that number. All other tracks and the native input are retained. -/
private lemma f2_loopHost_payload_rewind (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x)
    (p : Fin (x.length + 2)) (flag counter : ℤ → Option Bool)
    (ch : ℤ) (word out : List Bool) : ∀ j, j ≤ word.length →
    (f2_loopHost body F anchor findMode).tm.runFrom
        (f2_loopFrame body F base (some (.inr (.inr 12))) p flag counter
          (bufferTape word) ch ((j : ℤ) - 1) out) (j + 1) =
      f2_loopFrame body F base (some (.inr (.inr 13))) p flag counter
        (bufferTape word) ch 0 out := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    change (match (f2_loopFrame body F base (some (.inr (.inr 12))) p flag counter
        (bufferTape word) ch ((0 : ℤ) - 1) out).workTapeSymbols
          (Fin.last (body.k + 1 + (1 + F.k))) with
      | some _ => f2_loopControlAction body F 0 none (none, 0) (none, .neg) none
          (some (.inr (.inr 12)))
      | none => f2_loopControlAction body F 0 none (none, 0) (none, .pos) none
          (some (.inr (.inr 13)))).apply _ = _
    rw [f2_loopFrame_payload]
    simp only [zero_sub, bufferTape_left]
    rw [f2_loopControl_apply]
    simp [f2_loopWrite]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hs : (f2_loopHost body F anchor findMode).tm.step
        (f2_loopFrame body F base (some (.inr (.inr 12))) p flag counter
          (bufferTape word) ch (((j + 1 : ℕ) : ℤ) - 1) out) =
        f2_loopFrame body F base (some (.inr (.inr 12))) p flag counter
          (bufferTape word) ch ((j : ℤ) - 1) out := by
      change (match (f2_loopFrame body F base (some (.inr (.inr 12))) p flag counter
          (bufferTape word) ch (((j + 1 : ℕ) : ℤ) - 1) out).workTapeSymbols
            (Fin.last (body.k + 1 + (1 + F.k))) with
        | some _ => f2_loopControlAction body F 0 none (none, 0) (none, .neg) none
            (some (.inr (.inr 12)))
        | none => f2_loopControlAction body F 0 none (none, 0) (none, .pos) none
            (some (.inr (.inr 13)))).apply _ = _
      rw [f2_loopFrame_payload]
      rw [show ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) by omega,
        bufferTape_nat, List.getElem?_eq_getElem (by omega : j < word.length)]
      rw [f2_loopControl_apply]
      simp [f2_loopWrite, sub_eq_add_neg]
    rw [hs]
    exact ih (by omega)

/-- Phase 13 replays a framed payload, retaining arbitrary inactive tracks.
**Proof sketch.** Express the frame as the right-block replay configuration
using its own inactive tape and head projections, then apply the already
proved actual-host replay correspondence. -/
private lemma f2_loopHost_frame_replay (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x)
    (p : Fin (x.length + 2)) (flag counter : ℤ → Option Bool) (ch : ℤ) (word : List Bool) :
    let c := f2_loopFrame body F base (some (.inr (.inr 13))) p flag counter (bufferTape word) ch 0 []
    ((f2_loopHost body F anchor findMode).tm.runFrom c (word.length + 1)).state = none ∧
    ((f2_loopHost body F anchor findMode).tm.runFrom c (word.length + 1)).output = word := by
  dsimp only
  let c := f2_loopFrame body F base (some (.inr (.inr 13))) p flag counter (bufferTape word) ch 0 []
  let tapes := fun i : Fin (body.k + 1 + (1 + F.k)) => c.workTapes i.castSucc
  let heads := fun i : Fin (body.k + 1 + (1 + F.k)) => c.workTapePos i.castSucc
  have he : c = rightCfg (fun _ : Unit => Sum.inr (Sum.inr (13 : Fin 14)))
      (f2_loopReplayCfg x p (some ()) 0 word []) tapes heads := by
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    all_goals
      funext i
      refine Fin.addCases ?_ ?_ i
      · intro j
        simp only [rightCfg, Fin.addCases_left, tapes, heads]
        congr 1
      · intro j
        have hj : j = 0 := Subsingleton.elim _ _
        subst j
        have hf : body.k + 1 + (1 + F.k) ≠ body.k := by omega
        simp [c, rightCfg, f2_loopReplayCfg, f2_loopFrame, hf]
  change ((f2_loopHost body F anchor findMode).tm.runFrom c _).state = _ ∧
    ((f2_loopHost body F anchor findMode).tm.runFrom c _).output = _
  rw [he, f2_loopHost_replay]
  exact ⟨rfl, rfl⟩

/-- An accepting stopped call emits its fixed verdict or replays its full
captured payload, including the empty payload, within `2|output|+3` steps.
**Proof sketch.** The true stop flag dispatches acceptance independently of
payload length. Decision mode emits immediately. Find mode takes one left
move, the length-plus-one rewind, and the length-plus-one replay. -/
private lemma f2_loopHost_accept (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool} (c : Cfg body.k Bool body.State x)
    (word : List Bool) (fuel : Cfg F.k Bool F.State x) (hc : c.state = none) :
    ∃ t ≤ 2 * c.output.length + 3,
      ((f2_loopHost body F anchor findMode).tm.runFrom
        (f2_loopCall body F anchor false c false (some true) word fuel) t).state = none ∧
      ((f2_loopHost body F anchor findMode).tm.runFrom
        (f2_loopCall body F anchor false c false (some true) word fuel) t).output =
          (if findMode then c.output else [true]) := by
  let base := f2_loopCall body F anchor false c false (some true) word fuel
  let flag := fun z : ℤ => if z = 0 then some true else none
  have hf : base = f2_loopFrame body F base (some (.inr (.inr 7))) c.inputPos flag
      (bufferTape word) (bufferTape c.output) 0 c.output.length [] := by
    have hstate : (f2_loopCall body F anchor false c false (some true) word fuel).state =
        some (.inr (.inr (7 : Fin 14))) := by
      simp [f2_loopCall, captureCfg, f2_loopBodyPadded, leftCfg, f2_loopBodyCfg, hc]
    simpa only [hstate] using f2_loopCall_frame body F anchor false c false (some true) word fuel
  have hstep : (f2_loopHost body F anchor findMode).tm.step base =
      if findMode then
        f2_loopFrame body F base (some (.inr (.inr 12))) c.inputPos flag
          (bufferTape word) (bufferTape c.output) 0 (c.output.length - 1) []
      else f2_loopFrame body F base none c.inputPos flag
        (bufferTape word) (bufferTape c.output) 0 c.output.length [true] := by
    conv_lhs => arg 1; rw [hf]
    change (if (f2_loopFrame body F base (some (.inr (.inr 7))) c.inputPos flag
        (bufferTape word) (bufferTape c.output) 0 c.output.length []).workTapeSymbols
          ⟨body.k, by omega⟩ = some true then _
      else f2_loopControlAction body F 0 (some none) (none, 0) (none, 0) none
        (some (.inr (.inr 8)))).apply _ = _
    rw [f2_loopFrame_flag]
    change (if findMode then
      f2_loopControlAction body F 0 none (none, 0) (none, .neg) none (some (.inr (.inr 12)))
      else f2_loopControlAction body F 0 none (none, 0) (none, 0) (some true) none).apply _ = _
    cases findMode <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      rw [f2_loopControl_apply] <;> simp [f2_loopWrite, sub_eq_add_neg]
  cases findMode with
  | false =>
    refine ⟨1, by omega, ?_⟩
    change ((f2_loopHost body F anchor false).tm.step base).state = none ∧
      ((f2_loopHost body F anchor false).tm.step base).output = [true]
    rw [hstep]
    exact ⟨rfl, rfl⟩
  | true =>
    refine ⟨2 * c.output.length + 3, le_refl _, ?_⟩
    have hrun : (f2_loopHost body F anchor true).tm.runFrom base (2 * c.output.length + 3) =
        (f2_loopHost body F anchor true).tm.runFrom
          (f2_loopFrame body F base (some (.inr (.inr 13))) c.inputPos flag
            (bufferTape word) (bufferTape c.output) 0 0 []) (c.output.length + 1) := by
      rw [show 2 * c.output.length + 3 =
          ((c.output.length + 1) + (c.output.length + 1)) + 1 by omega,
        MultiTapeTM.runFrom_succ_eq_step, hstep]
      simp only [if_true]
      rw [MultiTapeTM.runFrom_add, f2_loopHost_payload_rewind body F anchor true base
        c.inputPos flag (bufferTape word) 0 c.output [] c.output.length (le_refl _)]
    change ((f2_loopHost body F anchor true).tm.runFrom base _).state = _ ∧
      ((f2_loopHost body F anchor true).tm.runFrom base _).output = _
    rw [hrun]
    exact f2_loopHost_frame_replay body F anchor true base c.inputPos flag (bufferTape word) 0 c.output

/-- One body round plus all controller work has a uniform local bound.
Acceptance returns the exact payload/verdict; rejection either reaches the
decremented next seam or finishes underflow within the same segment.
**Proof sketch.** For acceptance, replace a padded endpoint by its first
halt, capture every emission, and use the accepting dispatch bound. At most
one symbol is emitted per source step. For rejection, the live seam supplies
the anchor-stop capture; append the complete width-bounded counter dispatch. -/
private lemma f2_loopHost_round (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool} (s next payload : List Bool) (accepted : Bool)
    (word : List Bool) (fuel : Cfg F.k Bool F.State x) (t : ℕ) (ht : 0 < t)
    (hanchor : ∀ u, 0 < u → u < t →
      (body.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord body.k s)) u).state ≠ some anchor)
    (hend : if accepted then
      (body.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).state = none ∧
      (body.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).output = payload
      else body.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t =
        Cfg.ofWords anchor (stateWord body.k next)) :
    ∃ v ≤ 3 * t + 2 * word.length + 5,
      let start := f2_loopCall body F anchor false (Cfg.ofWords anchor (stateWord body.k s)) true none word fuel
      if accepted then
        ((f2_loopHost body F anchor findMode).tm.runFrom start v).state = none ∧
        ((f2_loopHost body F anchor findMode).tm.runFrom start v).output =
          (if findMode then payload else [true])
      else if (f2_loopDebit word).2 then
        (f2_loopHost body F anchor findMode).tm.runFrom start v =
          f2_loopCall body F anchor false (Cfg.ofWords anchor (stateWord body.k next))
            true none (f2_loopDebit word).1 fuel
      else ((f2_loopHost body F anchor findMode).tm.runFrom start v).state = none ∧
        ((f2_loopHost body F anchor findMode).tm.runFrom start v).output =
          (if findMode then [] else [false]) := by
  dsimp only
  let start := Cfg.ofWords (input := x) anchor (stateWord body.k s)
  by_cases ha : accepted = true
  · simp only [ha, if_true] at hend ⊢
    obtain ⟨u, hu, hut, hlive, hhalt, he⟩ := f2_loop_first_halt body.tm start t (by simp [start, Cfg.ofWords]) hend.1
    have hcap := f2_loopHost_halt_return body F anchor findMode start u word fuel hu hlive
      (fun v hv hvu => hanchor v hv (by omega)) hhalt
    obtain ⟨v, hv, hstop, hout⟩ := f2_loopHost_accept body F anchor findMode (body.tm.runFrom start u) word fuel hhalt
    have hw : (body.tm.runFrom start u).output.length ≤ u := by
      simpa [start, Cfg.ofWords] using f2_loop_output_length_le body.tm start u
    refine ⟨u + v, by omega, ?_⟩
    change ((f2_loopHost body F anchor findMode).tm.runFrom
      (f2_loopCall body F anchor false start true none word fuel) (u + v)).state = _ ∧ _
    rw [MultiTapeTM.runFrom_add, hcap]
    refine ⟨hstop, ?_⟩
    rw [hout, he, hend.2]
  · simp only [ha] at hend ⊢
    have hguard : ∀ u < t, (u = 0 ∧ true = true) ∨ (body.tm.runFrom start u).state ≠ some anchor := by
      intro u hu
      by_cases hz : u = 0
      · exact Or.inl ⟨hz, rfl⟩
      · exact Or.inr (hanchor u (by omega) hu)
    have hcap := f2_loopHost_anchor_return body F anchor findMode false start true t word fuel
      (by rw [hend]; rfl)
      (by intro hz; omega) hguard
    change (f2_loopHost body F anchor findMode).tm.runFrom _ (t + 1) = _ at hcap
    have hr : body.tm.runFrom start t = Cfg.ofWords anchor (stateWord body.k next) := hend
    rw [hr] at hcap
    obtain ⟨v, hv, hfinish⟩ := f2_loopHost_reject body F anchor findMode
      {Cfg.ofWords (input := x) anchor (stateWord body.k next) with state := none} word fuel rfl rfl
    refine ⟨(t + 1) + v, by omega, ?_⟩
    change (if (f2_loopDebit word).2 then
      (f2_loopHost body F anchor findMode).tm.runFrom
        (f2_loopCall body F anchor false start true none word fuel) ((t + 1) + v) = _
      else _)
    rw [MultiTapeTM.runFrom_add, hcap]
    exact hfinish

/-- At a canonical call, only the retained fuel bank can be displaced.
All body, flag, counter and capture heads are at zero. -/
private lemma f2_loopCall_heads (body F : FinTM Bool) (anchor : body.State)
    (x s word : List Bool) (fuel : Cfg F.k Bool F.State x) (B : ℕ)
    (hf : ∀ i, -(B : ℤ) ≤ fuel.workTapePos i ∧ fuel.workTapePos i ≤ B) :
    ∀ i, -(B : ℤ) ≤ (f2_loopCall body F anchor false
        (Cfg.ofWords anchor (stateWord body.k s)) true none word fuel).workTapePos i ∧
      (f2_loopCall body F anchor false
        (Cfg.ofWords anchor (stateWord body.k s)) true none word fuel).workTapePos i ≤ B := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [f2_loopCall, captureCfg, f2_loopBodyPadded, leftCfg, f2_loopBodyCfg, Cfg.ofWords]
  · simp only [f2_loopCall, captureCfg, Fin.coe_castSucc, dif_pos j.isLt]
    change -(B : ℤ) ≤ (f2_loopBodyPadded body F anchor
        (Cfg.ofWords anchor (stateWord body.k s)) true none word fuel).workTapePos j ∧
      (f2_loopBodyPadded body F anchor
        (Cfg.ofWords anchor (stateWord body.k s)) true none word fuel).workTapePos j ≤ B
    simp only [f2_loopBodyPadded, leftCfg]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp [Fin.addCases_left, f2_loopBodyCfg, Cfg.ofWords]
    · simp only [Fin.addCases_right]
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp only [Fin.addCases_left]
        omega
      · simpa only [Fin.addCases_right] using hf j

/-- The audit's fixed maximum for the received phase budgets. -/
private def f2_loopHost_bound : ℕ := max 1 (max 9 (3 + 2 + 5))

/-- Configuration contracts for the concrete controller in both output modes.
**Continuation frontier: unproved.** The public corollaries below are conditional
on this one machine-construction obligation; this is not a closed batch.

**Proof sketch.** Run the relocated fuel source to its first halt using
`f2_loopHost_fuel_capture`. Phases 0--5 copy and retain its binary fuel, clear
the capture tape, and rewind the two work heads and the input head. Run
startup with `f2_loopHost_body_capture`; phase 6 clears the flag and releases
the initial seam without a debit. Define each candidate seam using the
iterated body word and `f2_loopDebit` word, retaining the fuel work residue.
`f2_loop_orbit_inv` supplies every local body premise. The body simulation and
first-halt lemmas identify the first stop; W1 preserves its full payload.
Phase 7 either emits/replays that payload or starts the width-bounded
borrow. `f2_loopBorrow_correct` is the standalone counter template to be
lifted into phases 8--10. Final zero underflow and phase 11 belong to the
last rejecting segment. If the last candidate accepts, choose any halted
false/empty terminal. Sum the phase constants with the audit's maximum
ledger. The missing proof is precisely the controller-level lifting and
assembly of these phase contracts, including startup and replay bounds. -/
/- Batch L2 closure: the preceding continuation docstring is retained as
historical evidence. Its listed obligations are discharged below by the phase
lemmas and the canonical family; there is no remaining construction admission. -/
private lemma f2_loopHost_contracts (body F : FinTM Bool) (anchor : body.State)
    (Inv : List Bool → List Bool → Prop)
    (stepF : List Bool → List Bool → List Bool)
    (acceptF : List Bool → List Bool → Bool)
    (out : List Bool → List Bool → List Bool) (findMode : Bool)
    (s0 : List Bool → List Bool) (R T : ℕ → ℕ)
    (hF : F.ComputesFunInTime (fun x => Nat.bits (R x.length)) T)
    (hInv0 : ∀ x : List Bool, Inv x (s0 x))
    (hInvStep : ∀ (x s : List Bool), Inv x s → Inv x (stepF x s))
    (hstart : ∀ x : List Bool, ∃ t ≤ T x.length,
      (∀ t' < t,
        (body.tm.runFrom (body.tm.initCfg x) t').state ≠ some anchor) ∧
      body.tm.runFrom (body.tm.initCfg x) t =
        Cfg.ofWords anchor (stateWord body.k (s0 x)))
    (hround : ∀ (x s : List Bool), Inv x s →
      ∃ t, 0 < t ∧ t ≤ T x.length ∧
        (∀ t', 0 < t' → t' < t →
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t').state
              ≠ some anchor) ∧
        if acceptF x s then
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).state
              = none ∧
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).output
              = out x s
        else
          body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t =
              Cfg.ofWords anchor (stateWord body.k (stepF x s))) :
    ∃ c : ℕ, ∀ x : List Bool,
      ∃ (cfg : ℕ → Cfg (f2_loopHost body F anchor findMode).k Bool
          (f2_loopHost body F anchor findMode).State x) (startup : ℕ),
        startup ≤ c * (T x.length + 1) ∧
        (f2_loopHost body F anchor findMode).tm.runFrom
          ((f2_loopHost body F anchor findMode).tm.initCfg x) startup = cfg 0 ∧
        (∀ i ≤ R x.length, (cfg i).output = []) ∧
        (cfg (R x.length + 1)).state = none ∧
        (cfg (R x.length + 1)).output = (if findMode then [] else [false]) ∧
        (∀ i ≤ R x.length, ∃ t ≤ c * (T x.length + 1),
          if acceptF x ((stepF x)^[i] (s0 x)) then
            ((f2_loopHost body F anchor findMode).tm.runFrom (cfg i) t).state = none ∧
            ((f2_loopHost body F anchor findMode).tm.runFrom (cfg i) t).output =
              (if findMode then out x ((stepF x)^[i] (s0 x)) else [true])
          else (f2_loopHost body F anchor findMode).tm.runFrom (cfg i) t = cfg (i + 1)) ∧
        (∀ i ≤ R x.length, ∀ j,
          -(T x.length : ℤ) ≤ (cfg i).workTapePos j ∧
          (cfg i).workTapePos j ≤ T x.length) ∧
        (∀ j, -((T x.length + c * (T x.length + 1) : ℕ) : ℤ) ≤
          (cfg (R x.length + 1)).workTapePos j ∧
          (cfg (R x.length + 1)).workTapePos j ≤
            (T x.length + c * (T x.length + 1) : ℕ)) := by
  classical
  refine ⟨f2_loopHost_bound, ?_⟩
  intro x
  obtain ⟨fuel, ftime, hfh, hfo, hft, hprepare, hfuel⟩ :=
    f2_loopHost_prepare body F anchor findMode R T hF x
  obtain ⟨btime, hbt, hbguard, hbend⟩ := hstart x
  let words (i : ℕ) := (fun w => (f2_loopDebit w).1)^[i] (Nat.bits (R x.length))
  let orbit (i : ℕ) := (stepF x)^[i] (s0 x)
  let candidate (i : ℕ) := f2_loopCall body F anchor false
    (Cfg.ofWords (input := x) anchor (stateWord body.k (orbit i))) true none (words i) fuel
  have hheads (i : ℕ) (j) :
      -(T x.length : ℤ) ≤ (candidate i).workTapePos j ∧
      (candidate i).workTapePos j ≤ T x.length :=
    f2_loopCall_heads body F anchor x (orbit i) (words i) fuel (T x.length) hfuel j
  have hwidth (i : ℕ) : (words i).length ≤ T x.length := by
    dsimp only [words]
    rw [f2_loopDebit_iterate_length]
    exact f2_loop_fuel_width F R T hF x
  have hsuccess (i : ℕ) (hi : i ≤ R x.length) :
      (f2_loopDebit (words i)).2 = true ↔ i < R x.length := by
    rw [f2_loopDebit_success]
    dsimp only [words]
    rw [f2_loopDebit_iterate_value _ _ hi]
    omega
  -- Each specified seam has its own local contract, including unreachable
  -- seams following an earlier accepting candidate.
  have hlocal : ∀ i ≤ R x.length, ∃ t ≤ f2_loopHost_bound * (T x.length + 1),
      if acceptF x (orbit i) then
        ((f2_loopHost body F anchor findMode).tm.runFrom (candidate i) t).state = none ∧
        ((f2_loopHost body F anchor findMode).tm.runFrom (candidate i) t).output =
          (if findMode then out x (orbit i) else [true])
      else if i < R x.length then
        (f2_loopHost body F anchor findMode).tm.runFrom (candidate i) t = candidate (i + 1)
      else
        ((f2_loopHost body F anchor findMode).tm.runFrom (candidate i) t).state = none ∧
        ((f2_loopHost body F anchor findMode).tm.runFrom (candidate i) t).output =
          (if findMode then [] else [false]) := by
    intro i hi
    obtain ⟨t, htpos, ht, hguard, hend⟩ := hround x (orbit i)
      (f2_loop_orbit_inv Inv stepF s0 hInv0 hInvStep x i)
    obtain ⟨v, hv, hsegment⟩ := f2_loopHost_round body F anchor findMode
      (orbit i) (stepF x (orbit i)) (out x (orbit i)) (acceptF x (orbit i))
      (words i) fuel t htpos hguard hend
    refine ⟨v, ?_, ?_⟩
    · have hw := hwidth i
      change v ≤ 10 * (T x.length + 1)
      omega
    · simpa only [candidate, words, orbit, Function.iterate_succ_apply', hsuccess i hi] using hsegment
  -- Fix one segment witness per seam so the last rejecting segment's actual
  -- endpoint, including underflow and emission, is the chosen terminal.
  let time (i : ℕ) := if hi : i ≤ R x.length then (hlocal i hi).choose else 0
  have htime (i : ℕ) (hi : i ≤ R x.length) :
      time i ≤ f2_loopHost_bound * (T x.length + 1) ∧
      if acceptF x (orbit i) then
        ((f2_loopHost body F anchor findMode).tm.runFrom (candidate i) (time i)).state = none ∧
        ((f2_loopHost body F anchor findMode).tm.runFrom (candidate i) (time i)).output =
          (if findMode then out x (orbit i) else [true])
      else if i < R x.length then
        (f2_loopHost body F anchor findMode).tm.runFrom (candidate i) (time i) = candidate (i + 1)
      else
        ((f2_loopHost body F anchor findMode).tm.runFrom (candidate i) (time i)).state = none ∧
        ((f2_loopHost body F anchor findMode).tm.runFrom (candidate i) (time i)).output =
          (if findMode then [] else [false]) := by
    simpa only [time, dif_pos hi] using (hlocal i hi).choose_spec
  have hlast := htime (R x.length) (le_refl _)
  let terminal := if acceptF x (orbit (R x.length)) then
      {candidate (R x.length + 1) with state := none, output := if findMode then [] else [false]}
    else (f2_loopHost body F anchor findMode).tm.runFrom (candidate (R x.length))
      (time (R x.length))
  have hterminal : terminal.state = none ∧ terminal.output = (if findMode then [] else [false]) := by
    dsimp only [terminal]
    split
    · exact ⟨rfl, rfl⟩
    · rename_i ha
      simpa only [ha, Bool.false_eq_true, ↓reduceIte, Nat.lt_irrefl] using hlast.2
  have hterminalheads (j) :
      -((T x.length + f2_loopHost_bound * (T x.length + 1) : ℕ) : ℤ) ≤
        terminal.workTapePos j ∧
      terminal.workTapePos j ≤ (T x.length + f2_loopHost_bound * (T x.length + 1) : ℕ) := by
    dsimp only [terminal]
    split
    · have h := hheads (R x.length + 1) j
      dsimp only
      omega
    · have hd := f2_head_steps (f2_loopHost body F anchor findMode).tm
        (candidate (R x.length)) (time (R x.length)) j
      have hs := hheads (R x.length) j
      have ht := (htime (R x.length) (le_refl _)).1
      omega
  let cfg (i : ℕ) := if i ≤ R x.length then candidate i else terminal
  have hcfg (i : ℕ) (hi : i ≤ R x.length) : cfg i = candidate i := if_pos hi
  refine ⟨cfg, ftime + (btime + 2), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change ftime + (btime + 2) ≤ 10 * (T x.length + 1)
    omega
  · rw [hcfg 0 (Nat.zero_le _), MultiTapeTM.runFrom_add, hprepare,
      f2_loopHost_start body F anchor findMode (s0 x) btime fuel hbguard hbend]
    simp only [candidate, words, orbit, Function.iterate_zero_apply, hfo]
  · intro i hi
    rw [hcfg i hi]
    rfl
  · simpa only [cfg, if_neg (by omega : ¬R x.length + 1 ≤ R x.length)] using hterminal.1
  · simpa only [cfg, if_neg (by omega : ¬R x.length + 1 ≤ R x.length)] using hterminal.2
  · intro i hi
    have h := htime i hi
    refine ⟨time i, h.1, ?_⟩
    rw [hcfg i hi]
    change (if acceptF x (orbit i) then _ else _)
    by_cases ha : acceptF x (orbit i) = true
    · simp only [ha, if_true] at h ⊢
      simpa only [orbit] using h.2
    · simp only [ha, Bool.false_eq_true, ↓reduceIte] at h ⊢
      by_cases hlt : i < R x.length
      · rw [hcfg (i + 1) (by omega)]
        simpa only [if_pos hlt] using h.2
      · have he : i = R x.length := by omega
        subst i
        rw [show cfg (R x.length + 1) = terminal from if_neg (by omega)]
        simp only [terminal, ha, Bool.false_eq_true, ↓reduceIte]

  · intro i hi j
    rw [hcfg i hi]
    exact hheads i j
  · intro j
    rw [show cfg (R x.length + 1) = terminal from if_neg (by omega)]
    exact hterminalheads j

/-- The first accepting segment returns its own payload; an already-halted
empty-output terminal supplies exhaustion.
**Proof sketch.** Induct on the ordered candidate range. Acceptance at its
head terminates immediately. Otherwise compose the advance with the shifted
induction hypothesis; `find?_map` shifts the selected index back by one.
Thus the payload is tied to the least accepting candidate, including when
that payload is empty. -/
private lemma f2_loop_find_run {k : ℕ} {S : Type*} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (cfg : ℕ → Cfg k Bool S x)
    (accept : ℕ → Bool) (payload : ℕ → List Bool) (B N : ℕ)
    (hend : (cfg N).state = none ∧ (cfg N).output = [])
    (hround : ∀ j < N, ∃ t ≤ B,
      if accept j then
        (tm.runFrom (cfg j) t).state = none ∧
          (tm.runFrom (cfg j) t).output = payload j
      else tm.runFrom (cfg j) t = cfg (j + 1)) :
    ∃ t ≤ N * B, (tm.runFrom (cfg 0) t).state = none ∧
      (tm.runFrom (cfg 0) t).output =
        (match (List.range N).find? accept with | some i => payload i | none => []) := by
  induction N generalizing cfg accept payload with
  | zero => exact ⟨0, by simp, by simpa using hend⟩
  | succ N ih =>
    obtain ⟨t, ht, hc⟩ := hround 0 (by omega)
    by_cases hb : accept 0 = true
    · simp only [hb, ↓reduceIte] at hc
      refine ⟨t, ht.trans ?_, hc.1, ?_⟩
      · exact Nat.le_mul_of_pos_left B (by omega)
      · simpa [List.range_succ_eq_map, hb] using hc.2
    · simp only [hb] at hc
      obtain ⟨s, hs, hhalt, hout⟩ := ih
        (fun j => cfg (j + 1)) (fun j => accept (j + 1))
        (fun j => payload (j + 1)) hend (fun j hj => hround (j + 1) (by omega))
      refine ⟨t + s, ?_, ?_, ?_⟩
      · rw [Nat.succ_mul]; omega
      · rw [MultiTapeTM.runFrom_add, hc]; exact hhalt
      · rw [MultiTapeTM.runFrom_add, hc, hout, List.range_succ_eq_map]
        simp only [List.find?_cons_of_neg hb, List.find?_map, Function.comp_def]
        cases (List.range N).find? (fun j => accept (j + 1)) <;> rfl

/-- Uniform seam positions and segment lengths confine the complete loop,
including an accepting halt and all stationary later times. No round count
occurs in the interval: every next segment restarts at a bounded seam. -/
private lemma f2_segment_heads {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (cfg : ℕ → Cfg k Bool S x) (N B H : ℕ)
    (hseam : ∀ j < N, ∀ i, -(H : ℤ) ≤ (cfg j).workTapePos i ∧
      (cfg j).workTapePos i ≤ H)
    (hend : (cfg N).state = none)
    (hterminal : ∀ i, -((H + B : ℕ) : ℤ) ≤ (cfg N).workTapePos i ∧
      (cfg N).workTapePos i ≤ (H + B : ℕ))
    (hsegment : ∀ j < N, ∃ u ≤ B,
      (tm.runFrom (cfg j) u).state = none ∨ tm.runFrom (cfg j) u = cfg (j + 1)) :
    ∀ t i, -((H + B : ℕ) : ℤ) ≤ (tm.runFrom (cfg 0) t).workTapePos i ∧
      (tm.runFrom (cfg 0) t).workTapePos i ≤ (H + B : ℕ) := by
  induction N generalizing cfg with
  | zero =>
    intro t i
    rw [MultiTapeTM.runFrom_of_halt _ hend]
    exact hterminal i
  | succ N ih =>
    intro t i
    obtain ⟨u, hu, he⟩ := hsegment 0 (by omega)
    have hs := hseam 0 (by omega) i
    have hp (v : ℕ) (hv : v ≤ B) :
        -((H + B : ℕ) : ℤ) ≤ (tm.runFrom (cfg 0) v).workTapePos i ∧
        (tm.runFrom (cfg 0) v).workTapePos i ≤ (H + B : ℕ) := by
      have hh := f2_head_steps tm (cfg 0) v i
      omega
    by_cases ht : t ≤ u
    · exact hp t (ht.trans hu)
    · rw [show t = u + (t - u) by omega, MultiTapeTM.runFrom_add]
      rcases he with he | he
      · rw [MultiTapeTM.runFrom_of_halt _ he]
        exact hp u hu
      · rw [he]
        exact ih (fun j => cfg (j + 1))
          (fun j hj => hseam (j + 1) (by omega)) hend hterminal
          (fun j hj => hsegment (j + 1) (by omega)) (t - u) i

/-- Convert an all-time, origin-centred trajectory bound to total space.
The inclusive interval contains every head position at every prefix. -/
private lemma f2_space_radius (M : FinTM Bool) (x : List Bool) (B : ℕ)
    (h : ∀ t i, -(B : ℤ) ≤ (M.tm.runFrom (M.tm.initCfg x) t).workTapePos i ∧
      (M.tm.runFrom (M.tm.initCfg x) t).workTapePos i ≤ B) (t : ℕ) :
    M.tm.spaceUsed (M.tm.initCfg x) t ≤ M.k * (2 * B + 1) := by
  have hc (i : Fin M.k) : M.tm.spaceUsedByTape (M.tm.initCfg x) t i ≤ 2 * B + 1 := by
    have hs : M.tm.visitedByTapeHead (M.tm.initCfg x) t i ⊆
        Finset.Icc (-(B : ℤ)) (B : ℤ) := by
      intro z hz
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_Icc.mpr (h u i)
    exact (Finset.card_le_card hs).trans (by rw [Int.card_Icc]; omega)
  unfold MultiTapeTM.spaceUsed
  calc
    _ ≤ ∑ _i : Fin M.k, (2 * B + 1) := Finset.sum_le_sum (fun i _ => hc i)
    _ = _ := by simp

/-- A bounded startup followed by reusable seams has all-time space linear
in the common segment budget, independently of the number of rounds. -/
private lemma f2_seamed_space (M : FinTM Bool) (x : List Bool)
    (cfg : ℕ → Cfg M.k Bool M.State x) (N B H startup : ℕ)
    (hstart : startup ≤ B) (hinit : M.tm.runFrom (M.tm.initCfg x) startup = cfg 0)
    (hseam : ∀ j < N, ∀ i, -(H : ℤ) ≤ (cfg j).workTapePos i ∧
      (cfg j).workTapePos i ≤ H)
    (hend : (cfg N).state = none)
    (hterminal : ∀ i, -((H + B : ℕ) : ℤ) ≤ (cfg N).workTapePos i ∧
      (cfg N).workTapePos i ≤ (H + B : ℕ))
    (hsegment : ∀ j < N, ∃ u ≤ B,
      (M.tm.runFrom (cfg j) u).state = none ∨ M.tm.runFrom (cfg j) u = cfg (j + 1))
    (t : ℕ) : M.tm.spaceUsed (M.tm.initCfg x) t ≤ M.k * (2 * (H + B) + 1) := by
  apply f2_space_radius M x (H + B) _ t
  intro u i
  by_cases hu : u ≤ startup
  · have hp := f2_head_steps M.tm (M.tm.initCfg x) u i
    rw [show (M.tm.initCfg x).workTapePos i = 0 from rfl, zero_sub, zero_add] at hp
    omega
  · rw [show u = startup + (u - startup) by omega, MultiTapeTM.runFrom_add, hinit]
    exact f2_segment_heads M.tm cfg N B H hseam hend hterminal hsegment (u - startup) i

/-- The received result-bearing loop, retaining its reusable-seam space bound. -/
private lemma f2_exists_loopFind_space (body F : FinTM Bool) (anchor : body.State)
    (Inv : List Bool → List Bool → Prop)
    (stepF : List Bool → List Bool → List Bool)
    (acceptF : List Bool → List Bool → Bool)
    (out : List Bool → List Bool → List Bool)
    (s0 : List Bool → List Bool) (R T : ℕ → ℕ)
    (hF : F.ComputesFunInTime (fun x => Nat.bits (R x.length)) T)
    (hInv0 : ∀ x : List Bool, Inv x (s0 x))
    (hInvStep : ∀ (x s : List Bool), Inv x s → Inv x (stepF x s))
    (hstart : ∀ x : List Bool, ∃ t ≤ T x.length,
      (∀ t' < t,
        (body.tm.runFrom (body.tm.initCfg x) t').state ≠ some anchor) ∧
      body.tm.runFrom (body.tm.initCfg x) t =
        Cfg.ofWords anchor (stateWord body.k (s0 x)))
    (hround : ∀ (x s : List Bool), Inv x s →
      ∃ t, 0 < t ∧ t ≤ T x.length ∧
        (∀ t', 0 < t' → t' < t →
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t').state
              ≠ some anchor) ∧
        if acceptF x s then
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).state
              = none ∧
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).output
              = out x s
        else
          body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t =
              Cfg.ofWords anchor (stateWord body.k (stepF x s))) :
    ∃ (E : FinTM Bool) (c : ℕ),
      E.ComputesFunInTime
        (fun x => match (List.range (R x.length + 1)).find?
            (fun i => acceptF x ((stepF x)^[i] (s0 x))) with
          | some i => out x ((stepF x)^[i] (s0 x))
          | none => [])
        (fun n => c * (T n + 1) * (R n + 2)) ∧
      ∀ x t, E.tm.spaceUsed (E.tm.initCfg x) t ≤ c * (T x.length + 1) := by
  obtain ⟨c, hc⟩ := f2_loopHost_contracts body F anchor Inv stepF acceptF out true s0 R T
    hF hInv0 hInvStep hstart hround
  let E := f2_loopHost body F anchor true
  have ht : E.ComputesFunInTime
      (fun x => match (List.range (R x.length + 1)).find?
          (fun i => acceptF x ((stepF x)^[i] (s0 x))) with
        | some i => out x ((stepF x)^[i] (s0 x))
        | none => []) (fun n => c * (T n + 1) * (R n + 2)) := by
    intro x
    obtain ⟨cfg, startup, hs, hinit, _, hend, hout, hsegments, hheads, hterminal⟩ := hc x
    obtain ⟨t, ht, hhalt, houtput⟩ := f2_loop_find_run E.tm cfg
      (fun i => acceptF x ((stepF x)^[i] (s0 x)))
      (fun i => out x ((stepF x)^[i] (s0 x))) (c * (T x.length + 1)) (R x.length + 1)
      ⟨hend, by simpa using hout⟩
      (fun j hj => by simpa using hsegments j (by omega))
    have hrun := E.tm.runFrom_add (E.tm.initCfg x) startup t
    rw [hinit] at hrun
    have hcompute : E.ComputesInTime x
        (match (List.range (R x.length + 1)).find?
            (fun i => acceptF x ((stepF x)^[i] (s0 x))) with
          | some i => out x ((stepF x)^[i] (s0 x))
          | none => []) (startup + t) := by
      refine ⟨_, ?_, ?_, rfl⟩
      · rw [hrun]; exact hhalt
      · rw [hrun]; exact houtput
    apply hcompute.mono
    calc startup + t ≤ c * (T x.length + 1) +
          (R x.length + 1) * (c * (T x.length + 1)) := Nat.add_le_add hs ht
      _ = c * (T x.length + 1) * (R x.length + 2) := by
        rw [Nat.mul_comm (R x.length + 1)]
        simp only [Nat.mul_add, Nat.mul_one, Nat.mul_two]
        omega

  let K := E.k * (2 * (c + 1) + 1)
  refine ⟨E, c + K, ?_, ?_⟩
  · intro x
    exact (ht x).mono (Nat.mul_le_mul_right _
      (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)))
  · intro x t
    obtain ⟨cfg, startup, hs, hinit, _, hend, _, hsegments, hheads, hterminal⟩ := hc x
    have h := f2_seamed_space E x cfg (R x.length + 1) (c * (T x.length + 1))
      (T x.length) startup hs hinit (fun j hj => hheads j (by omega)) hend hterminal
      (by
        intro j hj
        obtain ⟨u, hu, he⟩ := hsegments j (by omega)
        refine ⟨u, hu, ?_⟩
        split at he
        · exact Or.inl he.1
        · exact Or.inr he) t
    have hb : 2 * (T x.length + c * (T x.length + 1)) + 1 ≤
        (2 * (c + 1) + 1) * (T x.length + 1) := by
      have he : (2 * (c + 1) + 1) * (T x.length + 1) =
          2 * (T x.length + c * (T x.length + 1)) + T x.length + 3 := by ring
      omega
    calc
      _ ≤ E.k * ((2 * (c + 1) + 1) * (T x.length + 1)) :=
        h.trans (Nat.mul_le_mul_left _ hb)
      _ = K * (T x.length + 1) := by dsimp [K]; ring
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.le_add_left _ _)

/-- The audited split-search step preserves every existing candidate bit;
at the one-past-end state it stalls. -/
private def f2_splitStep (w s : List Bool) : List Bool :=
  if s.length ≤ w.length then s ++ [true] else s

/-- Split-search acceptance is the exact padding length equation. -/
private def f2_splitAccept (C e : ℕ) (w s : List Bool) : Bool :=
  decide (s.length + C * (s.length + 1) ^ e = w.length)

/-- The length invariant is closed even on arbitrary candidate bit patterns. -/
private lemma f2_splitStep_inv (w s : List Bool) (hs : s.length ≤ w.length + 1) :
    (f2_splitStep w s).length ≤ w.length + 1 := by
  unfold f2_splitStep
  split <;> simp_all <;> omega

/-- All orbit points tested by the loop are precisely the unary candidates.
**Proof sketch.** Before fuel is exhausted the current length is the iteration
index, so the step appends one true. The extra one-past-end state is included. -/
private lemma f2_splitStep_orbit (w : List Bool) : ∀ i, i ≤ w.length + 1 →
    (f2_splitStep w)^[i] [] = List.replicate i true := by
  intro i
  induction i with
  | zero => intro hi; rfl
  | succ i ih =>
    intro hi
    rw [Function.iterate_succ_apply', ih (by omega)]
    simp only [f2_splitStep, List.length_replicate, if_pos (by omega : i ≤ w.length)]
    exact (List.replicate_succ').symm

/-- Extensional equality of search predicates on the searched list preserves
both the least-success index and failure. -/
private lemma f2_catalogFind_congr {α : Type} (xs : List α) (p q : α → Bool)
    (h : ∀ a ∈ xs, p a = q a) : xs.find? p = xs.find? q := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.find?_cons, h a (by simp)]
    rw [ih (fun b hb => h b (by simp [hb]))]

/-- The orbit predicate and `solveSplit` use the same finite search, including
its unsuccessful branch. The Boolean equality is converted explicitly. -/
private lemma f2_splitFind_eq (C e : ℕ) (w : List Bool) :
    (List.range (w.length + 1)).find?
      (fun i => f2_splitAccept C e w ((f2_splitStep w)^[i] [])) = solveSplit C e w.length := by
  apply f2_catalogFind_congr
  intro i hi
  have hi' : i ≤ w.length := by simpa only [List.mem_range, Nat.lt_succ_iff] using hi
  rw [f2_splitStep_orbit w i (by omega)]
  apply Bool.eq_iff_iff.mpr
  simp only [f2_splitAccept, List.length_replicate, decide_eq_true_eq, beq_iff_eq]

/-- Failed split search is equivalent to rejecting every candidate within fuel. -/
private lemma f2_splitFind_none (C e : ℕ) (w : List Bool) :
    solveSplit C e w.length = none ↔
      ∀ i ≤ w.length, f2_splitAccept C e w ((f2_splitStep w)^[i] []) = false := by
  rw [← f2_splitFind_eq, List.find?_eq_none]
  simp only [List.mem_range, Nat.lt_succ_iff, Bool.not_eq_true]

/-- Each successful orbit payload is exactly the split at the returned index;
exhaustion returns the same empty word on both sides. -/
private lemma f2_splitLoop_result (C e : ℕ) (w : List Bool) :
    (match (List.range (w.length + 1)).find?
        (fun i => f2_splitAccept C e w ((f2_splitStep w)^[i] [])) with
      | some i => pairEncode (w.take ((f2_splitStep w)^[i] []).length)
          (w.drop ((f2_splitStep w)^[i] []).length)
      | none => []) =
    (match solveSplit C e w.length with
      | some i => pairEncode (w.take i) (w.drop i)
      | none => []) := by
  rw [f2_splitFind_eq]
  cases hs : solveSplit C e w.length with
  | none => rfl
  | some i =>
    have hi := List.mem_of_find?_eq_some hs
    have hi' : i ≤ w.length := by simpa only [List.mem_range, Nat.lt_succ_iff] using hi
    simp only [f2_splitStep_orbit w i (by omega), List.length_replicate]

/-- The loop overhead raises the body's polynomial exponent by exactly one.
**Proof sketch.** Bound the additive one by `(n+1)^(e+1)` and the factor `n+2`
by `2(n+1)`, then combine powers. This includes `n=0` and `e=0`. -/
private lemma f2_splitLoop_bound (c A e n : ℕ) :
    c * (A * (n + 1) ^ (e + 1) + 1) * (n + 2) ≤
      (2 * c * (A + 1)) * (n + 1) ^ (e + 2) := by
  have hp : 1 ≤ (n + 1) ^ (e + 1) := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hfirst : A * (n + 1) ^ (e + 1) + 1 ≤ (A + 1) * (n + 1) ^ (e + 1) := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  calc
    _ ≤ c * ((A + 1) * (n + 1) ^ (e + 1)) * (2 * (n + 1)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left c hfirst) (by omega)
    _ = _ := by rw [show e + 2 = (e + 1) + 1 by omega, Nat.pow_succ]; ring

/-- A physical input position after consuming a unary count, saturated at the
right boundary. -/
private def f2_splitPos (w : List Bool) (j : ℕ) : Fin (w.length + 2) :=
  ⟨min j w.length + 1, by omega⟩

/-- A saturated countdown read is blank exactly after all input bits. -/
private lemma f2_splitPos_read {k : ℕ} {S : Type} (w : List Bool)
    (cfg : Cfg k Bool S w) (j : ℕ) (hp : cfg.inputPos = f2_splitPos w j) :
    cfg.inputSymbol = if h : j < w.length then some (w[j]'h) else none := by
  by_cases hj : j < w.length
  · rw [dif_pos hj]
    exact inputSymbolInner j
      (by simp [hp, f2_splitPos, Nat.min_eq_left (by omega : j ≤ w.length), Nat.add_comm]) hj
  · rw [dif_neg hj]
    simp [Cfg.inputSymbol, hp, f2_splitPos, Nat.min_eq_right (by omega : w.length ≤ j)]

/-- A forward move increments a saturated unary countdown position. -/
private lemma f2_splitPos_succ (w : List Bool) (j : ℕ) :
    moveInputPos (f2_splitPos w j) .pos = f2_splitPos w (j + 1) := by
  by_cases hj : j < w.length
  · rw [moveInputPos_pos_of_ne_right _ (by simp [f2_splitPos] <;> omega)]
    apply Fin.ext
    simp only [f2_splitPos, Fin.val_mk]
    omega
  · have he : f2_splitPos w j = ⟨w.length + 1, by omega⟩ := by
      apply Fin.ext
      simp [f2_splitPos, Nat.min_eq_right (by omega : w.length ≤ j)]
    rw [he, SignType.pos_eq_one, moveInputPos_rightBoundary]
    apply Fin.ext
    simp [f2_splitPos, Nat.min_eq_right (by omega : w.length ≤ j + 1)]

/-- A partially cleared unary scratch word, with its remaining suffix exposed. -/
private def f2_splitScratch (q j : ℕ) (z : ℤ) : Option Bool :=
  if (j : ℤ) ≤ z ∧ z < q then some true else none

/-- Clearing the exposed scratch cell advances the cleared prefix by one. -/
private lemma f2_splitScratch_erase (q j : ℕ) :
    Function.update (f2_splitScratch q j) (j : ℤ) none = f2_splitScratch q (j + 1) := by
  funext z
  by_cases hz : z = (j : ℤ)
  · subst z; simp [f2_splitScratch]
  · rw [Function.update_of_ne hz]
    have he : ((j : ℤ) ≤ z ∧ z < q) ↔ (((j + 1 : ℕ) : ℤ) ≤ z ∧ z < q) := by omega
    simp only [f2_splitScratch, he]

/-- The rejection cleanup preserves all candidate bits, appends only within
the input-length range, clears every unary scratch tape, and restores heads.
State 4 is an absorbing return seam, suitable for a first-return embedding. -/
private def f2_splitRestoreTM (k : ℕ) : FinTM Bool where
  k := k + 1
  State := Fin 5 × Bool
  tm := {
    q₀ := (0, false)
    tr := fun q inp work => match q.1.val with
      | 0 => match work 0 with
        | some _ => ⟨.pos, Fin.cases (none, .pos) (fun _ => (some none, .pos)),
            none, some (0, q.2 || inp.isNone)⟩
        | none => ⟨0, Fin.cases (if q.2 then (none, .neg) else (some (some true), .neg))
            (fun _ => (some none, .neg)), none, some (1, false)⟩
      | 1 => match work 0 with
        | some _ => ⟨0, fun _ => (none, .neg), none, some (1, false)⟩
        | none => ⟨0, fun _ => (none, .pos), none, some (2, false)⟩
      | 2 => controlAction .neg (some (3, false))
      | 3 => match inp with
        | some _ => controlAction .neg (some (3, false))
        | none => controlAction .pos (some (4, false))
      | _ => controlAction 0 (some (4, false)) }

/-- The clearing scan has consumed `j` candidate cells and erased exactly that
prefix on each scratch tape; the physical input tracks the same count. -/
private def f2_splitRestoreScan (k : ℕ) (w s : List Bool) (j : ℕ) :
    Cfg (k + 1) Bool (f2_splitRestoreTM k).State w :=
  ⟨some (0, decide (w.length < j)), f2_splitPos w j,
    Fin.cases (bufferTape s) (fun _ => f2_splitScratch (s.length + 1) j), fun _ => j, []⟩

/-- The silent cleanup scans each candidate bit once, including false bits.
**Proof sketch.** Each transition preserves tape 0, clears one cell on every
scratch tape, and advances all heads. The overflow flag records precisely
whether more candidate cells than native input cells have been consumed. -/
private lemma f2_splitRestore_scan (k : ℕ) (w s : List Bool) : ∀ j, j ≤ s.length →
    (f2_splitRestoreTM k).tm.runFrom (f2_splitRestoreScan k w s 0) j =
      f2_splitRestoreScan k w s j := by
  intro j
  induction j with
  | zero => intro hj; rfl
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hw : (f2_splitRestoreScan k w s j).workTapeSymbols 0 = some (s[j]'(by omega)) := by
      simp [f2_splitRestoreScan, Cfg.workTapeSymbols,
        List.getElem?_eq_getElem (by omega : j < s.length)]
    have hin := f2_splitPos_read w (f2_splitRestoreScan k w s j) j rfl
    unfold MultiTapeTM.step
    change ((f2_splitRestoreTM k).tm.tr (0, decide (w.length < j)) _ _).apply _ = _
    simp only [f2_splitRestoreTM, hw]
    refine Cfg.ext ?_ (f2_splitPos_succ w j) ?_ ?_ rfl
    · change some (0, decide (w.length < j) ||
        (f2_splitRestoreScan k w s j).inputSymbol.isNone) = some (0, decide (w.length < j + 1))
      rw [hin]
      by_cases hjn : j < w.length
      · simp [hjn, show ¬w.length < j by omega, show ¬w.length < j + 1 by omega]
      · simp [hjn, show w.length < j + 1 by omega]
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · exact f2_splitScratch_erase _ _
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i <;> simp [Action.apply, f2_splitRestoreScan]

/-- A cleaned configuration has only the candidate on tape zero; all work
heads are synchronized and the physical output is empty. -/
private def f2_splitRestoreClean (k : ℕ) (w s : List Bool)
    (q : (f2_splitRestoreTM k).State) (p : Fin (w.length + 2)) (h : ℤ) :
    Cfg (k + 1) Bool (f2_splitRestoreTM k).State w :=
  ⟨some q, p, Fin.cases (bufferTape s) (fun _ => fun _ => none), fun _ => h, []⟩

/-- The end-of-scan step clears the final extra scratch cell and appends to
tape 0 exactly when the old candidate length is at most the input length. -/
private lemma f2_splitRestore_append (k : ℕ) (w s : List Bool) :
    (f2_splitRestoreTM k).tm.step (f2_splitRestoreScan k w s s.length) =
      f2_splitRestoreClean k w (f2_splitStep w s) (1, false)
        (f2_splitPos w s.length) (s.length - 1) := by
  have hw : (f2_splitRestoreScan k w s s.length).workTapeSymbols 0 = none := by
    simp [f2_splitRestoreScan, Cfg.workTapeSymbols]
  unfold MultiTapeTM.step
  change ((f2_splitRestoreTM k).tm.tr (0, decide (w.length < s.length)) _ _).apply _ = _
  simp only [f2_splitRestoreTM, hw]
  by_cases hs : s.length ≤ w.length
  · have hflag : decide (w.length < s.length) = false := by simp; omega
    rw [hflag]
    refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa [Action.apply, f2_splitRestoreClean, f2_splitStep, hs] using (bufferTape_append s true).symm
      · change Function.update (f2_splitScratch (s.length + 1) s.length) (s.length : ℤ) none = _
        rw [f2_splitScratch_erase]
        funext z
        simp [f2_splitRestoreClean, f2_splitScratch]
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i <;> simp [Action.apply, f2_splitRestoreScan, f2_splitRestoreClean, sub_eq_add_neg]
  · have hflag : decide (w.length < s.length) = true := by simp; omega
    rw [hflag]
    refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [Action.apply, f2_splitRestoreScan, f2_splitRestoreClean, f2_splitStep, hs]
      · change Function.update (f2_splitScratch (s.length + 1) s.length) (s.length : ℤ) none = _
        rw [f2_splitScratch_erase]
        funext z
        simp [f2_splitRestoreClean, f2_splitScratch]
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i <;> simp [Action.apply, f2_splitRestoreScan, f2_splitRestoreClean, sub_eq_add_neg]

/-- Candidate-guided rewind restores every head, including heads on tapes
that have already been cleared. No candidate bit is altered. -/
private lemma f2_splitRestore_rewind (k : ℕ) (w s : List Bool) (p : Fin (w.length + 2)) :
    ∀ j, j ≤ s.length →
      (f2_splitRestoreTM k).tm.runFrom
        (f2_splitRestoreClean k w s (1, false) p ((j : ℤ) - 1)) (j + 1) =
        f2_splitRestoreClean k w s (2, false) p 0 := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    simp only [MultiTapeTM.step, f2_splitRestoreClean, f2_splitRestoreTM, Cfg.workTapeSymbols,
      Fin.cases_zero, Nat.cast_zero, zero_sub, bufferTape_left]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext i; simp [Action.apply, f2_splitRestoreScan]
  | succ j ih =>
    intro hj
    have hs : (f2_splitRestoreTM k).tm.step
        (f2_splitRestoreClean k w s (1, false) p (((j + 1 : ℕ) : ℤ) - 1)) =
        f2_splitRestoreClean k w s (1, false) p ((j : ℤ) - 1) := by
      have he : (((j + 1 : ℕ) : ℤ) - 1) = j := by omega
      rw [he]
      simp only [MultiTapeTM.step, f2_splitRestoreClean, f2_splitRestoreTM, Cfg.workTapeSymbols,
        Fin.cases_zero, bufferTape_nat, List.getElem?_eq_getElem (by omega : j < s.length)]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext i; simp [Action.apply, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Complete rejection cleanup restores exactly the audited state-word seam.
It works for arbitrary candidate bits, and its one-past-end stall is silent.
**Proof sketch.** Scan and erase `|s|` cells, handle the final scratch cell,
rewind synchronized heads along the preserved candidate, then rewind input.
The cost is at most `2|s|+|w|+5`, and every transition is silent. -/
private lemma f2_splitRestore_run (k : ℕ) (w s : List Bool) :
    ∃ t ≤ 2 * s.length + w.length + 5,
      (f2_splitRestoreTM k).tm.runFrom (f2_splitRestoreScan k w s 0) t =
        Cfg.ofWords (4, false) (stateWord (k + 1) (f2_splitStep w s)) := by
  have hlen : s.length ≤ (f2_splitStep w s).length := by
    unfold f2_splitStep
    split <;> simp
  obtain ⟨r, hr, he⟩ := f2_catalogRewind (f2_splitRestoreTM k).tm (2, false) (3, false)
    (some (4, false)) (fun _ _ => rfl) (fun inp _ => by cases inp <;> rfl)
    (f2_splitRestoreClean k w (f2_splitStep w s) (2, false) (f2_splitPos w s.length) 0) rfl
  have hp : (f2_splitPos w s.length).val ≤ w.length + 1 := by simp [f2_splitPos] <;> omega
  have hfirst : (f2_splitRestoreTM k).tm.runFrom (f2_splitRestoreScan k w s 0) (s.length + 1) =
      f2_splitRestoreClean k w (f2_splitStep w s) (1, false) (f2_splitPos w s.length) (s.length - 1) := by
    rw [MultiTapeTM.runFrom_succ_eq_step', f2_splitRestore_scan k w s _ (le_refl _),
      f2_splitRestore_append]
  refine ⟨(s.length + 1) + (s.length + 1) + r, ?_, ?_⟩
  · change r ≤ (f2_splitPos w s.length).val + 2 at hr
    omega
  · rw [MultiTapeTM.runFrom_add _ _ r,
      MultiTapeTM.runFrom_add _ (s.length + 1) (s.length + 1),
      hfirst, f2_splitRestore_rewind k w (f2_splitStep w s) _ _ hlen, he]
    refine Cfg.ext ?_ ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i <;>
        simp [f2_splitRestoreClean, Cfg.ofWords, stateWord]
    · rfl
    · rfl

/-- Replace source emissions by native-input consumption. Tape zero retains
the candidate; the source bank occupies successor-indexed tapes. A finite
flag remembers consumption past the native right boundary. -/
private def f2_splitCountAction {k : ℕ} {S H : Type} (emb : S → Bool → H) (ret : Bool → H)
    (over : Bool) (inp : Option Bool) (a : Action k Bool S) : Action (k + 1) Bool H :=
  let over' := over || (a.output.isSome && inp.isNone)
  ⟨if a.output.isSome then .pos else 0, Fin.cases (none, 0) a.workTapes, none,
    some (match a.state with | some q => emb q over' | none => ret over')⟩

/-- Source configurations use an empty virtual input and arbitrary initialized
work tapes. Their output length is consumed after the candidate's length. -/
private def f2_splitCountCfg {k : ℕ} {S H : Type} (emb : S → Bool → H) (ret : Bool → H)
    (w s : List Bool) (c : Cfg k Bool S []) : Cfg (k + 1) Bool H w :=
  let over := decide (w.length < s.length + c.output.length)
  ⟨some (match c.state with | some q => emb q over | none => ret over),
    f2_splitPos w (s.length + c.output.length), Fin.cases (bufferTape s) c.workTapes,
    Fin.cases 0 c.workTapePos, []⟩

/-- Consuming one additional symbol updates the saturation flag exactly. -/
private lemma f2_splitCount_over {k : ℕ} {S : Type} (w : List Bool)
    (cfg : Cfg k Bool S w) (j : ℕ) (hp : cfg.inputPos = f2_splitPos w j) :
    (decide (w.length < j) || cfg.inputSymbol.isNone) = decide (w.length < j + 1) := by
  rw [f2_splitPos_read w cfg j hp]
  by_cases hj : j < w.length
  · simp [hj, show ¬w.length < j by omega, show ¬w.length < j + 1 by omega]
  · simp [hj, show w.length < j + 1 by omega]

/-- One transformed step consumes exactly its optional source emission,
preserves the candidate, and reproduces all source-bank writes and moves.
**Proof sketch.** Split on the optional output and on tape zero versus source
tapes. The one-emission case is precisely the saturated-position increment
and overflow update; the zero-emission case leaves both unchanged. -/
private lemma f2_splitCount_apply {k : ℕ} {S H : Type} (emb : S → Bool → H) (ret : Bool → H)
    (w s : List Bool) (c : Cfg k Bool S []) (a : Action k Bool S) :
    (f2_splitCountAction emb ret (decide (w.length < s.length + c.output.length))
      (f2_splitCountCfg emb ret w s c).inputSymbol a).apply (f2_splitCountCfg emb ret w s c) =
      f2_splitCountCfg emb ret w s (a.apply c) := by
  have hflag := f2_splitCount_over w (f2_splitCountCfg emb ret w s c)
    (s.length + c.output.length) rfl
  cases ho : a.output with
  | none =>
    refine Cfg.ext ?_ ?_ ?_ ?_ rfl
    · simp [f2_splitCountAction, f2_splitCountCfg, Action.apply, ho]
    · simpa [f2_splitCountAction, f2_splitCountCfg, Action.apply, ho] using
        moveInputPos_zero (f2_splitPos w (s.length + c.output.length))
    · funext i; refine Fin.cases ?_ (fun i => ?_) i <;> rfl
    · funext i; refine Fin.cases ?_ (fun i => ?_) i <;>
        simp [f2_splitCountAction, f2_splitCountCfg, Action.apply]
  | some b =>
    refine Cfg.ext ?_ ?_ ?_ ?_ rfl
    · simpa [f2_splitCountAction, f2_splitCountCfg, Action.apply, ho, Nat.add_assoc] using
        congrArg (fun flag => some (match a.state with | some q => emb q flag | none => ret flag)) hflag
    · simpa [f2_splitCountAction, f2_splitCountCfg, Action.apply, ho, Nat.add_assoc] using
        f2_splitPos_succ w (s.length + c.output.length)
    · funext i; refine Fin.cases ?_ (fun i => ?_) i <;> rfl
    · funext i; refine Fin.cases ?_ (fun i => ?_) i <;>
        simp [f2_splitCountAction, f2_splitCountCfg, Action.apply]

/-- A counted source run follows the original work-bank computation exactly,
including a final emitting halt, while consuming its output on native input.
**Proof sketch.** Empty virtual input always reads blank. Apply the one-step
correspondence through the source's first halt, as in `capture_run`; the
physical output stays empty throughout. -/
private lemma f2_splitCount_run {k : ℕ} {S H : Type}
    (tm : MultiTapeTM k Bool S) (host : MultiTapeTM (k + 1) Bool H)
    (emb : S → Bool → H) (ret : Bool → H)
    (hagree : ∀ q over inp work, host.tr (emb q over) inp work =
      f2_splitCountAction emb ret over inp (tm.tr q none (fun i => work i.succ)))
    (w s : List Bool) (c : Cfg k Bool S []) (t : ℕ)
    (hlive : ∀ j < t, ¬(tm.runFrom c j).Halted) :
    host.runFrom (f2_splitCountCfg emb ret w s c) t =
      f2_splitCountCfg emb ret w s (tm.runFrom c t) := by
  have hstep (d : Cfg k Bool S []) (hs : ¬d.Halted) :
      host.step (f2_splitCountCfg emb ret w s d) = f2_splitCountCfg emb ret w s (tm.step d) := by
    cases hq : d.state with
    | none => exact False.elim (hs hq)
    | some q =>
      have hstate : (f2_splitCountCfg emb ret w s d).state =
          some (emb q (decide (w.length < s.length + d.output.length))) := by
        simp [f2_splitCountCfg, hq]
      have hsource : d.inputSymbol = none := by
        unfold Cfg.inputSymbol
        split_ifs with h₀ h₁
        · rfl
        · rfl
        · have hp := d.inputPos.isLt
          simp only [Fin.ext_iff, Fin.val_zero] at h₀
          simp only [List.length_nil] at hp
          simp only [List.length_nil, Nat.zero_add, Nat.cast_one, Fin.ext_iff, Fin.val_one] at h₁
          omega
      have hwork : (fun i => (f2_splitCountCfg emb ret w s d).workTapeSymbols i.succ) =
          d.workTapeSymbols := by
        funext i; simp [f2_splitCountCfg, Cfg.workTapeSymbols]
      simp only [MultiTapeTM.step, hstate, hq]
      rw [hagree, hwork, hsource]
      exact f2_splitCount_apply emb ret w s d _
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (fun j hj => hlive j (by omega)),
      hstep _ (hlive t (by omega)), MultiTapeTM.runFrom_succ_eq_step']

/-- The in-file generator's loop phase ends with every unary scratch head
back at zero, ready for the restoration controller. The source input is empty;
its loop side length is supplied by the initialized work tapes.
**Proof sketch.** Run the existing exact nested-loop invariant over the full
box and then take the final halting transition. No fresh generator proof is
assumed, and the zero coefficient is included. -/
private lemma f2_splitPoly_loop_end (c C q : ℕ) (hq : 0 < q) :
    (f2_catalogPolyUnaryTM c C).tm.runFrom
      (f2_catalogPolyCfg (C := C) [] q (.loop (Fin.last c)) (fun _ => 0) [])
      (f2_catalogPolyCost q C (c + 1) + 1) =
      {f2_catalogPolyCfg (C := C) [] q (.advance (Fin.last (c + 1))) (fun _ => 0)
        (List.replicate (C * q ^ (c + 1)) true) with state := none} := by
  have hl := f2_catalogPoly_loop (c := c) (C := C) [] q hq c (by omega)
    (fun _ => 0) (by simp) [] q 0 (by omega)
  have hout : q * (C * q ^ c) = C * q ^ (c + 1) := by rw [Nat.pow_succ]; ring
  have hloop : (f2_catalogPolyUnaryTM c C).tm.runFrom
      (f2_catalogPolyCfg (C := C) [] q (.loop (Fin.last c)) (fun _ => 0) [])
      (f2_catalogPolyCost q C (c + 1)) =
      f2_catalogPolyCfg (C := C) [] q (.advance (Fin.last (c + 1))) (fun _ => 0)
        (List.replicate (C * q ^ (c + 1)) true) := by
    simpa [f2_catalogPolyCost, hout] using hl
  rw [MultiTapeTM.runFrom_succ_eq_step', hloop]
  simp only [MultiTapeTM.step, f2_catalogPolyCfg, f2_catalogPolyUnaryTM, Fin.val_last,
    Nat.lt_irrefl, ↓reduceDIte]
  refine Cfg.ext rfl ?_ rfl ?_ ?_
  · rfl
  · funext i; simp [MultiTapeTM.step, f2_catalogPolyUnaryTM, Action.apply, f2_catalogPolyCfg]
  · simp [MultiTapeTM.step, f2_catalogPolyUnaryTM, Action.apply, f2_catalogPolyCfg]

/-- A run reaching an absorbing control state has a least such entry, and its
configuration at that first entry is already the final configuration.
**Proof sketch.** Choose the least hit. Absorption makes its entire suffix
constant, so the bounded endpoint identifies the first-hit configuration. -/
private lemma f2_catalogFirstEntry {k : ℕ} {S : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (q : S) (c d : Cfg k Bool S w) (T : ℕ)
    (hfix : ∀ z : Cfg k Bool S w, z.state = some q → tm.step z = z)
    (hd : d.state = some q) (hT : tm.runFrom c T = d) :
    ∃ t ≤ T, (∀ j < t, (tm.runFrom c j).state ≠ some q) ∧ tm.runFrom c t = d := by
  classical
  have hh : ∃ t, (tm.runFrom c t).state = some q := ⟨T, by rw [hT, hd]⟩
  let t := Nat.find hh
  have ht : t ≤ T := Nat.find_min' hh (by rw [hT, hd])
  have hs : (tm.runFrom c t).state = some q := Nat.find_spec hh
  refine ⟨t, ht, fun j hj => Nat.find_min hh hj, ?_⟩
  have hconst : tm.runFrom (tm.runFrom c t) (T - t) = tm.runFrom c t :=
    Function.iterate_fixed (hfix _ hs) _
  have he := tm.runFrom_add c t (T - t)
  rw [Nat.add_sub_of_le ht, hT, hconst] at he
  exact he.symm

/-- The cleanup's return seam is absorbing, so its exact restoration can be
exported with positive duration and no earlier return-state visit. -/
private lemma f2_splitRestore_first (k : ℕ) (w s : List Bool) :
    ∃ t, 0 < t ∧ t ≤ 2 * s.length + w.length + 5 ∧
      (∀ j < t, ((f2_splitRestoreTM k).tm.runFrom (f2_splitRestoreScan k w s 0) j).state
        ≠ some (4, false)) ∧
      (f2_splitRestoreTM k).tm.runFrom (f2_splitRestoreScan k w s 0) t =
        Cfg.ofWords (4, false) (stateWord (k + 1) (f2_splitStep w s)) := by
  obtain ⟨T, hTle, hT⟩ := f2_splitRestore_run k w s
  have hfix (z : Cfg (k + 1) Bool (f2_splitRestoreTM k).State w)
      (hz : z.state = some (4, false)) : (f2_splitRestoreTM k).tm.step z = z := by
    unfold MultiTapeTM.step
    rw [hz]
    change (controlAction 0 (some (4, false))).apply z = z
    rw [controlAction_apply, moveInputPos_zero]
    cases z
    simp_all
  obtain ⟨t, ht, hi, he⟩ := f2_catalogFirstEntry (f2_splitRestoreTM k).tm (4, false)
    (f2_splitRestoreScan k w s 0) _ T hfix rfl hT
  refine ⟨t, ?_, ht.trans hTle, hi, he⟩
  by_contra h
  have ht0 : t = 0 := by omega
  have hstate := congrArg Cfg.state he
  simp only [ht0, MultiTapeTM.runFrom_zero, f2_splitRestoreScan, Cfg.ofWords,
    Option.some.injEq, Prod.mk.injEq] at hstate
  have hf := congrArg (fun q : (f2_splitRestoreTM k).State => q.1.val) hstate
  norm_num at hf

/-- Native countdown acceptance is exactly equality of the consumed length
and the original input length; overflow and short counts both reject. -/
private lemma f2_splitCount_accept {k : ℕ} {S H : Type} (emb : S → Bool → H) (ret : Bool → H)
    (w s : List Bool) (c : Cfg k Bool S []) :
    (!decide (w.length < s.length + c.output.length) &&
      (f2_splitCountCfg emb ret w s c).inputSymbol.isNone) =
        decide (s.length + c.output.length = w.length) := by
  rw [f2_splitPos_read w (f2_splitCountCfg emb ret w s c) (s.length + c.output.length) rfl]
  by_cases hlt : s.length + c.output.length < w.length
  · simp [hlt, show ¬s.length + c.output.length = w.length by omega]
  · by_cases he : s.length + c.output.length = w.length
    · simp [he]
    · simp [hlt, he, show w.length < s.length + c.output.length by omega]

/-- The counted simulation can be stopped at the source's first halt without
losing the exact initialized-bank endpoint. This removes any padded halted
tail from a source time bound before entering the next controller phase. -/
private lemma f2_splitCount_firstHalt {k : ℕ} {S H : Type}
    (tm : MultiTapeTM k Bool S) (host : MultiTapeTM (k + 1) Bool H)
    (emb : S → Bool → H) (ret : Bool → H)
    (hagree : ∀ q over inp work, host.tr (emb q over) inp work =
      f2_splitCountAction emb ret over inp (tm.tr q none (fun i => work i.succ)))
    (w s : List Bool) (c d : Cfg k Bool S []) (T : ℕ)
    (hd : d.state = none) (hT : tm.runFrom c T = d) :
    ∃ t ≤ T, host.runFrom (f2_splitCountCfg emb ret w s c) t = f2_splitCountCfg emb ret w s d := by
  classical
  have hh : ∃ t, (tm.runFrom c t).state = none := ⟨T, by rw [hT, hd]⟩
  let t := Nat.find hh
  have ht : t ≤ T := Nat.find_min' hh (by rw [hT, hd])
  have hs : (tm.runFrom c t).state = none := Nat.find_spec hh
  have he := tm.runFrom_add c t (T - t)
  rw [Nat.add_sub_of_le ht, hT, tm.runFrom_of_halt _ hs] at he
  refine ⟨t, ht, ?_⟩
  rw [f2_splitCount_run tm host emb ret hagree w s c t (fun j hj => Nat.find_min hh hj), ← he]

/-- Prepare the polynomial loop bank by copying the candidate's length to all
scratch tapes in parallel, adding the extra side-length cell, and rewinding
all work heads along the untouched candidate. State 2 is the return seam. -/
private def f2_splitPrepareTM (k : ℕ) : FinTM Bool where
  k := k + 1
  State := Fin 3 × Bool
  tm := {
    q₀ := (0, false)
    tr := fun q inp work => match q.1.val with
      | 0 => match work 0 with
        | some _ => ⟨.pos, Fin.cases (none, .pos) (fun _ => (some (some true), .pos)),
            none, some (0, q.2 || inp.isNone)⟩
        | none => ⟨0, Fin.cases (none, .neg) (fun _ => (some (some true), .neg)),
            none, some (1, q.2)⟩
      | 1 => match work 0 with
        | some _ => ⟨0, fun _ => (none, .neg), none, some (1, q.2)⟩
        | none => ⟨0, fun _ => (none, .pos), none, some (2, q.2)⟩
      | _ => controlAction 0 (some (2, q.2)) }

/-- During preparation, every scratch tape contains the length scanned so far. -/
private def f2_splitPrepareScan (k : ℕ) (w s : List Bool) (j : ℕ) :
    Cfg (k + 1) Bool (f2_splitPrepareTM k).State w :=
  ⟨some (0, decide (w.length < j)), f2_splitPos w j,
    Fin.cases (bufferTape s) (fun _ => f2_catalogPolyTape j), fun _ => j, []⟩

/-- Preparation copies a unary side length without reading or changing any
candidate bit value. The same induction covers a candidate past native EOF. -/
private lemma f2_splitPrepare_scan (k : ℕ) (w s : List Bool) : ∀ j, j ≤ s.length →
    (f2_splitPrepareTM k).tm.runFrom (f2_splitPrepareScan k w s 0) j =
      f2_splitPrepareScan k w s j := by
  intro j
  induction j with
  | zero => intro hj; rfl
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hw : (f2_splitPrepareScan k w s j).workTapeSymbols 0 = some (s[j]'(by omega)) := by
      simp [f2_splitPrepareScan, Cfg.workTapeSymbols,
        List.getElem?_eq_getElem (by omega : j < s.length)]
    unfold MultiTapeTM.step
    change ((f2_splitPrepareTM k).tm.tr (0, decide (w.length < j)) _ _).apply _ = _
    simp only [f2_splitPrepareTM, hw]
    refine Cfg.ext ?_ (f2_splitPos_succ w j) ?_ ?_ rfl
    · exact congrArg (fun over => some (0, over))
        (f2_splitCount_over w (f2_splitPrepareScan k w s j) j rfl)
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · exact f2_catalogPolyTape_write j
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i <;> simp [Action.apply, f2_splitPrepareScan]

/-- Prepared scratch tapes have side length `|s|+1`, with synchronized heads;
the overflow flag records the candidate's length alone. -/
private def f2_splitPrepareReady (k : ℕ) (w s : List Bool)
    (q : Fin 3) (h : ℤ) : Cfg (k + 1) Bool (f2_splitPrepareTM k).State w :=
  ⟨some (q, decide (w.length < s.length)), f2_splitPos w s.length,
    Fin.cases (bufferTape s) (fun _ => f2_catalogPolyTape (s.length + 1)), fun _ => h, []⟩

/-- Adding the extra side-length cell handles the empty candidate uniformly. -/
private lemma f2_splitPrepare_extra (k : ℕ) (w s : List Bool) :
    (f2_splitPrepareTM k).tm.step (f2_splitPrepareScan k w s s.length) =
      f2_splitPrepareReady k w s 1 (s.length - 1) := by
  have hw : (f2_splitPrepareScan k w s s.length).workTapeSymbols 0 = none := by
    simp [f2_splitPrepareScan, Cfg.workTapeSymbols]
  unfold MultiTapeTM.step
  change ((f2_splitPrepareTM k).tm.tr (0, decide (w.length < s.length)) _ _).apply _ = _
  simp only [f2_splitPrepareTM, hw]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
  · funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · exact f2_catalogPolyTape_write s.length
  · funext i
    refine Fin.cases ?_ (fun i => ?_) i <;>
      simp [Action.apply, f2_splitPrepareScan, f2_splitPrepareReady, sub_eq_add_neg]

/-- Rewind the synchronized bank along the preserved candidate; each scratch
tape retains its extra cell even though the rewind uses the candidate length. -/
private lemma f2_splitPrepare_rewind (k : ℕ) (w s : List Bool) : ∀ j, j ≤ s.length →
    (f2_splitPrepareTM k).tm.runFrom (f2_splitPrepareReady k w s 1 ((j : ℤ) - 1)) (j + 1) =
      f2_splitPrepareReady k w s 2 0 := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    simp only [MultiTapeTM.step, f2_splitPrepareReady, f2_splitPrepareTM, Cfg.workTapeSymbols,
      Fin.cases_zero, Nat.cast_zero, zero_sub, bufferTape_left]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext i; simp [Action.apply]
  | succ j ih =>
    intro hj
    have hs : (f2_splitPrepareTM k).tm.step (f2_splitPrepareReady k w s 1 (((j + 1 : ℕ) : ℤ) - 1)) =
        f2_splitPrepareReady k w s 1 ((j : ℤ) - 1) := by
      have he : (((j + 1 : ℕ) : ℤ) - 1) = j := by omega
      rw [he]
      simp only [MultiTapeTM.step, f2_splitPrepareReady, f2_splitPrepareTM, Cfg.workTapeSymbols,
        Fin.cases_zero, bufferTape_nat, List.getElem?_eq_getElem (by omega : j < s.length)]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext i; simp [Action.apply, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- From the audited state-word seam, preparation takes exactly `2(|s|+1)`
silent steps and initializes every loop head at zero. -/
private lemma f2_splitPrepare_run (k : ℕ) (w s : List Bool) :
    (f2_splitPrepareTM k).tm.runFrom
      (Cfg.ofWords (input := w) (0, false) (stateWord (k + 1) s)) (2 * (s.length + 1)) =
      f2_splitPrepareReady k w s 2 0 := by
  have hinit : Cfg.ofWords (input := w) (0, false) (stateWord (k + 1) s) =
      f2_splitPrepareScan k w s 0 := by
    refine Cfg.ext (by simp [f2_splitPrepareScan, Cfg.ofWords]) ?_ ?_ rfl rfl
    · simp [f2_splitPrepareScan, Cfg.ofWords, f2_splitPos]
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i <;>
        simp [f2_splitPrepareScan, Cfg.ofWords, stateWord]
      funext z
      simp [f2_catalogPolyTape]
  have hfirst : (f2_splitPrepareTM k).tm.runFrom (f2_splitPrepareScan k w s 0) (s.length + 1) =
      f2_splitPrepareReady k w s 1 (s.length - 1) := by
    rw [MultiTapeTM.runFrom_succ_eq_step', f2_splitPrepare_scan k w s _ (le_refl _), f2_splitPrepare_extra]
  rw [hinit, show 2 * (s.length + 1) = (s.length + 1) + (s.length + 1) by omega,
    MultiTapeTM.runFrom_add, hfirst, f2_splitPrepare_rewind k w s s.length (le_refl _)]

/-- Preparation can be exposed at its first return-state entry, with no
premature visit and without changing its exact initialized-bank endpoint. -/
private lemma f2_splitPrepare_first (k : ℕ) (w s : List Bool) :
    ∃ t ≤ 2 * (s.length + 1),
      (∀ j < t, ((f2_splitPrepareTM k).tm.runFrom
        (Cfg.ofWords (input := w) (0, false) (stateWord (k + 1) s)) j).state ≠
          some (2, decide (w.length < s.length))) ∧
      (f2_splitPrepareTM k).tm.runFrom
        (Cfg.ofWords (input := w) (0, false) (stateWord (k + 1) s)) t =
          f2_splitPrepareReady k w s 2 0 := by
  apply f2_catalogFirstEntry (f2_splitPrepareTM k).tm (2, decide (w.length < s.length))
  · intro z hz
    unfold MultiTapeTM.step
    rw [hz]
    change (controlAction 0 (some (2, decide (w.length < s.length)))).apply z = z
    rw [controlAction_apply, moveInputPos_zero]
    cases z
    simp_all
  · rfl
  · exact f2_splitPrepare_run k w s

/-- A phase trace excludes the round anchor even at its two endpoints. -/
private def f2_splitSafe {k : ℕ} {S : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (anchor : S) (c : Cfg k Bool S w) (t : ℕ) : Prop :=
  ∀ j ≤ t, (tm.runFrom c j).state ≠ some anchor

/-- Safe traces concatenate at their literal configuration seam. -/
private lemma f2_splitSafe_add {k : ℕ} {S : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (anchor : S) (c : Cfg k Bool S w) (u v : ℕ)
    (hu : f2_splitSafe tm anchor c u) (hv : f2_splitSafe tm anchor (tm.runFrom c u) v) :
    f2_splitSafe tm anchor c (u + v) := by
  intro j hj
  by_cases h : j ≤ u
  · exact hu j h
  · have he : j = u + (j - u) := by omega
    rw [he, MultiTapeTM.runFrom_add]
    exact hv (j - u) (by omega)

/-- Cut an absorbing source phase at its first terminal control state and
embed the entire prefix into a disjoint host phase.
**Proof sketch.** Take the least terminal visit. Absorption identifies its
configuration with the known endpoint. Induct on the prefix length using
transition agreement only before that visit; every mapped control state,
including a halted state, is different from the host anchor. -/
private lemma f2_splitEmbed_cut {k : ℕ} {S H : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (host : MultiTapeTM k Bool H)
    (emb : S → H) (anchor : H) (stop : S → Prop) [DecidablePred stop]
    (haway : ∀ q, emb q ≠ anchor)
    (hfix : ∀ c : Cfg k Bool S w, (∃ q, c.state = some q ∧ stop q) → tm.step c = c)
    (hagree : ∀ q, ¬stop q → ∀ inp work,
      host.tr (emb q) inp work = (tm.tr q inp work).mapState emb)
    (c d : Cfg k Bool S w) (T : ℕ)
    (hd : ∃ q, d.state = some q ∧ stop q) (hT : tm.runFrom c T = d) :
    ∃ t ≤ T, host.runFrom (c.mapState emb) t = d.mapState emb ∧
      f2_splitSafe host anchor (c.mapState emb) t := by
  classical
  have hex : ∃ t, ∃ q, (tm.runFrom c t).state = some q ∧ stop q :=
    ⟨T, by rw [hT]; exact hd⟩
  let t := Nat.find hex
  have ht : t ≤ T := Nat.find_min' hex (by rw [hT]; exact hd)
  have he : tm.runFrom c t = d := by
    have hh := tm.runFrom_add c t (T - t)
    have hconst : tm.runFrom (tm.runFrom c t) (T - t) = tm.runFrom c t :=
      Function.iterate_fixed (hfix _ (Nat.find_spec hex)) _
    rw [Nat.add_sub_of_le ht, hT, hconst] at hh
    exact hh.symm
  have hp : ∀ j ≤ t, host.runFrom (c.mapState emb) j = (tm.runFrom c j).mapState emb := by
    intro j
    induction j with
    | zero => intro hj; rfl
    | succ j ih =>
      intro hj
      rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega),
        MultiTapeTM.runFrom_succ_eq_step']
      let z := tm.runFrom c j
      change host.step (z.mapState emb) = (tm.step z).mapState emb
      cases hz : z.state with
      | none => simp [MultiTapeTM.step, Cfg.mapState, hz]
      | some q =>
        have hn : ¬stop q := fun hq => Nat.find_min hex (by omega) ⟨q, hz, hq⟩
        simp only [MultiTapeTM.step, Cfg.mapState, hz, Option.map_some]
        rw [hagree q hn]
        rfl
  refine ⟨t, ht, by rw [hp t (le_refl _), he], ?_⟩
  intro j hj
  rw [hp j hj]
  cases hs : (tm.runFrom c j).state with
  | none => simp [Cfg.mapState, hs]
  | some q => simpa [Cfg.mapState, hs] using haway q

/-- A standalone native-input rewind, with an absorbing return at state two. -/
private def f2_splitRewindTM (k : ℕ) : FinTM Bool where
  k := k + 1
  State := Fin 3
  tm := {
    q₀ := 0
    tr := fun q inp _ => match q.val with
      | 0 => controlAction .neg (some 1)
      | 1 => match inp with
        | some _ => controlAction .neg (some 1)
        | none => controlAction .pos (some 2)
      | _ => controlAction 0 (some 2) }

/-- Emit a native-input split, using tape zero only as a length counter.
The first two states double native bits, state two completes the separator,
and state three copies the native suffix. No candidate bit is emitted. -/
private def f2_splitEmitTM (k : ℕ) : FinTM Bool where
  k := k + 1
  State := Fin 4
  tm := {
    q₀ := 0
    tr := fun q inp work => match q.val with
      | 0 => match work 0 with
        | none => ⟨0, fun _ => (none, 0), some false, some 2⟩
        | some _ => ⟨0, fun _ => (none, 0), inp, some 1⟩
      | 1 => ⟨.pos, Fin.cases (none, .pos) (fun _ => (none, 0)), inp, some 0⟩
      | 2 => ⟨0, fun _ => (none, 0), some true, some 3⟩
      | _ => match inp with
        | some b => ⟨.pos, fun _ => (none, 0), some b, some 3⟩
        | none => controlAction 0 none }

/-- Each subroutine has its own finite control phase; only cleanup can
return to the anchor. The acceptance bit survives the native-input rewind. -/
private inductive f2_SplitBodyState (S : Type) where
  | anchor
  | prepare (q : Fin 3 × Bool)
  | count (q : S) (over : Bool)
  | check (over : Bool)
  | rewind (accept : Bool) (q : Fin 3)
  | restore (q : Fin 5 × Bool)
  | emit (q : Fin 4)

private instance f2_splitBodyStateFintype (S : Type) [Fintype S] :
    Fintype (f2_SplitBodyState S) := derive_fintype% _

/-- Equality of controller states compares only matching phases and their
finite payloads. Keep the instance private, including its generated helpers. -/
private instance f2_splitBodyStateDecidableEq (S : Type) [DecidableEq S] :
    DecidableEq (f2_SplitBodyState S) := by
  intro a b
  cases a <;> cases b
  all_goals try (solve | apply isFalse; intro h; cases h)
  · exact isTrue rfl
  · exact decidable_of_iff _ (Iff.symm (iff_of_eq (f2_SplitBodyState.prepare.injEq _ _)))
  · exact decidable_of_iff _ (Iff.symm (iff_of_eq (f2_SplitBodyState.count.injEq _ _ _ _)))
  · exact decidable_of_iff _ (Iff.symm (iff_of_eq (f2_SplitBodyState.check.injEq _ _)))
  · exact decidable_of_iff _ (Iff.symm (iff_of_eq (f2_SplitBodyState.rewind.injEq _ _ _ _)))
  · exact decidable_of_iff _ (Iff.symm (iff_of_eq (f2_SplitBodyState.restore.injEq _ _)))
  · exact decidable_of_iff _ (Iff.symm (iff_of_eq (f2_SplitBodyState.emit.injEq _ _)))

/-- Combined round controller. The polynomial source starts on the prepared
bank, and its emissions are counted against native input without physical
output. Every seam transition is explicit, including the final anchor return. -/
private def f2_splitBodyTM (M : FinTM Bool) (start : M.State) : FinTM Bool where
  k := M.k + 1
  State := f2_SplitBodyState M.State
  tm := {
    q₀ := .anchor
    tr := fun q inp work => match q with
      | .anchor => controlAction 0 (some (.prepare (0, false)))
      | .prepare p =>
        if p.1 = 2 then controlAction 0 (some (.count start p.2))
        else ((f2_splitPrepareTM M.k).tm.tr p inp work).mapState .prepare
      | .count q over => f2_splitCountAction .count .check over inp
          (M.tm.tr q none (fun i => work i.succ))
      | .check over => controlAction 0 (some (.rewind (!over && inp.isNone) 0))
      | .rewind ok p =>
        if p = 2 then controlAction 0 (some (if ok then .emit 0 else .restore (0, false)))
        else ((f2_splitRewindTM M.k).tm.tr p inp work).mapState (.rewind ok)
      | .restore p =>
        if p = (4, false) then controlAction 0 (some .anchor)
        else ((f2_splitRestoreTM M.k).tm.tr p inp work).mapState .restore
      | .emit p => ((f2_splitEmitTM M.k).tm.tr p inp work).mapState .emit }

/-- The source bank has the candidate's successor length on each tape and
all heads at zero; its virtual input is empty. -/
private def f2_splitBank (M : FinTM Bool) (s : List Bool)
    (q : Option M.State) (out : List Bool) : Cfg M.k Bool M.State [] :=
  ⟨q, 1, fun _ => f2_catalogPolyTape (s.length + 1), fun _ => 0, out⟩

/-- The genuine initial configuration is the empty-candidate anchor seam;
there is no unproved startup work hidden in a zero-time witness. -/
private lemma f2_splitBody_start (M : FinTM Bool) (start : M.State) (w : List Bool) :
    (f2_splitBodyTM M start).tm.initCfg w =
      Cfg.ofWords .anchor (stateWord (M.k + 1) []) := by
  rw [initCfg_ofWords]
  congr 1
  funext i
  simp [stateWord]

/-- A complete source embedding commutes with every step, including halt. -/
private lemma f2_splitEmbed_run {k : ℕ} {S H : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (host : MultiTapeTM k Bool H) (emb : S → H)
    (hagree : ∀ q inp work, host.tr (emb q) inp work = (tm.tr q inp work).mapState emb)
    (c : Cfg k Bool S w) (t : ℕ) :
    host.runFrom (c.mapState emb) t = (tm.runFrom c t).mapState emb := by
  apply MultiTapeTM.runFrom_comm_of_step
  intro z
  cases hs : z.state with
  | none => simp [MultiTapeTM.step, Cfg.mapState, hs]
  | some q =>
    simp only [MultiTapeTM.step, Cfg.mapState, hs, Option.map_some]
    rw [hagree]
    rfl

/-- Preparation reaches its first return with the exact counted-source bank.
Every configuration of the embedded preparation is outside the anchor phase.
**Proof sketch.** Cut the absorbing source at its first return, map its full
configuration into the preparation phase, then take the explicit dispatch.
Check the source-bank seam field by field, including the native head and flag. -/
private lemma f2_splitBody_prepare (M : FinTM Bool) (start : M.State) (w s : List Bool) :
    ∃ t ≤ 2 * (s.length + 1),
      (f2_splitBodyTM M start).tm.runFrom
        (Cfg.ofWords (.prepare (0, false)) (stateWord (M.k + 1) s)) (t + 1) =
          f2_splitCountCfg f2_SplitBodyState.count f2_SplitBodyState.check w s
            (f2_splitBank M s (some start) []) ∧
      f2_splitSafe (f2_splitBodyTM M start).tm .anchor
        (Cfg.ofWords (input := w) (.prepare (0, false)) (stateWord (M.k + 1) s)) (t + 1) := by
  obtain ⟨t, ht, he, hsafe⟩ := f2_splitEmbed_cut (f2_splitPrepareTM M.k).tm
    (f2_splitBodyTM M start).tm f2_SplitBodyState.prepare .anchor (fun q => q.1 = 2)
    (by intro q; simp)
    (by
      rintro z ⟨⟨q, over⟩, hz, hq⟩
      change q = 2 at hq
      subst q
      simp only [MultiTapeTM.step, hz]
      change (controlAction 0 (some (2, over))).apply z = z
      rw [controlAction_apply, moveInputPos_zero]
      cases z; simp_all)
    (by intro q hq inp work; simp [f2_splitBodyTM, hq])
    (Cfg.ofWords (input := w) (0, false) (stateWord (M.k + 1) s))
    (f2_splitPrepareReady M.k w s 2 0) (2 * (s.length + 1))
    ⟨_, rfl, rfl⟩ (f2_splitPrepare_run M.k w s)
  have hstep : (f2_splitBodyTM M start).tm.step
      ((f2_splitPrepareReady M.k w s 2 0).mapState f2_SplitBodyState.prepare) =
      f2_splitCountCfg f2_SplitBodyState.count f2_SplitBodyState.check w s
        (f2_splitBank M s (some start) []) := by
    simp only [MultiTapeTM.step, Cfg.mapState, f2_splitPrepareReady, Option.map_some,
      f2_splitBodyTM, ↓reduceIte]
    refine Cfg.ext ?_ ?_ rfl ?_ rfl
    · simp [Action.apply, controlAction, f2_splitCountCfg, f2_splitBank]
    · simp [Action.apply, controlAction, f2_splitCountCfg, f2_splitBank]
    · funext i
      refine Fin.cases ?_ (fun j => ?_) i <;>
        simp [Action.apply, controlAction, f2_splitCountCfg, f2_splitBank]
  have hinit : (Cfg.ofWords (input := w) (0, false) (stateWord (M.k + 1) s)).mapState
      (f2_SplitBodyState.prepare (S := M.State)) = Cfg.ofWords (.prepare (0, false)) (stateWord (M.k + 1) s) := rfl
  rw [hinit] at he hsafe
  have hend : (f2_splitBodyTM M start).tm.runFrom
      (Cfg.ofWords (.prepare (0, false)) (stateWord (M.k + 1) s)) (t + 1) =
      f2_splitCountCfg f2_SplitBodyState.count f2_SplitBodyState.check w s
        (f2_splitBank M s (some start) []) := by
    rw [MultiTapeTM.runFrom_succ_eq_step', he, hstep]
  refine ⟨t, ht, hend, ?_⟩
  intro j hj
  by_cases hjt : j ≤ t
  · exact hsafe j hjt
  · have hj' : j = t + 1 := by omega
    rw [hj', hend]
    simp [f2_splitCountCfg, f2_splitBank]

/-- Counted evaluation reaches its first source halt; every prefix remains
in a count or check state and therefore cannot revisit the round anchor.
**Proof sketch.** Choose the least source halt and remove its constant halted
suffix. Apply the counted correspondence to every prefix through that halt;
its control image is disjoint from the anchor, including the return state. -/
private lemma f2_splitBody_count (M : FinTM Bool) (start : M.State) (w s : List Bool)
    (out : List Bool) (T : ℕ)
    (hT : M.tm.runFrom (f2_splitBank M s (some start) []) T = f2_splitBank M s none out) :
    ∃ t ≤ T, (f2_splitBodyTM M start).tm.runFrom
      (f2_splitCountCfg f2_SplitBodyState.count f2_SplitBodyState.check w s (f2_splitBank M s (some start) [])) t =
      f2_splitCountCfg f2_SplitBodyState.count f2_SplitBodyState.check w s (f2_splitBank M s none out) ∧
      f2_splitSafe (f2_splitBodyTM M start).tm .anchor
        (f2_splitCountCfg f2_SplitBodyState.count f2_SplitBodyState.check w s (f2_splitBank M s (some start) [])) t := by
  classical
  let c := f2_splitBank M s (some start) []
  let d := f2_splitBank M s none out
  have hh : ∃ t, (M.tm.runFrom c t).state = none := ⟨T, by rw [hT]; rfl⟩
  let t := Nat.find hh
  have ht : t ≤ T := Nat.find_min' hh (by rw [hT]; rfl)
  have he : M.tm.runFrom c t = d := by
    have h := M.tm.runFrom_add c t (T - t)
    rw [Nat.add_sub_of_le ht, hT, M.tm.runFrom_of_halt _ (Nat.find_spec hh)] at h
    exact h.symm
  have hp (j : ℕ) (hj : j ≤ t) := f2_splitCount_run M.tm (f2_splitBodyTM M start).tm
    f2_SplitBodyState.count f2_SplitBodyState.check (fun _ _ _ _ => rfl) w s c j
    (fun l hl => Nat.find_min hh (by omega))
  refine ⟨t, ht, ?_, ?_⟩
  · rw [hp t (le_refl _), he]
  · intro j hj
    rw [hp j hj]
    cases hq : (M.tm.runFrom c j).state <;> simp [f2_splitCountCfg, hq]

/-- Rewind preserves the exact source bank and physical output. Its terminal
state is cut before dispatch to the accepting emitter or rejecting cleanup.
**Proof sketch.** Use the quantitative native rewind, then cut its absorbing
return and embed that prefix while retaining the acceptance bit in control. -/
private lemma f2_splitBody_rewind (M : FinTM Bool) (start : M.State) (w : List Bool)
    (ok : Bool) (c : Cfg (M.k + 1) Bool (Fin 3) w)
    (hc : c.state = some 0) :
    ∃ t ≤ c.inputPos.val + 2,
      (f2_splitBodyTM M start).tm.runFrom (c.mapState (f2_SplitBodyState.rewind ok)) t =
        ({c with state := some (2 : Fin 3), inputPos := 1}).mapState (f2_SplitBodyState.rewind ok) ∧
      f2_splitSafe (f2_splitBodyTM M start).tm .anchor (c.mapState (f2_SplitBodyState.rewind ok)) t := by
  obtain ⟨T, hT, he⟩ := f2_catalogRewind (f2_splitRewindTM M.k).tm (0 : Fin 3) (1 : Fin 3) (some (2 : Fin 3))
    (fun _ _ => rfl) (fun _ _ => rfl) c hc
  obtain ⟨t, ht, hend, hsafe⟩ := f2_splitEmbed_cut (f2_splitRewindTM M.k).tm
    (f2_splitBodyTM M start).tm (f2_SplitBodyState.rewind ok) .anchor (fun q => q = (2 : Fin 3))
    (by intro q; simp)
    (by
      rintro z ⟨q, hz, rfl⟩
      simp only [MultiTapeTM.step, hz]
      change (controlAction 0 (some (2 : Fin 3))).apply z = z
      rw [controlAction_apply, moveInputPos_zero]
      cases z; simp_all)
    (by intro q hq inp work; simp [f2_splitBodyTM, hq])
    c {c with state := some (2 : Fin 3), inputPos := 1} T ⟨(2 : Fin 3), rfl, rfl⟩ he
  exact ⟨t, ht.trans hT, hend, hsafe⟩

/-- Rejection cleanup is embedded up to its absorbing return, so its exact
restoration and the no-anchor property hold simultaneously in the body.
**Proof sketch.** Apply the exact restoration run and cut at its absorbing
false-flag return. Its host control remains in the restore phase; the final
transition to the anchor is accounted for separately by the round proof. -/
private lemma f2_splitBody_restore (M : FinTM Bool) (start : M.State) (w s : List Bool) :
    ∃ t ≤ 2 * s.length + w.length + 5,
      (f2_splitBodyTM M start).tm.runFrom
        ((f2_splitRestoreScan M.k w s 0).mapState f2_SplitBodyState.restore) t =
        Cfg.ofWords (.restore (4, false)) (stateWord (M.k + 1) (f2_splitStep w s)) ∧
      f2_splitSafe (f2_splitBodyTM M start).tm .anchor
        ((f2_splitRestoreScan M.k w s 0).mapState f2_SplitBodyState.restore) t := by
  obtain ⟨T, hT, he⟩ := f2_splitRestore_run M.k w s
  obtain ⟨t, ht, hend, hsafe⟩ := f2_splitEmbed_cut (f2_splitRestoreTM M.k).tm
    (f2_splitBodyTM M start).tm f2_SplitBodyState.restore .anchor (fun q => q = (4, false))
    (by intro q; simp)
    (by
      rintro z ⟨q, hz, rfl⟩
      simp only [MultiTapeTM.step, hz]
      change (controlAction 0 (some (4, false))).apply z = z
      rw [controlAction_apply, moveInputPos_zero]
      cases z; simp_all)
    (by intro q hq inp work; simp [f2_splitBodyTM, hq])
    (f2_splitRestoreScan M.k w s 0)
    (Cfg.ofWords (4, false) (stateWord (M.k + 1) (f2_splitStep w s))) T
    ⟨_, rfl, rfl⟩ he
  exact ⟨t, ht.trans hT, hend, hsafe⟩

/-- Emitter configurations preserve the initialized scratch bank and use the
candidate head only to count the doubled native prefix. -/
private def f2_splitEmitCfg (k : ℕ) (w s : List Bool) (q : Option (Fin 4))
    (j h : ℕ) (out : List Bool) : Cfg (k + 1) Bool (Fin 4) w :=
  ⟨q, f2_splitPos w j, Fin.cases (bufferTape s) (fun _ => f2_catalogPolyTape (s.length + 1)),
    Fin.cases (h : ℤ) (fun _ => 0), out⟩

/-- Two transitions emit two copies of the current native bit and advance
both the native head and the candidate counter. Arbitrary candidate bit
values are read only for their presence.
**Proof sketch.** Induct on the number of doubled cells. The two transitions
read the same native bit, emit it twice, and only then advance both heads. -/
private lemma f2_splitEmit_double (k : ℕ) (w s : List Bool) (hs : s.length ≤ w.length) :
    ∀ j, j ≤ s.length → (f2_splitEmitTM k).tm.runFrom
      (f2_splitEmitCfg k w s (some 0) 0 0 []) (2 * j) =
      f2_splitEmitCfg k w s (some 0) j j ((w.take j).flatMap fun b => [b, b]) := by
  intro j
  induction j with
  | zero => intro hj; rfl
  | succ j ih =>
    intro hj
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by omega,
      MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hread (q : Fin 4) (out : List Bool) :
        (f2_splitEmitCfg k w s (some q) j j out).inputSymbol = some (w[j]'(by omega)) := by
      rw [f2_splitPos_read w _ j rfl, dif_pos (by omega)]
    have hwork : (f2_splitEmitCfg k w s (some 0) j j
        ((w.take j).flatMap fun b => [b, b])).workTapeSymbols 0 = some (s[j]'(by omega)) := by
      simp [f2_splitEmitCfg, Cfg.workTapeSymbols, List.getElem?_eq_getElem (by omega : j < s.length)]
    have hfirst : (f2_splitEmitTM k).tm.step
        (f2_splitEmitCfg k w s (some 0) j j ((w.take j).flatMap fun b => [b, b])) =
        f2_splitEmitCfg k w s (some 1) j j
          (((w.take j).flatMap fun b => [b, b]) ++ [w[j]'(by omega)]) := by
      unfold MultiTapeTM.step
      change ((f2_splitEmitTM k).tm.tr (0 : Fin 4) _ _).apply _ = _
      simp only [f2_splitEmitTM, hwork, hread]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext i; simp [Action.apply, f2_splitEmitCfg]
    rw [hfirst]
    unfold MultiTapeTM.step
    change ((f2_splitEmitTM k).tm.tr (1 : Fin 4) _ _).apply _ = _
    simp only [f2_splitEmitTM, hread]
    refine Cfg.ext rfl (f2_splitPos_succ w j) ?_ ?_ ?_
    · funext i
      refine Fin.cases ?_ (fun l => ?_) i <;> rfl
    · funext i
      refine Fin.cases ?_ (fun l => ?_) i <;> simp [Action.apply, f2_splitEmitCfg]
    · change (((w.take j).flatMap fun b => [b, b]) ++ [w[j]'(by omega)]) ++
          [w[j]'(by omega)] = (w.take (j + 1)).flatMap fun b => [b, b]
      simp only [List.take_succ, List.getElem?_eq_getElem (by omega : j < w.length),
        Option.toList_some, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.append_assoc, List.cons_append, List.nil_append]

/-- Once the counter is exhausted, emit the two separator bits without
moving the native head away from the beginning of the suffix. -/
private lemma f2_splitEmit_separator (k : ℕ) (w s : List Bool) (out : List Bool) :
    (f2_splitEmitTM k).tm.runFrom (f2_splitEmitCfg k w s (some 0) s.length s.length out) 2 =
      f2_splitEmitCfg k w s (some 3) s.length s.length (out ++ [false, true]) := by
  have hwork : (f2_splitEmitCfg k w s (some 0) s.length s.length out).workTapeSymbols 0 = none := by
    simp [f2_splitEmitCfg, Cfg.workTapeSymbols]
  have hf : (f2_splitEmitTM k).tm.step (f2_splitEmitCfg k w s (some 0) s.length s.length out) =
      f2_splitEmitCfg k w s (some 2) s.length s.length (out ++ [false]) := by
    unfold MultiTapeTM.step
    change ((f2_splitEmitTM k).tm.tr (0 : Fin 4) _ _).apply _ = _
    simp only [f2_splitEmitTM, hwork]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext i; simp [Action.apply, f2_splitEmitCfg]
  rw [show 2 = 1 + 1 by omega, MultiTapeTM.runFrom_succ_eq_step,
    show (f2_splitEmitTM k).tm.step _ = _ from hf, MultiTapeTM.runFrom_succ_eq_step,
    MultiTapeTM.runFrom_zero]
  refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ ?_
  · funext i; simp [MultiTapeTM.step, f2_splitEmitTM, Action.apply, f2_splitEmitCfg]
  · simp [MultiTapeTM.step, f2_splitEmitTM, Action.apply, f2_splitEmitCfg, List.append_assoc]

/-- The suffix-copy phase preserves all work tapes and copies native bits
verbatim, including the empty suffix and its final blank-reading halt.
**Proof sketch.** Induct on the remaining suffix while allowing arbitrary
already-copied prefix and output. The nonempty case copies one native bit;
the empty case reads the right blank and halts without an extra emission. -/
private lemma f2_splitEmit_suffix (k : ℕ) (w s rest : List Bool) :
    ∀ pre out h, w = pre ++ rest → (f2_splitEmitTM k).tm.runFrom
      (f2_splitEmitCfg k w s (some 3) pre.length h out) (rest.length + 1) =
      f2_splitEmitCfg k w s none w.length h (out ++ rest) := by
  induction rest with
  | nil =>
    intro pre out h hw
    have he : w = pre := by simpa using hw
    clear hw
    subst w
    simp only [List.append_nil, List.length_nil, MultiTapeTM.runFrom_succ_eq_step,
      MultiTapeTM.runFrom_zero]
    have hr := f2_splitPos_read pre (f2_splitEmitCfg k pre s (some 3) pre.length h out) pre.length rfl
    simp only [Nat.lt_irrefl, ↓reduceDIte] at hr
    unfold MultiTapeTM.step
    change ((f2_splitEmitTM k).tm.tr (3 : Fin 4) _ _).apply _ = _
    rw [hr]
    simp [f2_splitEmitTM, controlAction, f2_splitEmitCfg]
  | cons b rest ih =>
    intro pre out h hw
    have hread : (f2_splitEmitCfg k w s (some 3) pre.length h out).inputSymbol = some b := by
      rw [f2_splitPos_read w _ pre.length rfl]
      simp [hw]
    have hstep : (f2_splitEmitTM k).tm.step (f2_splitEmitCfg k w s (some 3) pre.length h out) =
        f2_splitEmitCfg k w s (some 3) (pre ++ [b]).length h (out ++ [b]) := by
      unfold MultiTapeTM.step
      change ((f2_splitEmitTM k).tm.tr (3 : Fin 4) _ _).apply _ = _
      rw [hread]
      refine Cfg.ext rfl ?_ rfl ?_ rfl
      · simpa only [List.length_append, List.length_singleton] using f2_splitPos_succ w pre.length
      · funext i; simp [f2_splitEmitTM, Action.apply, f2_splitEmitCfg]
    simp only [List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step, hstep]
    simpa only [List.append_assoc, List.singleton_append] using
      ih (pre ++ [b]) (out ++ [b]) h (by simpa [List.append_assoc] using hw)

/-- The accepting emitter produces exactly the encoded native split in
`|s|+|w|+3` steps. Its candidate may contain any bit pattern.
**Proof sketch.** Double exactly the native prefix counted by the candidate,
emit the separator, and copy the remaining native suffix. Concatenate the
three exact runs and cancel the prefix length in the time expression. -/
private lemma f2_splitEmit_run (k : ℕ) (w s : List Bool) (hs : s.length ≤ w.length) :
    (f2_splitEmitTM k).tm.runFrom (f2_splitEmitCfg k w s (some 0) 0 0 [])
      (s.length + w.length + 3) =
      f2_splitEmitCfg k w s none w.length s.length
        (pairEncode (w.take s.length) (w.drop s.length)) := by
  have ht : s.length + w.length + 3 =
      2 * s.length + 2 + ((w.drop s.length).length + 1) := by
    simp only [List.length_drop]; omega
  rw [ht, MultiTapeTM.runFrom_add,
    MultiTapeTM.runFrom_add _ (2 * s.length) 2,
    f2_splitEmit_double k w s hs _ (le_refl _), f2_splitEmit_separator]
  have h := f2_splitEmit_suffix k w s (w.drop s.length) (w.take s.length)
    (((w.take s.length).flatMap fun b => [b, b]) ++ [false, true]) s.length
    (List.take_append_drop s.length w).symm
  simpa [List.length_take, Nat.min_eq_left hs, pairEncode] using h

/-- A single transition is safe when both its endpoints exclude the anchor. -/
private lemma f2_splitSafe_one {k : ℕ} {S : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (anchor : S) (c d : Cfg k Bool S w)
    (he : tm.step c = d) (hc : c.state ≠ some anchor) (hd : d.state ≠ some anchor) :
    tm.runFrom c 1 = d ∧ f2_splitSafe tm anchor c 1 := by
  refine ⟨he, ?_⟩
  intro j hj
  rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
  · exact hc
  · change (tm.step c).state ≠ _
    rw [he]; exact hd

/-- Concatenate two safe exact phase runs. -/
private lemma f2_splitSafe_join {k : ℕ} {S : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (anchor : S) (c d f : Cfg k Bool S w) (u v : ℕ)
    (h1 : tm.runFrom c u = d) (hs1 : f2_splitSafe tm anchor c u)
    (h2 : tm.runFrom d v = f) (hs2 : f2_splitSafe tm anchor d v) :
    tm.runFrom c (u + v) = f ∧ f2_splitSafe tm anchor c (u + v) := by
  refine ⟨by rw [MultiTapeTM.runFrom_add, h1, h2], ?_⟩
  apply f2_splitSafe_add tm anchor c u v hs1
  rw [h1]; exact hs2

/-- A completed source gives a complete body round, including acceptance,
rejection, positive duration, and anchor exclusion over every strict interior
step. The bound explicitly includes all dispatches, rewinds, and emission.
**Proof sketch.** Depart the anchor in one step. Concatenate safe preparation,
counting, decision, and rewind traces. Equality accepts and emits native
slices. Inequality dispatches to the exact scratch restoration, followed by
one explicit return to the anchor. All intermediate states belong to disjoint
phases; the only anchor step is the final rejecting transition. -/
private lemma f2_splitBody_round (M : FinTM Bool) (start : M.State) (w s out : List Bool)
    (T : ℕ) (hT : M.tm.runFrom (f2_splitBank M s (some start) []) T = f2_splitBank M s none out) :
    ∃ t, 0 < t ∧ t ≤ T + 5 * s.length + 3 * w.length + 20 ∧
      (∀ j, 0 < j → j < t →
        ((f2_splitBodyTM M start).tm.runFrom
          (Cfg.ofWords (input := w) .anchor (stateWord (M.k + 1) s)) j).state ≠ some .anchor) ∧
      if decide (s.length + out.length = w.length) then
        ((f2_splitBodyTM M start).tm.runFrom
          (Cfg.ofWords (input := w) .anchor (stateWord (M.k + 1) s)) t).state = none ∧
        ((f2_splitBodyTM M start).tm.runFrom
          (Cfg.ofWords (input := w) .anchor (stateWord (M.k + 1) s)) t).output =
            pairEncode (w.take s.length) (w.drop s.length)
      else (f2_splitBodyTM M start).tm.runFrom
        (Cfg.ofWords (input := w) .anchor (stateWord (M.k + 1) s)) t =
          Cfg.ofWords .anchor (stateWord (M.k + 1) (f2_splitStep w s)) := by
  let tm := (f2_splitBodyTM M start).tm
  let z : Cfg (M.k + 1) Bool (f2_SplitBodyState M.State) w :=
    Cfg.ofWords .anchor (stateWord (M.k + 1) s)
  let p : Cfg (M.k + 1) Bool (f2_SplitBodyState M.State) w :=
    Cfg.ofWords (.prepare (0, false)) (stateWord (M.k + 1) s)
  let d := f2_splitCountCfg f2_SplitBodyState.count f2_SplitBodyState.check w s (f2_splitBank M s none out)
  let ok := decide (s.length + out.length = w.length)
  let c : Cfg (M.k + 1) Bool (Fin 3) w :=
    ⟨some 0, f2_splitPos w (s.length + out.length),
      Fin.cases (bufferTape s) (fun _ => f2_catalogPolyTape (s.length + 1)),
      Fin.cases 0 (fun _ => 0), []⟩
  let r : Cfg (M.k + 1) Bool (f2_SplitBodyState M.State) w :=
    ({c with state := some (2 : Fin 3), inputPos := 1} : Cfg (M.k + 1) Bool (Fin 3) w).mapState
    (f2_SplitBodyState.rewind (S := M.State) ok)
  have hdepart : tm.runFrom z 1 = p := by
    change (controlAction 0 (some (.prepare (0, false)))).apply z = p
    rw [controlAction_apply, moveInputPos_zero]
    rfl
  obtain ⟨a, ha, hprep, hpreps⟩ := f2_splitBody_prepare M start w s
  obtain ⟨b, hb, hcount, hcounts⟩ := f2_splitBody_count M start w s out T hT
  obtain ⟨h1, hs1⟩ := f2_splitSafe_join tm .anchor p _ d (a + 1) b hprep hpreps hcount hcounts
  have hcheck : tm.step d = c.mapState (f2_SplitBodyState.rewind ok) := by
    unfold MultiTapeTM.step
    change (controlAction 0 (some (.rewind
      (!decide (w.length < s.length + out.length) && d.inputSymbol.isNone) 0))).apply d = _
    rw [controlAction_apply, moveInputPos_zero]
    have hok := f2_splitCount_accept f2_SplitBodyState.count f2_SplitBodyState.check w s
      (f2_splitBank M s none out)
    change (!decide (w.length < s.length + out.length) && d.inputSymbol.isNone) = ok at hok
    rw [hok]
    rfl
  obtain ⟨hcheck', hchecks⟩ := f2_splitSafe_one tm .anchor d _ hcheck
    (by simp [d, f2_splitCountCfg, f2_splitBank]) (by simp [c, Cfg.mapState])
  obtain ⟨h2, hs2⟩ := f2_splitSafe_join tm .anchor p d _ (a + 1 + b) 1 h1 hs1 hcheck' hchecks
  obtain ⟨v, hv, hrew, hrews⟩ := f2_splitBody_rewind M start w ok c rfl
  obtain ⟨h3, hs3⟩ := f2_splitSafe_join tm .anchor p _ r (a + 1 + b + 1) v h2 hs2 hrew hrews
  have hv' : v ≤ w.length + 3 := by
    have hp : c.inputPos.val ≤ w.length + 1 := by simp [c, f2_splitPos]
    omega
  by_cases hok : s.length + out.length = w.length
  · have hs : s.length ≤ w.length := by omega
    let ec := f2_splitEmitCfg M.k w s (some 0) 0 0 []
    let ed := f2_splitEmitCfg M.k w s none w.length s.length
      (pairEncode (w.take s.length) (w.drop s.length))
    have hdispatch : tm.step r = ec.mapState f2_SplitBodyState.emit := by
      simp only [r, c, Cfg.mapState, Option.map_some, MultiTapeTM.step,
        tm, f2_splitBodyTM, ↓reduceIte, ok, hok, decide_true]
      rw [controlAction_apply, moveInputPos_zero]
      refine Cfg.ext rfl ?_ rfl rfl rfl
      simp [ec, f2_splitEmitCfg, f2_splitPos]
    obtain ⟨hd, hds⟩ := f2_splitSafe_one tm .anchor r _ hdispatch
      (by simp [r, Cfg.mapState]) (by simp [ec, Cfg.mapState, f2_splitEmitCfg])
    obtain ⟨h4, hs4⟩ := f2_splitSafe_join tm .anchor p r _ (a + 1 + b + 1 + v) 1 h3 hs3 hd hds
    have hemit : tm.runFrom (ec.mapState f2_SplitBodyState.emit) (s.length + w.length + 3) =
        ed.mapState f2_SplitBodyState.emit := by
      rw [f2_splitEmbed_run (f2_splitEmitTM M.k).tm tm f2_SplitBodyState.emit (fun _ _ _ => rfl)]
      exact congrArg (Cfg.mapState f2_SplitBodyState.emit) (f2_splitEmit_run M.k w s hs)
    have hemits : f2_splitSafe tm .anchor (ec.mapState f2_SplitBodyState.emit) (s.length + w.length + 3) := by
      intro j hj
      rw [f2_splitEmbed_run (f2_splitEmitTM M.k).tm tm f2_SplitBodyState.emit (fun _ _ _ => rfl)]
      cases hq : ((f2_splitEmitTM M.k).tm.runFrom ec j).state <;> simp [Cfg.mapState, hq]
    obtain ⟨h5, hs5⟩ := f2_splitSafe_join tm .anchor p _ _ (a + 1 + b + 1 + v + 1)
      (s.length + w.length + 3) h4 hs4 hemit hemits
    let u := a + 1 + b + 1 + v + 1 + (s.length + w.length + 3)
    have hend : tm.runFrom z (1 + u) = ed.mapState f2_SplitBodyState.emit := by
      rw [MultiTapeTM.runFrom_add, hdepart]; exact h5
    refine ⟨1 + u, by omega, by dsimp [u]; omega, ?_, ?_⟩
    · intro j hj hjt
      change (tm.runFrom z j).state ≠ _
      rw [show j = 1 + (j - 1) by omega, MultiTapeTM.runFrom_add, hdepart]
      exact hs5 (j - 1) (by dsimp [u] at hjt; omega)
    · simp only [hok, decide_true, ↓reduceIte]
      change (tm.runFrom z (1 + u)).state = none ∧ _
      rw [hend]
      exact ⟨rfl, rfl⟩
  · let rc := (f2_splitRestoreScan M.k w s 0).mapState (f2_SplitBodyState.restore (S := M.State))
    have hdispatch : tm.step r = rc := by
      simp only [r, c, Cfg.mapState, Option.map_some, MultiTapeTM.step,
        tm, f2_splitBodyTM, ↓reduceIte, ok, hok, decide_false, Bool.false_eq_true]
      rw [controlAction_apply, moveInputPos_zero]
      refine Cfg.ext ?_ ?_ ?_ ?_ rfl
      · simp [rc, f2_splitRestoreScan, Cfg.mapState]
      · simp [rc, f2_splitRestoreScan, Cfg.mapState, f2_splitPos]
      · funext i
        refine Fin.cases ?_ (fun l => ?_) i
        · rfl
        · funext z; simp [rc, f2_splitRestoreScan, Cfg.mapState, f2_splitScratch, f2_catalogPolyTape]
      · funext i
        refine Fin.cases ?_ (fun l => ?_) i <;> rfl
    obtain ⟨hd, hds⟩ := f2_splitSafe_one tm .anchor r rc hdispatch
      (by simp [r, Cfg.mapState]) (by simp [rc, Cfg.mapState, f2_splitRestoreScan])
    obtain ⟨h4, hs4⟩ := f2_splitSafe_join tm .anchor p r rc (a + 1 + b + 1 + v) 1 h3 hs3 hd hds
    obtain ⟨l, hl, hrest, hrests⟩ := f2_splitBody_restore M start w s
    obtain ⟨h5, hs5⟩ := f2_splitSafe_join tm .anchor p rc _ (a + 1 + b + 1 + v + 1) l h4 hs4 hrest hrests
    let u := a + 1 + b + 1 + v + 1 + l
    have hreturn : tm.step (Cfg.ofWords (.restore (4, false)) (stateWord (M.k + 1) (f2_splitStep w s))) =
        Cfg.ofWords (input := w) .anchor (stateWord (M.k + 1) (f2_splitStep w s)) := by
      change (controlAction 0 (some (f2_SplitBodyState.anchor (S := M.State)))).apply _ = _
      rw [controlAction_apply, moveInputPos_zero]
      rfl
    refine ⟨1 + u + 1, by omega, by dsimp [u]; omega, ?_, ?_⟩
    · intro j hj hjt
      change (tm.runFrom z j).state ≠ _
      rw [show j = 1 + (j - 1) by omega, MultiTapeTM.runFrom_add, hdepart]
      exact hs5 (j - 1) (by dsimp [u] at hjt; omega)
    · simp only [hok, decide_false, Bool.false_eq_true, ↓reduceIte]
      change tm.runFrom z (1 + u + 1) = _
      rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_add, hdepart, h5, hreturn]

/-- Given the concrete startup and round contracts, the audited loop supplies
the frozen split-search result and exponent. No body contract is assumed as an
axiom: both are explicit arguments, including the positive silent stall.
**Proof sketch.** Enlarge the body coefficient to cover the existing binary
length machine, instantiate the proved loop, identify its unary orbit and
finite search, then apply the checked exponent calculation. -/
private lemma f2_splitSolve_of_body (C e : ℕ) (body : FinTM Bool) (anchor : body.State)
    (A : ℕ)
    (hstart : ∀ w : List Bool, ∃ t ≤ A * (w.length + 1) ^ (e + 1),
      (∀ t' < t, (body.tm.runFrom (body.tm.initCfg w) t').state ≠ some anchor) ∧
      body.tm.runFrom (body.tm.initCfg w) t =
        Cfg.ofWords anchor (stateWord body.k []))
    (hround : ∀ (w s : List Bool), s.length ≤ w.length + 1 →
      ∃ t, 0 < t ∧ t ≤ A * (w.length + 1) ^ (e + 1) ∧
        (∀ t', 0 < t' → t' < t →
          (body.tm.runFrom (Cfg.ofWords (input := w) anchor (stateWord body.k s)) t').state
            ≠ some anchor) ∧
        if f2_splitAccept C e w s then
          (body.tm.runFrom (Cfg.ofWords (input := w) anchor (stateWord body.k s)) t).state = none ∧
          (body.tm.runFrom (Cfg.ofWords (input := w) anchor (stateWord body.k s)) t).output =
            pairEncode (w.take s.length) (w.drop s.length)
        else
          body.tm.runFrom (Cfg.ofWords (input := w) anchor (stateWord body.k s)) t =
            Cfg.ofWords anchor (stateWord body.k (f2_splitStep w s))) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun w => match solveSplit C e w.length with
          | some i => pairEncode (w.take i) (w.drop i)
          | none => []) (fun n => c * (n + 1) ^ (e + 2)) ∧
      ∀ x t, M.tm.spaceUsed (M.tm.initCfg x) t ≤ c * (x.length + 1) ^ (e + 1) := by
  obtain ⟨F, a, hF, _⟩ := computesFunInTime_lengthBits_spaceUsed
  have hn (n : ℕ) : n + 1 ≤ (n + 1) ^ (e + 1) := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right (Nat.succ_pos n)
      (show 1 ≤ e + 1 by omega)
  have hbody (n : ℕ) : A * (n + 1) ^ (e + 1) ≤ (A + a) * (n + 1) ^ (e + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  have hF' : F.ComputesFunInTime (fun w => Nat.bits w.length)
      (fun n => (A + a) * (n + 1) ^ (e + 1)) := by
    intro w
    apply (hF w).mono
    exact (Nat.mul_le_mul_left a (hn w.length)).trans (Nat.mul_le_mul_right _ (by omega))
  obtain ⟨M, c, hM, hspace⟩ := f2_exists_loopFind_space body F anchor
    (fun w s => s.length ≤ w.length + 1) f2_splitStep (f2_splitAccept C e)
    (fun w s => pairEncode (w.take s.length) (w.drop s.length)) (fun _ => [])
    id (fun n => (A + a) * (n + 1) ^ (e + 1)) hF'
    (by intro w; simp) f2_splitStep_inv
    (by
      intro w
      obtain ⟨t, ht, hi, hh⟩ := hstart w
      exact ⟨t, ht.trans (hbody w.length), hi, hh⟩)
    (by
      intro w s hs
      obtain ⟨t, htpos, ht, hi, hh⟩ := hround w s hs
      exact ⟨t, htpos, ht.trans (hbody w.length), hi, hh⟩)
  refine ⟨M, 2 * c * (A + a + 1), ?_, ?_⟩
  · intro w
    have hm := hM w
    dsimp only [id_eq] at hm
    convert hm.mono (f2_splitLoop_bound c (A + a) e w.length) using 1
    exact (f2_splitLoop_result C e w).symm

  · intro x t
    have h := hspace x t
    have hp : 1 ≤ (x.length + 1) ^ (e + 1) := Nat.one_le_pow _ _ (Nat.succ_pos _)
    have hb : (A + a) * (x.length + 1) ^ (e + 1) + 1 ≤
        (A + a + 1) * (x.length + 1) ^ (e + 1) := by
      simp only [Nat.add_mul, Nat.one_mul]
      omega
    calc
      _ ≤ c * ((A + a + 1) * (x.length + 1) ^ (e + 1)) :=
        h.trans (Nat.mul_le_mul_left c hb)
      _ = (c * (A + a + 1)) * (x.length + 1) ^ (e + 1) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _
        (Nat.mul_le_mul_right _ (by omega : c ≤ 2 * c))

/-- The positive-exponent source is the already proved nested-loop phase,
started on the prepared bank rather than rerunning input initialization. -/
private lemma f2_splitSource_poly (c C : ℕ) (s : List Bool) :
    (f2_catalogPolyUnaryTM c C).tm.runFrom
      (f2_splitBank (f2_catalogPolyUnaryTM c C) s (some (.loop (Fin.last c))) [])
      (f2_catalogPolyCost (s.length + 1) C (c + 1) + 1) =
      f2_splitBank (f2_catalogPolyUnaryTM c C) s none
        (List.replicate (C * (s.length + 1) ^ (c + 1)) true) := by
  simpa [f2_splitBank, f2_catalogPolyCfg] using f2_splitPoly_loop_end c C (s.length + 1) (by omega)

/-- Exponent zero uses the fixed prefix source on empty virtual input, with
no scratch tapes. Its last blank-reading step is included in the bound. -/
private lemma f2_splitSource_constant (C : ℕ) (s : List Bool) :
    (f2_catalogPrefixTM (List.replicate C true)).tm.runFrom
      (f2_splitBank (f2_catalogPrefixTM (List.replicate C true)) s (some (0 : Fin ((List.replicate C true).length + 1))) []) (C + 1) =
      f2_splitBank (f2_catalogPrefixTM (List.replicate C true)) s none (List.replicate C true) := by
  have hi : f2_splitBank (f2_catalogPrefixTM (List.replicate C true)) s (some (0 : Fin ((List.replicate C true).length + 1))) [] =
      (f2_catalogPrefixTM (List.replicate C true)).tm.initCfg [] := by
    apply Cfg.ext_zero_tapes <;> rfl
  rw [hi, MultiTapeTM.runFrom_succ_eq_step']
  have he := f2_catalogPrefixTM_emit (List.replicate C true) [] C (by simp)
  rw [he]
  simp only [List.take_replicate, Nat.min_self]
  apply Cfg.ext_zero_tapes <;>
    simp [MultiTapeTM.step, f2_catalogPrefixTM, f2_catalogPrefixCfg, Cfg.inputSymbol,
      Fin.ext_iff, Action.apply, f2_splitBank]

/-- The invariant bounds every candidate, including the one-past-end stall,
inside one common body envelope. The factor `2^e` covers the prepared side
length `|s|+1 ≤ 2(|w|+1)` without increasing the exponent.
**Proof sketch.** Bound the source by its proved box cost, compare the two
side lengths, and absorb all linear controller overhead into forty copies of
the positive polynomial envelope. -/
private lemma f2_splitBody_envelope (C e l n T : ℕ) (hl : l ≤ n + 1)
    (hT : T ≤ (C + 1 + 5 * e) * (l + 1) ^ e + 1) :
    T + 5 * l + 3 * n + 20 ≤
      ((C + 1 + 5 * e) * 2 ^ e + 40) * (n + 1) ^ (e + 1) := by
  have hp : (l + 1) ^ e ≤ 2 ^ e * (n + 1) ^ (e + 1) := by
    calc
      (l + 1) ^ e ≤ (2 * (n + 1)) ^ e := Nat.pow_le_pow_left (by omega) e
      _ = 2 ^ e * (n + 1) ^ e := Nat.mul_pow _ _ _
      _ ≤ 2 ^ e * (n + 1) ^ (e + 1) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
  have hmul := Nat.mul_le_mul_left (C + 1 + 5 * e) hp
  have hn : n + 1 ≤ (n + 1) ^ (e + 1) := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right (Nat.succ_pos n)
      (show 1 ≤ e + 1 by omega)
  have hlin : 5 * l + 3 * n + 21 ≤ 40 * (n + 1) ^ (e + 1) := by omega
  calc
    T + 5 * l + 3 * n + 20 ≤
        (C + 1 + 5 * e) * (2 ^ e * (n + 1) ^ (e + 1)) +
          40 * (n + 1) ^ (e + 1) := by omega
    _ = _ := by ring

/-- Instantiate the completed controller with an exact unary-output source.
The source assumption is discharged below separately for zero and positive
exponents; startup and the full body round have already been constructed.
**Proof sketch.** Supply the exact zero-time startup and constructed round to
the existing loop closure. The common envelope bounds the actual phase times,
and the source's unary-output length identifies the checked acceptance test. -/
private lemma f2_splitSolve_source (C e : ℕ) (M : FinTM Bool) (start : M.State)
    (B : ℕ → ℕ)
    (hsource : ∀ s : List Bool, M.tm.runFrom (f2_splitBank M s (some start) []) (B s.length) =
      f2_splitBank M s none (List.replicate (C * (s.length + 1) ^ e) true))
    (hbound : ∀ l, B l ≤ (C + 1 + 5 * e) * (l + 1) ^ e + 1) :
    ∃ (N : FinTM Bool) (c : ℕ),
      N.ComputesFunInTime
        (fun w => match solveSplit C e w.length with
          | some i => pairEncode (w.take i) (w.drop i)
          | none => []) (fun n => c * (n + 1) ^ (e + 2)) ∧
      ∀ x t, N.tm.spaceUsed (N.tm.initCfg x) t ≤ c * (x.length + 1) ^ (e + 1) := by
  apply f2_splitSolve_of_body C e (f2_splitBodyTM M start) .anchor
    ((C + 1 + 5 * e) * 2 ^ e + 40)
  · intro w
    refine ⟨0, Nat.zero_le _, ?_, ?_⟩
    · intro j hj; omega
    · exact f2_splitBody_start M start w
  · intro w s hs
    obtain ⟨t, htpos, ht, hsafe, hend⟩ := f2_splitBody_round M start w s
      (List.replicate (C * (s.length + 1) ^ e) true) (B s.length) (hsource s)
    refine ⟨t, htpos, ht.trans (f2_splitBody_envelope C e s.length w.length (B s.length)
      hs (hbound s.length)), hsafe, ?_⟩
    simpa only [f2_splitAccept, List.length_replicate] using hend

/-- Close the two exponent cases privately, so compiler-generated proof
helpers also remain private. Both cases instantiate the concrete body and
its proved round contract through the exact source interfaces. -/
private lemma f2_splitSolve_closed (C e : ℕ) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun w => match solveSplit C e w.length with
          | some i => pairEncode (w.take i) (w.drop i)
          | none => [])
        (fun n => c * (n + 1) ^ (e + 2)) ∧
      ∀ x t, M.tm.spaceUsed (M.tm.initCfg x) t ≤ c * (x.length + 1) ^ (e + 1) := by
  cases e with
  | zero =>
    apply f2_splitSolve_source C 0 (f2_catalogPrefixTM (List.replicate C true))
      (0 : Fin ((List.replicate C true).length + 1)) (fun _ => C + 1)
    · intro s
      simpa using f2_splitSource_constant C s
    · intro l; simp
  | succ e =>
    apply f2_splitSolve_source C (e + 1) (f2_catalogPolyUnaryTM e C) (.loop (Fin.last e))
      (fun l => f2_catalogPolyCost (l + 1) C (e + 1) + 1)
    · exact f2_splitSource_poly e C
    · intro l
      exact Nat.add_le_add_right (f2_catalogPolyCost_le (l + 1) C (by omega) (e + 1)) 1

/-- **P15 space row, split search** (spec, fill pending — design §12 R3;
annotates `Turing.FinTM.computesFunInTime_splitSolve`). The padding
split search runs in space one polynomial degree below its time: per
candidate it rebuilds unary banks of size at most `C·(n+1)^e` in place,
and candidates reuse the same banks.

**Proof sketch.** Head-movement count of the loop body's phases: the
candidate banks and the generator's output bank are rebuilt in place
every round (the round seam restores heads to the origin), so the
per-tape visited sets are intervals of length at most the largest bank,
`C·(n+1)^e` cells plus linear administration; the round count multiplies
time, not space. -/
theorem computesFunInTime_splitSolve_spaceUsed (C e : ℕ) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun w => match solveSplit C e w.length with
          | some i => pairEncode (w.take i) (w.drop i)
          | none => [])
        (fun n => c * (n + 1) ^ (e + 2)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c * (x.length + 1) ^ (e + 1) := by
  exact f2_splitSolve_closed C e

/- Local copies of the W2 correspondence from Build/Wrappers.lean.
The originals are private; the all-time trajectory is needed for the space row. -/
/-- Map a source state and its last-emission register to simulation, halt,
or the stationary live loop. An empty register never matches a bit. -/
private def catalog_redirectState {S : Type} (haltOn : Bool) (q : Option S)
    (r : Option Bool) : Option ((S × Option Bool) ⊕ Unit) :=
  match q with
  | some s => some (.inl (s, r))
  | none => if r = some haltOn then none else some (.inr ())

/-- Suppress physical emission, updating the register before the halt test. -/
private def catalog_redirectAction {k : ℕ} {S : Type} (haltOn : Bool)
    (a : Action k Bool S) (r : Option Bool) : Action k Bool ((S × Option Bool) ⊕ Unit) :=
  ⟨a.inputTape, a.workTapes, none, catalog_redirectState haltOn a.state (a.output.or r)⟩

/-- The source tapes and input head are unchanged; its last emitted bit is
remembered in control and the physical output is empty. -/
private def catalog_redirectCfg (M : FinTM Bool) (haltOn : Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) : Cfg (redirectTM M haltOn).k Bool
      (redirectTM M haltOn).State x :=
  ⟨catalog_redirectState haltOn c.state c.output.getLast?, c.inputPos,
    c.workTapes, c.workTapePos, []⟩

/-- The stationary live loop is fixed by every subsequent transition. -/
private lemma catalog_redirect_loop (M : FinTM Bool) (haltOn : Bool) {x : List Bool}
    (c : Cfg (redirectTM M haltOn).k Bool (redirectTM M haltOn).State x)
    (hs : c.state = some (.inr ())) (t : ℕ) :
    (redirectTM M haltOn).tm.runFrom c t = c := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih]
    apply Cfg.ext <;> simp [MultiTapeTM.step, hs, redirectTM, Action.apply]

/-- Capture and application commute because the last entry of an appended
singleton is the new bit, while no emission leaves the old register intact. -/
private lemma catalog_redirect_apply (M : FinTM Bool) (haltOn : Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (a : Action M.k Bool M.State) :
    (catalog_redirectAction haltOn a c.output.getLast?).apply (catalog_redirectCfg M haltOn c) =
      catalog_redirectCfg M haltOn (a.apply c) := by
  have hlast : (c.output ++ a.output.toList).getLast? = a.output.or c.output.getLast? := by
    cases a.output <;> simp
  refine Cfg.ext ?_ rfl rfl rfl rfl
  dsimp only [catalog_redirectCfg, catalog_redirectAction, Action.apply]
  rw [hlast]

/-- The correspondence also holds after a source halt: a matching result
is absorbed as halted, and a mismatching result is absorbed in the live loop.
This adapts `acceptCfg_step` in the HALT reduction to an optional register. -/
private lemma catalog_redirect_step (M : FinTM Bool) (haltOn : Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) :
    (redirectTM M haltOn).tm.step (catalog_redirectCfg M haltOn c) =
      catalog_redirectCfg M haltOn (M.tm.step c) := by
  cases hs : c.state with
  | none =>
    rw [MultiTapeTM.step_of_halt hs]
    by_cases hr : c.output.getLast? = some haltOn
    · exact MultiTapeTM.step_of_halt (by simp [catalog_redirectCfg, catalog_redirectState, hs, hr])
    · exact catalog_redirect_loop M haltOn (catalog_redirectCfg M haltOn c)
        (by simp [catalog_redirectCfg, catalog_redirectState, hs, hr]) 1
  | some q =>
    have hi : (catalog_redirectCfg M haltOn c).inputSymbol = c.inputSymbol := rfl
    have hw : (catalog_redirectCfg M haltOn c).workTapeSymbols = c.workTapeSymbols := rfl
    have hstate : (catalog_redirectCfg M haltOn c).state = some (.inl (q, c.output.getLast?)) := by
      simp only [catalog_redirectCfg, catalog_redirectState, hs]
    simp only [MultiTapeTM.step, hstate, hs]
    rw [hi, hw]
    have htr : (redirectTM M haltOn).tm.tr (.inl (q, c.output.getLast?))
        c.inputSymbol c.workTapeSymbols =
        catalog_redirectAction haltOn (M.tm.tr q c.inputSymbol c.workTapeSymbols) c.output.getLast? := by
      cases hq : (M.tm.tr q c.inputSymbol c.workTapeSymbols).state <;>
        cases ho : (M.tm.tr q c.inputSymbol c.workTapeSymbols).output <;>
          simp [redirectTM, catalog_redirectAction, catalog_redirectState, hq, ho]
    rw [htr]
    exact catalog_redirect_apply M haltOn c _

/-- Initialized runs commute with redirection at every time, including
after a source halt. This is the last-emission invariant for both clauses. -/
private lemma catalog_redirect_run (M : FinTM Bool) (haltOn : Bool) (x : List Bool) (t : ℕ) :
    (redirectTM M haltOn).tm.runFrom ((redirectTM M haltOn).tm.initCfg x) t =
      catalog_redirectCfg M haltOn (M.tm.runFrom (M.tm.initCfg x) t) := by
  have hi : (redirectTM M haltOn).tm.initCfg x = catalog_redirectCfg M haltOn (M.tm.initCfg x) := rfl
  rw [hi]
  exact MultiTapeTM.runFrom_comm_of_step (catalog_redirectCfg M haltOn) (catalog_redirect_step M haltOn)
    (M.tm.initCfg x) t


/-- **W2 space row** (spec, fill pending — design §12 R3, decision 12.3;
annotates `Turing.FinTM.redirectTM` beside its
`redirectTM_computes`/`redirectTM_live` contract pair). Redirection costs
no space, per tape and exactly: the redirected machine's tape actions are
the source's verbatim, before and after the source halt.

**Proof sketch.** `redirect_run`'s configuration correspondence preserves
work tapes and heads at every time (the live loop is stationary and the
simulation phase copies the source's tape actions), so the two head
trajectories coincide pointwise and the visited images agree. -/
theorem redirectTM_spaceUsedByTape (M : FinTM Bool) (haltOn : Bool)
    (x : List Bool) (t : ℕ) (i : Fin M.k) :
    (redirectTM M haltOn).tm.spaceUsedByTape
        ((redirectTM M haltOn).tm.initCfg x) t i
      = M.tm.spaceUsedByTape (M.tm.initCfg x) t i := by
  unfold MultiTapeTM.spaceUsedByTape MultiTapeTM.visitedByTapeHead
  congr 1
  apply Finset.image_congr
  intro u _
  dsimp only
  rw [catalog_redirect_run]
  rfl

/-- Pad the decider with the fresh branch tapes. The added tapes are idle,
so the public left-block simulation supplies its complete run invariant. -/
private def f2_timedPadTM (D : FinTM Bool) (r : ℕ) : MultiTapeTM (D.k + r) Bool D.State where
  q₀ := D.tm.q₀
  tr q inp work := leftAction r id (D.tm.tr q inp (fun i => work (Fin.castAdd r i)))

/-- The conditional controller captures the decider on the last tape,
steps back to read its singleton verdict, rewinds the physical input, then
runs the selected branch on its untouched tape bank. In the administrative
states, the first Boolean distinguishes back/read and the second distinguishes
rewind-start/scan. The branch transition table is independent of its selector. -/
private def f2_timedCondTM (D M₁ M₂ : FinTM Bool) : FinTM Bool where
  k := (D.k + (M₁.k + M₂.k)) + 1
  State := D.State ⊕ (Bool ⊕ ((Bool × Bool) ⊕ (M₁.State ⊕ M₂.State)))
  tm :=
    { q₀ := .inl D.tm.q₀
      tr := fun q inp work => match q with
        | .inl q => captureAction Sum.inl (.inr (.inl false))
            ((f2_timedPadTM D (M₁.k + M₂.k)).tr q inp (fun i => work i.castSucc))
        | .inr (.inl false) =>
          ⟨0, (fun i => if (i : ℕ) < D.k + (M₁.k + M₂.k) then (none, 0)
            else (none, .neg)), none, some (.inr (.inl true))⟩
        | .inr (.inl true) => controlAction 0
            (some (.inr (.inr (.inl ((work (Fin.last _)).getD false, false)))))
        | .inr (.inr (.inl (b, false))) =>
            controlAction .neg (some (.inr (.inr (.inl (b, true)))))
        | .inr (.inr (.inl (b, true))) => match inp with
          | some _ => controlAction .neg (some (.inr (.inr (.inl (b, true)))))
          | none => controlAction .pos
              (some (.inr (.inr (.inr (branchTM M₁ M₂ b).tm.q₀))))
        | .inr (.inr (.inr q)) => leftAction 1 id
            (rightAction D.k (fun s => .inr (.inr (.inr s)))
              ((branchTM M₁ M₂ false).tm.tr q inp
                (fun i => work (Fin.natAdd D.k i).castSucc))) }

/-- The branch configuration retains the decider's finished work and the
captured verdict; its own state, input head, work tapes, and output are exact. -/
private def f2_timedBranchCfg (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg (M₁.k + M₂.k) Bool (M₁.State ⊕ M₂.State) x)
    (tapes : Fin D.k → ℤ → Option Bool) (heads : Fin D.k → ℤ) (b : Bool) :
    Cfg (f2_timedCondTM D M₁ M₂).k Bool (f2_timedCondTM D M₁ M₂).State x :=
  leftCfg id (rightCfg (fun s => .inr (.inr (.inr s))) c tapes heads)
    (fun (_ : Fin 1) => bufferTape [b]) (fun _ => 0)

/-- The decider's configuration inside its padded, captured simulation.
Both branch tape banks are blank throughout this phase. -/
private def f2_timedControlCfg (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg D.k Bool D.State x) :
    Cfg (f2_timedCondTM D M₁ M₂).k Bool (f2_timedCondTM D M₁ M₂).State x :=
  captureCfg Sum.inl (.inr (.inl false)) [] []
    (leftCfg id c (fun (_ : Fin (M₁.k + M₂.k)) _ => none) (fun _ => 0))

/-- The capture contract, instantiated on the padded decider, gives the
entire controller phase through its first halt. -/
private lemma f2_timed_capture (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg D.k Bool D.State x) (t : ℕ)
    (hlive : ∀ s < t, ¬(D.tm.runFrom c s).Halted) :
    (f2_timedCondTM D M₁ M₂).tm.runFrom (f2_timedControlCfg D M₁ M₂ c) t =
      f2_timedControlCfg D M₁ M₂ (D.tm.runFrom c t) := by
  have hpad (u : ℕ) := leftCfg_run D.tm (f2_timedPadTM D (M₁.k + M₂.k)) id
    (fun _ _ _ => rfl) c (fun _ _ => none) (fun _ => 0) u
  have h := capture_run (f2_timedPadTM D (M₁.k + M₂.k)) (f2_timedCondTM D M₁ M₂).tm
    Sum.inl (.inr (.inl false)) (fun _ _ _ => rfl) [] []
    (leftCfg id c (fun _ _ => none) (fun _ => 0)) t (fun s hs => by
      unfold Cfg.Halted
      rw [hpad s]
      simpa only [leftCfg, Option.map_id] using hlive s hs)
  simpa only [hpad t] using h

/-- The host's genuine initial configuration is the captured, padded
initial configuration: all three work-tape blocks are blank. -/
private lemma f2_timed_control_init (D M₁ M₂ : FinTM Bool) (x : List Bool) :
    (f2_timedCondTM D M₁ M₂).tm.initCfg x =
      f2_timedControlCfg D M₁ M₂ (D.tm.initCfg x) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    by_cases hi : (i : ℕ) < D.k + (M₁.k + M₂.k)
    · simp only [f2_timedControlCfg, captureCfg, leftCfg, MultiTapeTM.initCfg,
        Cfg.init, dif_pos hi]
      exact (Fin.addCases (fun _ => by simp) (fun _ => by simp) ⟨i, hi⟩)
    · simp [f2_timedControlCfg, captureCfg, leftCfg, hi]
  · funext i
    by_cases hi : (i : ℕ) < D.k + (M₁.k + M₂.k)
    · simp only [f2_timedControlCfg, captureCfg, leftCfg, MultiTapeTM.initCfg,
        Cfg.init, dif_pos hi]
      exact (Fin.addCases (fun _ => by simp) (fun _ => by simp) ⟨i, hi⟩)
    · simp [f2_timedControlCfg, captureCfg, leftCfg, hi]

/-- Once dispatched, the selected branch runs in lockstep while the old
decider tapes and singleton capture tape remain idle.
**Proof sketch.** The branch action is a right-block embedding followed by
a left-block embedding; compose their application lemmas, then iterate. -/
private lemma f2_timed_branch_run (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg (M₁.k + M₂.k) Bool (M₁.State ⊕ M₂.State) x)
    (tapes : Fin D.k → ℤ → Option Bool) (heads : Fin D.k → ℤ) (b : Bool) (t : ℕ) :
    (f2_timedCondTM D M₁ M₂).tm.runFrom (f2_timedBranchCfg D M₁ M₂ c tapes heads b) t =
      f2_timedBranchCfg D M₁ M₂ ((branchTM M₁ M₂ b).tm.runFrom c t) tapes heads b := by
  apply MultiTapeTM.runFrom_comm_of_step (fun c => f2_timedBranchCfg D M₁ M₂ c tapes heads b)
  intro d
  cases hs : d.state with
  | none =>
    simp only [MultiTapeTM.step, f2_timedBranchCfg, leftCfg, rightCfg, hs, Option.map_none]
  | some q =>
    have hstate : (f2_timedBranchCfg D M₁ M₂ d tapes heads b).state =
        some (.inr (.inr (.inr q))) := by
      simp only [f2_timedBranchCfg, leftCfg, rightCfg, hs, Option.map_some, id_eq]
    have hi : (f2_timedBranchCfg D M₁ M₂ d tapes heads b).inputSymbol = d.inputSymbol := rfl
    have hw : (fun i => (f2_timedBranchCfg D M₁ M₂ d tapes heads b).workTapeSymbols
        (Fin.natAdd D.k i).castSucc) = d.workTapeSymbols := by
      funext i
      simp only [f2_timedBranchCfg, leftCfg, rightCfg, Cfg.workTapeSymbols,
        Fin.castSucc, Fin.addCases_left, Fin.addCases_right]
    simp only [MultiTapeTM.step, hstate, hs]
    dsimp only [f2_timedCondTM]
    let emb : (M₁.State ⊕ M₂.State) → (f2_timedCondTM D M₁ M₂).State :=
      fun s => .inr (.inr (.inr s))
    change (leftAction 1 id (rightAction D.k emb
      ((branchTM M₁ M₂ b).tm.tr q d.inputSymbol
        (fun i => (f2_timedBranchCfg D M₁ M₂ d tapes heads b).workTapeSymbols
          (Fin.natAdd D.k i).castSucc)))).apply
        (leftCfg id (rightCfg emb d tapes heads)
          (fun (_ : Fin 1) => bufferTape [b]) (fun _ => 0)) = _
    erw [hw, leftCfg_apply, rightCfg_apply]
    rfl

/-- After reading the verdict, all branch data are initialized; only the
input head still needs rewinding. The capture head is back at cell zero. -/
private def f2_timedReadyCfg (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg D.k Bool D.State x) (b : Bool) :
    Cfg (f2_timedCondTM D M₁ M₂).k Bool (f2_timedCondTM D M₁ M₂).State x :=
  { f2_timedBranchCfg D M₁ M₂ ((branchTM M₁ M₂ b).tm.initCfg x) c.workTapes c.workTapePos b with
    state := some (.inr (.inr (.inl (b, false))))
    inputPos := c.inputPos }

/-- Two silent transitions move the capture head left and read the completed
singleton verdict, without touching the input or either work bank.
**Proof sketch.** The final capture head is one past the singleton, hence at
one. Moving it left exposes exactly its bit at zero; the next transition
records that bit in the rewind state. -/
private lemma f2_timed_read (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg D.k Bool D.State x) (b : Bool) (hs : c.state = none) (ho : c.output = [b]) :
    (f2_timedCondTM D M₁ M₂).tm.runFrom (f2_timedControlCfg D M₁ M₂ c) 2 =
      f2_timedReadyCfg D M₁ M₂ c b := by
  let ready := f2_timedReadyCfg D M₁ M₂ c b
  have hback : (f2_timedCondTM D M₁ M₂).tm.step (f2_timedControlCfg D M₁ M₂ c) =
      {ready with state := some (.inr (.inl true))} := by
    have hstate : (f2_timedControlCfg D M₁ M₂ c).state = some (.inr (.inl false)) := by
      simp [f2_timedControlCfg, captureCfg, leftCfg, hs]
    simp only [MultiTapeTM.step, hstate]
    refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j
        simp [f2_timedCondTM, Action.apply, f2_timedControlCfg, captureCfg, leftCfg,
          f2_timedReadyCfg, f2_timedBranchCfg, rightCfg, ready, j.isLt]
        refine Fin.addCases ?_ ?_ j <;> intro z <;> simp
      · intro j
        simp [f2_timedCondTM, Action.apply, f2_timedControlCfg, captureCfg, leftCfg,
          f2_timedReadyCfg, f2_timedBranchCfg, rightCfg, ready, ho]
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j
        simp [f2_timedCondTM, Action.apply, f2_timedControlCfg, captureCfg, leftCfg,
          f2_timedReadyCfg, f2_timedBranchCfg, rightCfg, ready, j.isLt]
        refine Fin.addCases ?_ ?_ j <;> intro z <;> simp
      · intro j
        simp [f2_timedCondTM, Action.apply, f2_timedControlCfg, captureCfg, leftCfg,
          f2_timedReadyCfg, f2_timedBranchCfg, rightCfg, ready, ho]
  have hread : (f2_timedCondTM D M₁ M₂).tm.step
      {ready with state := some (.inr (.inl true))} = ready := by
    have hsym : ({ready with state := some (.inr (.inl true))} :
        Cfg (f2_timedCondTM D M₁ M₂).k Bool (f2_timedCondTM D M₁ M₂).State x).workTapeSymbols
        (Fin.last _) = some b := by
      change (f2_timedBranchCfg D M₁ M₂ ((branchTM M₁ M₂ b).tm.initCfg x)
        c.workTapes c.workTapePos b).workTapeSymbols
          (Fin.natAdd (D.k + (M₁.k + M₂.k)) (0 : Fin 1)) = some b
      simp [f2_timedBranchCfg, leftCfg, rightCfg, Cfg.workTapeSymbols, bufferTape]
    unfold MultiTapeTM.step
    dsimp only
    change ((controlAction 0 (some (.inr (.inr (.inl
      ((({ready with state := some (.inr (.inl true))} :
        Cfg (f2_timedCondTM D M₁ M₂).k Bool (f2_timedCondTM D M₁ M₂).State x).workTapeSymbols
        (Fin.last _)).getD false, false)))))) :
          Action (f2_timedCondTM D M₁ M₂).k Bool (f2_timedCondTM D M₁ M₂).State).apply _ = _
    rw [hsym, controlAction_apply]
    simp only [Option.getD_some, moveInputPos_zero]
    rfl
  change (f2_timedCondTM D M₁ M₂).tm.step
    ((f2_timedCondTM D M₁ M₂).tm.step (f2_timedControlCfg D M₁ M₂ c)) = _
  rw [hback, hread]

/-- A singleton-output decider reaches the selected branch's genuine
initial configuration in at most twice its budget plus five steps.
**Proof sketch.** Choose the first source halt, which is within the supplied
budget. Capture until that halt, read the singleton in two steps, and rewind
in at most the current input position plus two. The head-position bound
charges this rewind to the decider's elapsed steps, not the input length. -/
private lemma f2_timed_start (D M₁ M₂ : FinTM Bool) (x : List Bool) (b : Bool) (T : ℕ)
    (hD : D.ComputesInTime x [b] T) :
    ∃ a ≤ 2 * T + 5, ∃ (tapes : Fin D.k → ℤ → Option Bool) (heads : Fin D.k → ℤ),
      (f2_timedCondTM D M₁ M₂).tm.runFrom ((f2_timedCondTM D M₁ M₂).tm.initCfg x) a =
        f2_timedBranchCfg D M₁ M₂ ((branchTM M₁ M₂ b).tm.initCfg x) tapes heads b := by
  classical
  have hh : ∃ t, (D.tm.runFrom (D.tm.initCfg x) t).state = none :=
    ⟨T, ((computesInTime_iff _ _ _ _).mp hD).1⟩
  let t := Nat.find hh
  let c := D.tm.runFrom (D.tm.initCfg x) t
  have ht : t ≤ T := Nat.find_min' hh ((computesInTime_iff _ _ _ _).mp hD).1
  have hs : c.state = none := Nat.find_spec hh
  have hc : D.ComputesInTime x c.output t := (computesInTime_iff _ _ _ _).mpr ⟨hs, rfl⟩
  have ho : c.output = [b] := hc.output_unique hD
  have hcap : (f2_timedCondTM D M₁ M₂).tm.runFrom ((f2_timedCondTM D M₁ M₂).tm.initCfg x) t =
      f2_timedControlCfg D M₁ M₂ c := by
    rw [f2_timed_control_init]
    exact f2_timed_capture D M₁ M₂ _ t (fun s hst => Nat.find_min hh hst)
  obtain ⟨r, hrle, hr⟩ := timed_rewind (f2_timedCondTM D M₁ M₂).tm
    (.inr (.inr (.inl (b, false)))) (.inr (.inr (.inl (b, true))))
    (some (.inr (.inr (.inr (branchTM M₁ M₂ b).tm.q₀))))
    (fun _ _ => rfl) (fun inp _ => by cases inp <;> rfl)
    (f2_timedReadyCfg D M₁ M₂ c b) rfl
  refine ⟨t + 2 + r, ?_, c.workTapes, c.workTapePos, ?_⟩
  · have hp : c.inputPos.val ≤ 1 + t := by
      simpa only [MultiTapeTM.initCfg, Cfg.init, Fin.val_one] using
        MultiTapeTM.timed_input_bound (tm := D.tm) (D.tm.initCfg x) t
    change r ≤ c.inputPos.val + 2 at hrle
    omega
  · rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add, hcap,
      f2_timed_read D M₁ M₂ c b hs ho, hr]
    rfl

private lemma f2_cond_time {D M₁ M₂ : FinTM Bool} {p : List Bool → Bool}
    {f₁ f₂ : List Bool → List Bool} {T₀ T₁ T₂ : ℕ → ℕ}
    (hD : D.ComputesFunInTime (fun x => [p x]) T₀)
    (h₁ : M₁.ComputesFunInTime f₁ T₁) (h₂ : M₂.ComputesFunInTime f₂ T₂) :
    (f2_timedCondTM D M₁ M₂).ComputesFunInTime
      (fun x => if p x then f₁ x else f₂ x)
      (fun n => 5 * (T₀ n + max (T₁ n) (T₂ n) + 1)) := by
  intro x
  let B := max (T₁ x.length) (T₂ x.length)
  have hb : (branchTM M₁ M₂ (p x)).ComputesInTime x
      (if p x then f₁ x else f₂ x) B := by
    apply (branchTM_computes M₁ M₂ (p x) x _ B).mpr
    cases hp : p x with
    | false => exact (h₂ x).mono (Nat.le_max_right _ _)
    | true => exact (h₁ x).mono (Nat.le_max_left _ _)
  obtain ⟨a, ha, tapes, heads, hstart⟩ :=
    f2_timed_start D M₁ M₂ x (p x) (T₀ x.length) (hD x)
  have hc : (f2_timedCondTM D M₁ M₂).ComputesInTime x
      (if p x then f₁ x else f₂ x) (a + B) := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_add, hstart, f2_timed_branch_run]
    obtain ⟨hs, ho⟩ := (computesInTime_iff _ _ _ _).mp hb
    exact ⟨by simpa only [f2_timedBranchCfg, leftCfg, rightCfg, Option.map_eq_none_iff] using hs, ho⟩
  -- The controller prefix and selected branch fit one uniform coefficient.
  apply hc.mono
  dsimp only [B] at *
  omega

/-- A native input rewind keeps every work head fixed at every prefix,
including its dispatch step. -/
private lemma f2_rewind_scan_heads {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (scan : S) (dest : Option S)
    (htr : ∀ inp work, tm.tr scan inp work = match inp with
      | some _ => controlAction .neg (some scan)
      | none => controlAction .pos dest) :
    ∀ (j : ℕ) (cfg : Cfg k Bool S x), cfg.state = some scan →
      cfg.inputPos.val = j → j ≤ x.length →
      ∀ u ≤ j + 1, (tm.runFrom cfg u).workTapePos = cfg.workTapePos := by
  intro j
  induction j with
  | zero =>
    intro cfg hs hj hp u hu
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hu with rfl | rfl
    · rfl
    · have hz : cfg.inputPos = 0 := Fin.ext hj
      have hi : cfg.inputSymbol = none := by simp [Cfg.inputSymbol, hz]
      change (tm.step cfg).workTapePos = _
      simp only [MultiTapeTM.step, hs, htr, hi, controlAction_apply]
  | succ j ih =>
    intro cfg hs hj hp u hu
    cases u with
    | zero => rfl
    | succ u =>
      have hi : cfg.inputSymbol = some (x[j]'(by omega)) :=
        inputSymbolInner j (by omega) (by omega)
      have he : tm.step cfg =
          {cfg with state := some scan, inputPos := moveInputPos cfg.inputPos .neg} := by
        simp only [MultiTapeTM.step, hs, htr, hi, controlAction_apply]
      rw [MultiTapeTM.runFrom_succ_eq_step, he]
      apply ih _ rfl _ (by omega) u (by omega)
      simp only [moveInputPos_neg_val]
      omega

/-- The bounded rewind with the prefix work-head equality retained. -/
private lemma f2_rewind_heads {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (start scan : S) (dest : Option S)
    (hstart : ∀ inp work, tm.tr start inp work = controlAction .neg (some scan))
    (hscan : ∀ inp work, tm.tr scan inp work = match inp with
      | some _ => controlAction .neg (some scan)
      | none => controlAction .pos dest)
    (c : Cfg k Bool S x) (hs : c.state = some start) :
    ∃ r ≤ c.inputPos.val + 2,
      tm.runFrom c r = {c with state := dest, inputPos := 1} ∧
      ∀ u ≤ r, (tm.runFrom c u).workTapePos = c.workTapePos := by
  have hstep : tm.step c =
      {c with state := some scan, inputPos := moveInputPos c.inputPos .neg} := by
    simp only [MultiTapeTM.step, hs, hstart, controlAction_apply]
  have hp : (moveInputPos c.inputPos .neg).val ≤ x.length := by
    rw [moveInputPos_neg_val]
    have := c.inputPos.isLt
    omega
  refine ⟨1 + ((moveInputPos c.inputPos .neg).val + 1), ?_, ?_, ?_⟩
  · rw [moveInputPos_neg_val]; omega
  · rw [MultiTapeTM.runFrom_add]
    change tm.runFrom (tm.step c) _ = _
    rw [hstep, rewind_scan tm scan dest hscan _ rfl hp]
  · intro u hu
    cases u with
    | zero => rfl
    | succ u =>
      rw [MultiTapeTM.runFrom_succ_eq_step, hstep]
      exact f2_rewind_scan_heads tm scan dest hscan (moveInputPos c.inputPos .neg).val _ rfl rfl hp u (by omega)

/-- Explicit equivalence between a disjoint pair of banks and their concatenation. -/
private def f2_finSumEquiv (a b : ℕ) : Fin a ⊕ Fin b ≃ Fin (a + b) where
  toFun := Sum.elim (Fin.castAdd b) (Fin.natAdd a)
  invFun := fun i => if h : (i : ℕ) < a then Sum.inl ⟨i, h⟩
    else Sum.inr ⟨i - a, by have := i.isLt; omega⟩
  left_inv := by
    intro i
    cases i with
    | inl i => simp [i.isLt]
    | inr i =>
      simp only [Sum.elim_inr, Fin.coe_natAdd, not_lt.mpr (Nat.le_add_right _ _), ↓reduceDIte]
      congr 1
      apply Fin.ext
      simp
  right_inv := by
    intro i
    dsimp only
    split
    · rfl
    · apply Fin.ext
      dsimp only [Sum.elim_inr, Fin.coe_natAdd]
      omega

/-- Sum a finite tape bank by its two disjoint blocks. -/
private lemma f2_sum_add {a b : ℕ} (f : Fin (a + b) → ℕ) :
    (∑ i : Fin (a + b), f i) =
      (∑ i : Fin a, f (Fin.castAdd b i)) + ∑ i : Fin b, f (Fin.natAdd a i) := by
  rw [Fintype.sum_equiv (f2_finSumEquiv a b).symm f (fun i => f ((f2_finSumEquiv a b).toFun i))]
  · exact Finset.sum_disjSum Finset.univ Finset.univ _
  · intro x
    simp only [Equiv.toFun_as_coe, Equiv.apply_symm_apply]

/-- Disjoint branch banks give exact selected-space plus idle origins. -/
private lemma f2_branch_space (M₁ M₂ : FinTM Bool) (b : Bool) (x : List Bool) (t : ℕ) :
    (branchTM M₁ M₂ b).tm.spaceUsed ((branchTM M₁ M₂ b).tm.initCfg x) t =
      if b then M₁.tm.spaceUsed (M₁.tm.initCfg x) t + M₂.k
      else M₂.tm.spaceUsed (M₂.tm.initCfg x) t + M₁.k := by
  cases b with
  | false =>
    have hi : (branchTM M₁ M₂ false).tm.initCfg x =
        rightCfg Sum.inr (M₂.tm.initCfg x) (fun (_ : Fin M₁.k) _ => none) (fun _ => 0) := by
      refine Cfg.ext rfl rfl ?_ ?_ rfl
      · funext i; refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [rightCfg]
      · funext i; refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [rightCfg]
    have hr (u : ℕ) := rightCfg_run M₂.tm (branchTM M₁ M₂ false).tm Sum.inr
      (fun _ _ _ => rfl) (M₂.tm.initCfg x) (fun (_ : Fin M₁.k) _ => none) (fun _ => 0) u
    simp only [Bool.false_eq_true, ↓reduceIte, MultiTapeTM.spaceUsed]
    change (∑ i : Fin (M₁.k + M₂.k),
      (branchTM M₁ M₂ false).tm.spaceUsedByTape ((branchTM M₁ M₂ false).tm.initCfg x) t i) = _
    rw [f2_sum_add (a := M₁.k) (b := M₂.k)]
    simp only [MultiTapeTM.spaceUsedByTape, MultiTapeTM.visitedByTapeHead]
    simp only [hi]
    simp only [hr]
    simp only [rightCfg, Fin.addCases_left, Fin.addCases_right]
    simp [Finset.image_const Finset.nonempty_range_add_one, Nat.add_comm]
  | true =>
    have hi : (branchTM M₁ M₂ true).tm.initCfg x =
        leftCfg Sum.inl (M₁.tm.initCfg x) (fun (_ : Fin M₂.k) _ => none) (fun _ => 0) := by
      refine Cfg.ext rfl rfl ?_ ?_ rfl
      · funext i; refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [leftCfg]
      · funext i; refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [leftCfg]
    have hr (u : ℕ) := leftCfg_run M₁.tm (branchTM M₁ M₂ true).tm Sum.inl
      (fun _ _ _ => rfl) (M₁.tm.initCfg x) (fun (_ : Fin M₂.k) _ => none) (fun _ => 0) u
    simp only [↓reduceIte, MultiTapeTM.spaceUsed]
    change (∑ i : Fin (M₁.k + M₂.k),
      (branchTM M₁ M₂ true).tm.spaceUsedByTape ((branchTM M₁ M₂ true).tm.initCfg x) t i) = _
    rw [f2_sum_add (a := M₁.k) (b := M₂.k)]
    simp only [MultiTapeTM.spaceUsedByTape, MultiTapeTM.visitedByTapeHead]
    simp only [hi]
    simp only [hr]
    simp only [leftCfg, Fin.addCases_left, Fin.addCases_right]
    simp [Finset.image_const Finset.nonempty_range_add_one]

/-- Head layout of the timed controller, with one scalar capture position. -/
private def f2_condHeads (D M₁ M₂ : FinTM Bool) (d : Fin D.k → ℤ)
    (b : Fin (M₁.k + M₂.k) → ℤ) (z : ℤ) :
    Fin ((D.k + (M₁.k + M₂.k)) + 1) → ℤ :=
  Fin.addCases (Fin.addCases d b) (fun _ => z)

/-- The captured decider has its source positions, idle branches, and a
capture head at its output length. -/
private lemma f2_control_heads (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg D.k Bool D.State x) :
    (f2_timedControlCfg D M₁ M₂ c).workTapePos =
      f2_condHeads D M₁ M₂ c.workTapePos (fun _ => 0) c.output.length := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [f2_timedControlCfg, captureCfg, leftCfg, f2_condHeads, j.isLt]
  · simp [f2_timedControlCfg, captureCfg, leftCfg, f2_condHeads]

/-- A dispatched branch keeps the completed decider's heads and the
capture head fixed while simulating precisely its selected bank. -/
private lemma f2_branch_heads (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg (M₁.k + M₂.k) Bool (M₁.State ⊕ M₂.State) x)
    (tapes : Fin D.k → ℤ → Option Bool) (heads : Fin D.k → ℤ) (b : Bool) :
    (f2_timedBranchCfg D M₁ M₂ c tapes heads b).workTapePos =
      f2_condHeads D M₁ M₂ heads c.workTapePos 0 := rfl

/-- The mandatory back/read pair preserves both machine banks and moves
only the singleton capture head from one to zero. -/
private lemma f2_read_heads (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg D.k Bool D.State x) (b : Bool) (hs : c.state = none) (ho : c.output = [b]) :
    ∀ u ≤ 2, ∃ z : ℤ, 0 ≤ z ∧ z ≤ 1 ∧
      ((f2_timedCondTM D M₁ M₂).tm.runFrom (f2_timedControlCfg D M₁ M₂ c) u).workTapePos =
        f2_condHeads D M₁ M₂ c.workTapePos (fun _ => 0) z := by
  intro u hu
  have hu : u = 0 ∨ u = 1 ∨ u = 2 := by omega
  rcases hu with rfl | rfl | rfl
  · refine ⟨1, by omega, by omega, ?_⟩
    simpa [ho] using f2_control_heads D M₁ M₂ c
  · refine ⟨0, by omega, by omega, ?_⟩
    have hstate : (f2_timedControlCfg D M₁ M₂ c).state = some (.inr (.inl false)) := by
      simp [f2_timedControlCfg, captureCfg, leftCfg, hs]
    change ((f2_timedCondTM D M₁ M₂).tm.step (f2_timedControlCfg D M₁ M₂ c)).workTapePos = _
    simp only [MultiTapeTM.step, hstate]
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [f2_timedCondTM, Action.apply, f2_control_heads, f2_condHeads, j.isLt]
    · simp [f2_timedCondTM, Action.apply, f2_control_heads, f2_condHeads, ho]
  · refine ⟨0, by omega, by omega, ?_⟩
    rw [f2_timed_read D M₁ M₂ c b hs ho]
    rfl

/-- The whole timed conditional has two unchanged source trajectories:
a decider prefix, then a branch prefix. The administrative stages repeat
endpoints; only the capture head has positions zero or one. -/
private lemma f2_cond_ledger (D M₁ M₂ : FinTM Bool) (x : List Bool) (b : Bool) (T : ℕ)
    (hD : D.ComputesInTime x [b] T) :
    ∀ u, ∃ v ≤ T, ∃ w ≤ u, ∃ z : ℤ, 0 ≤ z ∧ z ≤ 1 ∧
      ((f2_timedCondTM D M₁ M₂).tm.runFrom ((f2_timedCondTM D M₁ M₂).tm.initCfg x) u).workTapePos =
        f2_condHeads D M₁ M₂ (D.tm.runFrom (D.tm.initCfg x) v).workTapePos
          ((branchTM M₁ M₂ b).tm.runFrom ((branchTM M₁ M₂ b).tm.initCfg x) w).workTapePos z := by
  classical
  have hh : ∃ t, (D.tm.runFrom (D.tm.initCfg x) t).state = none :=
    ⟨T, ((computesInTime_iff _ _ _ _).mp hD).1⟩
  let d := Nat.find hh
  let c := D.tm.runFrom (D.tm.initCfg x) d
  have hd : d ≤ T := Nat.find_min' hh ((computesInTime_iff _ _ _ _).mp hD).1
  have hs : c.state = none := Nat.find_spec hh
  have hc : D.ComputesInTime x c.output d := (computesInTime_iff _ _ _ _).mpr ⟨hs, rfl⟩
  have ho : c.output = [b] := hc.output_unique hD
  have hcap (u : ℕ) (hu : u ≤ d) :
      (f2_timedCondTM D M₁ M₂).tm.runFrom ((f2_timedCondTM D M₁ M₂).tm.initCfg x) u =
        f2_timedControlCfg D M₁ M₂ (D.tm.runFrom (D.tm.initCfg x) u) := by
    rw [f2_timed_control_init]
    exact f2_timed_capture D M₁ M₂ _ u (fun s hsu => Nat.find_min hh (by omega))
  obtain ⟨r, hrle, hr, hrheads⟩ := f2_rewind_heads (f2_timedCondTM D M₁ M₂).tm
    (.inr (.inr (.inl (b, false)))) (.inr (.inr (.inl (b, true))))
    (some (.inr (.inr (.inr (branchTM M₁ M₂ b).tm.q₀))))
    (fun _ _ => rfl) (fun inp _ => by cases inp <;> rfl)
    (f2_timedReadyCfg D M₁ M₂ c b) rfl
  have hstart : (f2_timedCondTM D M₁ M₂).tm.runFrom
      ((f2_timedCondTM D M₁ M₂).tm.initCfg x) (d + 2 + r) =
      f2_timedBranchCfg D M₁ M₂ ((branchTM M₁ M₂ b).tm.initCfg x)
        c.workTapes c.workTapePos b := by
    rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add, hcap d (le_refl _),
      f2_timed_read D M₁ M₂ c b hs ho, hr]
    rfl
  intro u
  by_cases hu : u ≤ d
  · refine ⟨u, hu.trans hd, 0, Nat.zero_le _,
      (D.tm.runFrom (D.tm.initCfg x) u).output.length, by omega, ?_, ?_⟩
    · have hp := (D.tm.output_prefix (D.tm.initCfg x) hu).length_le
      change (D.tm.runFrom (D.tm.initCfg x) u).output.length ≤ c.output.length at hp
      rw [ho] at hp
      simp only [List.length_singleton] at hp
      exact_mod_cast hp
    · rw [hcap u hu, f2_control_heads]
      rfl
  · refine ⟨d, hd, ?_⟩
    by_cases hread : u ≤ d + 2
    · obtain ⟨z, hz0, hz1, he⟩ := f2_read_heads D M₁ M₂ c b hs ho (u - d) (by omega)
      refine ⟨0, Nat.zero_le _, z, hz0, hz1, ?_⟩
      rw [show u = d + (u - d) by omega, MultiTapeTM.runFrom_add, hcap d (le_refl _)]
      exact he
    · by_cases hrew : u ≤ d + 2 + r
      · refine ⟨0, Nat.zero_le _, 0, by omega, by omega, ?_⟩
        rw [show u = d + 2 + (u - (d + 2)) by omega, MultiTapeTM.runFrom_add,
          MultiTapeTM.runFrom_add, hcap d (le_refl _), f2_timed_read D M₁ M₂ c b hs ho,
          hrheads _ (by omega)]
        rfl
      · refine ⟨u - (d + 2 + r), by omega, 0, by omega, by omega, ?_⟩
        rw [show u = d + 2 + r + (u - (d + 2 + r)) by omega,
          MultiTapeTM.runFrom_add, hstart, f2_timed_branch_run, f2_branch_heads]
        simp only [Nat.add_sub_cancel_left]
        rfl

/-- Cardinalities of the disjoint source banks, with the singleton verdict
occupying at most its two head positions. -/
private lemma f2_cond_space (D M₁ M₂ : FinTM Bool) (x : List Bool) (b : Bool) (T t : ℕ)
    (hD : D.ComputesInTime x [b] T) :
    (f2_timedCondTM D M₁ M₂).tm.spaceUsed ((f2_timedCondTM D M₁ M₂).tm.initCfg x) t ≤
      D.tm.spaceUsed (D.tm.initCfg x) T +
        (branchTM M₁ M₂ b).tm.spaceUsed ((branchTM M₁ M₂ b).tm.initCfg x) t + 2 := by
  let M := f2_timedCondTM D M₁ M₂
  let B := branchTM M₁ M₂ b
  have hDcard (i : Fin D.k) :
      M.tm.spaceUsedByTape (M.tm.initCfg x) t ((Fin.castAdd (M₁.k + M₂.k) i).castSucc) ≤
        D.tm.spaceUsedByTape (D.tm.initCfg x) T i := by
    apply Finset.card_le_card
    intro z hz
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨v, hv, w, hw, z, hz0, hz1, he⟩ := f2_cond_ledger D M₁ M₂ x b T hD u
    apply Finset.mem_image.mpr
    refine ⟨v, Finset.mem_range.mpr (by omega), ?_⟩
    change _ = ((f2_timedCondTM D M₁ M₂).tm.runFrom _ u).workTapePos _
    rw [he]
    simp [f2_condHeads, Fin.castSucc]
  have hBcard (i : Fin (M₁.k + M₂.k)) :
      M.tm.spaceUsedByTape (M.tm.initCfg x) t ((Fin.natAdd D.k i).castSucc) ≤
        B.tm.spaceUsedByTape (B.tm.initCfg x) t i := by
    apply Finset.card_le_card
    intro z hz
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨v, hv, w, hw, z, hz0, hz1, he⟩ := f2_cond_ledger D M₁ M₂ x b T hD u
    apply Finset.mem_image.mpr
    refine ⟨w, Finset.mem_range.mpr (by have := Finset.mem_range.mp hu; omega), ?_⟩
    change _ = ((f2_timedCondTM D M₁ M₂).tm.runFrom _ u).workTapePos _
    rw [he]
    simp [f2_condHeads, Fin.castSucc, B]
  have hcap : M.tm.spaceUsedByTape (M.tm.initCfg x) t (Fin.last _) ≤ 2 := by
    have hsub : M.tm.visitedByTapeHead (M.tm.initCfg x) t (Fin.last _) ⊆ Finset.Icc (0 : ℤ) 1 := by
      intro z hz
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨v, hv, w, hw, z, hz0, hz1, he⟩ := f2_cond_ledger D M₁ M₂ x b T hD u
      change ((f2_timedCondTM D M₁ M₂).tm.runFrom _ u).workTapePos _ ∈ _
      rw [he]
      simpa [f2_condHeads, Fin.last, Fin.addCases] using Finset.mem_Icc.mpr ⟨hz0, hz1⟩
    exact (Finset.card_le_card hsub).trans (by decide)
  change (∑ i : Fin ((D.k + (M₁.k + M₂.k)) + 1), M.tm.spaceUsedByTape (M.tm.initCfg x) t i) ≤ _
  rw [f2_sum_add, f2_sum_add]
  simp only [Fintype.sum_unique]
  exact Nat.add_le_add (Nat.add_le_add
    (Finset.sum_le_sum (fun i _ => hDcard i))
    (Finset.sum_le_sum (fun i _ => hBcard i))) hcap

/-- **W3 space row** (spec, fill pending — design §12 R3, decision 12.3;
annotates `Turing.FinTM.computesFunInTime_cond`). Given space bounds for
the decider and both branches, the conditional controller's space is the
decider's plus the selected branch's **max** — the unselected branch's
bank is idle (origin singletons) — plus a machine constant for the
capture tape and the idle banks' origin cells.

**Proof sketch.** The controller's tape banks are disjoint: the decider
bank is only touched in the capture phase (bounded by `sD` through the
W1 lockstep), the selected branch bank only after dispatch (bounded by
its own hypothesis on the same input `x` — no monotonicity needed), the
unselected bank and the capture tape contribute one cell per tape plus
the singleton verdict; sum the three groups. -/
theorem computesFunInTime_cond_spaceUsed {D M₁ M₂ : FinTM Bool}
    {p : List Bool → Bool} {f₁ f₂ : List Bool → List Bool}
    {T₀ T₁ T₂ : ℕ → ℕ} (sD s₁ s₂ : ℕ → ℕ)
    (hD : D.ComputesFunInTime (fun x => [p x]) T₀)
    (h₁ : M₁.ComputesFunInTime f₁ T₁) (h₂ : M₂.ComputesFunInTime f₂ T₂)
    (hsD : ∀ (x : List Bool) (t : ℕ),
      D.tm.spaceUsed (D.tm.initCfg x) t ≤ sD x.length)
    (hs₁ : ∀ (x : List Bool) (t : ℕ),
      M₁.tm.spaceUsed (M₁.tm.initCfg x) t ≤ s₁ x.length)
    (hs₂ : ∀ (x : List Bool) (t : ℕ),
      M₂.tm.spaceUsed (M₂.tm.initCfg x) t ≤ s₂ x.length) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => if p x then f₁ x else f₂ x)
        (fun n => c * (T₀ n + max (T₁ n) (T₂ n) + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t
          ≤ sD x.length + max (s₁ x.length) (s₂ x.length) + c := by
  refine ⟨f2_timedCondTM D M₁ M₂, 7 + M₁.k + M₂.k, ?_, ?_⟩
  · intro x
    exact (f2_cond_time hD h₁ h₂ x).mono (Nat.mul_le_mul_right _ (by omega))
  · intro x t
    have h := f2_cond_space D M₁ M₂ x (p x) (T₀ x.length) t (hD x)
    rw [f2_branch_space] at h
    have hd := hsD x (T₀ x.length)
    have h1 := hs₁ x t
    have h2 := hs₂ x t
    have hm1 := Nat.le_max_left (s₁ x.length) (s₂ x.length)
    have hm2 := Nat.le_max_right (s₁ x.length) (s₂ x.length)
    split at h <;> omega

/-- A unit-step head starting at zero visits every integer between zero and
its endpoint. Thus a bound on total visited space bounds its displacement.
**Proof sketch.** Induct on time to put the intervening integer interval in
the visited set: a unit step adds at most its new endpoint. Take interval
cardinalities and use the inclusion of this tape's space in total space. -/
private lemma a2_source_radius {k : ℕ} {Q : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool Q) (c : Cfg k Bool Q x) (t B : ℕ)
    (hc : ∀ i, c.workTapePos i = 0) (hb : tm.spaceUsed c t ≤ B) (i : Fin k) :
    -(B : ℤ) ≤ (tm.runFrom c t).workTapePos i ∧
      (tm.runFrom c t).workTapePos i ≤ B := by
  have hinter (u : ℕ) : Finset.Icc (min 0 ((tm.runFrom c u).workTapePos i))
      (max 0 ((tm.runFrom c u).workTapePos i)) ⊆ tm.visitedByTapeHead c u i := by
    induction u with
    | zero =>
      intro z hz
      simp only [MultiTapeTM.runFrom_zero, hc, min_self, max_self,
        Finset.mem_Icc] at hz
      have hz0 : z = 0 := by omega
      subst z
      exact Finset.mem_image.mpr ⟨0, by simp, by simpa using hc i⟩
    | succ u ih =>
      intro z hz
      have hd := tm.workTapePos_step_le (tm.runFrom c u) i
      rw [abs_le] at hd
      rw [← MultiTapeTM.runFrom_succ_eq_step'] at hd
      by_cases hp : z ∈ Finset.Icc (min 0 ((tm.runFrom c u).workTapePos i))
          (max 0 ((tm.runFrom c u).workTapePos i))
      · obtain ⟨v, hv, he⟩ := Finset.mem_image.mp (ih hp)
        exact Finset.mem_image.mpr ⟨v, Finset.mem_range.mpr
          (by have := Finset.mem_range.mp hv; omega), he⟩
      · simp only [Finset.mem_Icc] at hz hp
        have he : (tm.runFrom c (u + 1)).workTapePos i = z := by omega
        exact Finset.mem_image.mpr ⟨u + 1, by simp, he⟩
  have hcard := Finset.card_le_card (hinter t)
  rw [Int.card_Icc] at hcard
  have htotal := tm.spaceUsedByTape_le_spaceUsed c t i
  change (tm.visitedByTapeHead c t i).card ≤ tm.spaceUsed c t at htotal
  omega

/-- All physical heads lie in one fixed origin-centred integer interval. -/
private def a2_heads {k : ℕ} {Q : Type} {x : List Bool}
    (c : Cfg k Bool Q x) (B : ℕ) : Prop :=
  ∀ i, -(B : ℤ) ≤ c.workTapePos i ∧ c.workTapePos i ≤ B

/-- Enlarging the common interval preserves a head bound. -/
private lemma a2_heads_mono {k : ℕ} {Q : Type} {x : List Bool}
    {c : Cfg k Bool Q x} {A B : ℕ} (h : a2_heads c A) (hle : A ≤ B) :
    a2_heads c B := by
  intro i
  have := h i
  constructor <;> omega

/-- A short administrative segment enlarges its starting interval by at
most its duration, including every intermediate work-head position. -/
private lemma a2_heads_steps {k : ℕ} {Q : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool Q) (c : Cfg k Bool Q x) (A B t : ℕ)
    (h : a2_heads c A) (ht : t ≤ B) : a2_heads (tm.runFrom c t) (A + B) := by
  intro i
  have hs := h i
  have hm := f2_head_steps tm c t i
  constructor <;> omega

/-- Concatenating two bounded traces reuses their common interval. -/
private lemma a2_heads_join {k : ℕ} {Q : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool Q) (c : Cfg k Bool Q x) (a b B : ℕ)
    (ha : ∀ u ≤ a, a2_heads (tm.runFrom c u) B)
    (hb : ∀ u ≤ b, a2_heads (tm.runFrom (tm.runFrom c a) u) B) :
    ∀ u ≤ a + b, a2_heads (tm.runFrom c u) B := by
  intro u hu
  by_cases h : u ≤ a
  · exact ha u h
  · rw [show u = a + (u - a) by omega, MultiTapeTM.runFrom_add]
    exact hb (u - a) (by omega)

/-- After a halting endpoint, every later head is that same endpoint head. -/
private lemma a2_heads_halted {k : ℕ} {Q : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool Q) (c : Cfg k Bool Q x) (a B : ℕ)
    (hh : (tm.runFrom c a).state = none)
    (ha : ∀ u ≤ a, a2_heads (tm.runFrom c u) B) :
    ∀ u, a2_heads (tm.runFrom c u) B := by
  intro u
  by_cases h : u ≤ a
  · exact ha u h
  · rw [show u = a + (u - a) by omega, MultiTapeTM.runFrom_add,
      MultiTapeTM.runFrom_of_halt _ hh]
    exact ha a (le_refl _)

/-- Project a captured body call onto its body, stationary flag, fixed
counter origin, retained fuel bank, and current output-length head. -/
private lemma a2_call_heads (body F : FinTM Bool) (anchor : body.State)
    {x : List Bool} (startup : Bool) (c : Cfg body.k Bool body.State x)
    (release : Bool) (flag : Option Bool) (word : List Bool)
    (fuel : Cfg F.k Bool F.State x) (B : ℕ)
    (hb : a2_heads c B) (hf : a2_heads fuel B) (ho : c.output.length ≤ B) :
    a2_heads (f2_loopCall body F anchor startup c release flag word fuel) B := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [f2_loopCall, captureCfg, Fin.val_last, lt_self_iff_false, ↓reduceDIte,
      f2_loopBodyPadded, leftCfg, f2_loopBodyCfg, List.nil_append]
    constructor <;> omega
  · simp only [f2_loopCall, captureCfg, Fin.coe_castSucc, dif_pos j.isLt]
    change -(B : ℤ) ≤ (f2_loopBodyPadded body F anchor c release flag word fuel).workTapePos j ∧
      (f2_loopBodyPadded body F anchor c release flag word fuel).workTapePos j ≤ B
    simp only [f2_loopBodyPadded, leftCfg]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp only [Fin.addCases_left, f2_loopBodyCfg]
      split
      · exact hb _
      · constructor <;> omega
    · simp only [Fin.addCases_right]
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp only [Fin.addCases_left]; constructor <;> omega
      · simpa only [Fin.addCases_right] using hf j

/-- Fuel capture preserves its source heads, leaves the other banks at
zero, and places its last head at the current fuel output length. -/
private lemma a2_fuel_heads (body F : FinTM Bool) {x : List Bool}
    (c : Cfg F.k Bool F.State x) (B : ℕ)
    (hf : a2_heads c B) (ho : c.output.length ≤ B) :
    a2_heads (f2_loopFuelCaptured body F c) B := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [f2_loopFuelCaptured, captureCfg, Fin.val_last, lt_self_iff_false,
      ↓reduceDIte, f2_loopFuelCfg, rightCfg, List.nil_append]
    constructor <;> omega
  · simp only [f2_loopFuelCaptured, captureCfg, Fin.coe_castSucc, dif_pos j.isLt]
    change -(B : ℤ) ≤ (f2_loopFuelCfg body F c).workTapePos j ∧
      (f2_loopFuelCfg body F c).workTapePos j ≤ B
    simp only [f2_loopFuelCfg, rightCfg]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp only [Fin.addCases_left]; constructor <;> omega
    · simp only [Fin.addCases_right]
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp only [Fin.addCases_left]; constructor <;> omega
      · simpa only [Fin.addCases_right] using hf j

/-- Every prefix of a captured body call is the same prefix of its source,
with the release bit consumed once and the halt flag set on the last action. -/
private lemma a2_call_run (body F : FinTM Bool) (anchor : body.State)
    (findMode startup : Bool) {x : List Bool}
    (c : Cfg body.k Bool body.State x) (release : Bool) (t : ℕ)
    (word : List Bool) (fuel : Cfg F.k Bool F.State x) (hc : c.state ≠ none)
    (hlive : ∀ u < t, (body.tm.runFrom c u).state ≠ none)
    (hanchor : ∀ u < t, (u = 0 ∧ release = true) ∨
      (body.tm.runFrom c u).state ≠ some anchor) :
    (f2_loopHost body F anchor findMode).tm.runFrom
        (f2_loopCall body F anchor startup c release none word fuel) t =
      f2_loopCall body F anchor startup (body.tm.runFrom c t)
        (if t = 0 then release else false)
        (if (body.tm.runFrom c t).state = none then some true else none) word fuel := by
  unfold f2_loopCall f2_loopBodyPadded
  rw [f2_loopHost_body_capture]
  · rw [f2_loopBodySource_run, f2_loopBody_run body anchor c release hc t hlive hanchor]
  · intro u hu
    rw [f2_loopBodySource_run, f2_loopBody_run body anchor c release hc u
      (fun v hv => hlive v (by omega)) (fun v hv => hanchor v (by omega))]
    simpa [Cfg.Halted, leftCfg, f2_loopBodyCfg] using hlive u hu

/-- Budgeted source space bounds all captured-call prefixes. Empty final
output gives no capture growth; a singleton final verdict gives at most one
cell of growth, including a verdict emitted by the halting action. -/
private lemma a2_call_prefix (body F : FinTM Bool) (anchor : body.State)
    (startup : Bool) {x : List Bool}
    (c : Cfg body.k Bool body.State x) (release : Bool) (t B : ℕ)
    (word : List Bool) (fuel : Cfg F.k Bool F.State x) (hc : c.state ≠ none)
    (hzero : ∀ i, c.workTapePos i = 0)
    (hlive : ∀ u < t, (body.tm.runFrom c u).state ≠ none)
    (hanchor : ∀ u < t, (u = 0 ∧ release = true) ∨
      (body.tm.runFrom c u).state ≠ some anchor)
    (hspace : ∀ u ≤ t, body.tm.spaceUsed c u ≤ B)
    (hf : a2_heads fuel B) (hout : (body.tm.runFrom c t).output.length ≤ B) :
    ∀ u ≤ t, a2_heads ((f2_loopHost body F anchor false).tm.runFrom
      (f2_loopCall body F anchor startup c release none word fuel) u) B := by
  intro u hu
  rw [a2_call_run body F anchor false startup c release u word fuel hc
    (fun v hv => hlive v (by omega)) (fun v hv => hanchor v (by omega))]
  exact a2_call_heads body F anchor startup _ _ _ word fuel B
    (a2_source_radius body.tm c u B hzero (hspace u hu)) hf
    (((body.tm.output_prefix c hu).length_le).trans hout)

/-- Fuel capture and installation have a width-bounded space ledger.
The fuel source is charged to its space hypothesis; the three installation
scans cost `3*width+4`, and the possibly long input rewind moves no work head.
**Proof sketch.** Capture to the first halt, project the source heads and
output lengths at every prefix, then concatenate the setup and input-only
rewind traces. Retain the source endpoint's `B` bound for all later calls. -/
private lemma a2_loop_prepare (body F : FinTM Bool) (anchor : body.State)
    (R T S : ℕ → ℕ)
    (hF : F.ComputesFunInTime (fun x => Nat.bits (R x.length)) T)
    (hspace : ∀ x t, F.tm.spaceUsed (F.tm.initCfg x) t ≤ S x.length)
    (x : List Bool) :
    ∃ (c : Cfg F.k Bool F.State x) (t : ℕ),
      c.state = none ∧ c.output = Nat.bits (R x.length) ∧ t ≤ 5 * T x.length + 7 ∧
      (f2_loopHost body F anchor false).tm.runFrom
        ((f2_loopHost body F anchor false).tm.initCfg x) t = f2_loopReady body F c ∧
      a2_heads c (S x.length) ∧
      ∀ u ≤ t, a2_heads ((f2_loopHost body F anchor false).tm.runFrom
        ((f2_loopHost body F anchor false).tm.initCfg x) u)
        (S x.length + 4 * (Nat.bits (R x.length)).length + 4) := by
  obtain ⟨space, hhalt, hout, _⟩ := hF x
  obtain ⟨u, hu, hut, hlive, huh, hue⟩ :=
    f2_loop_first_halt F.tm (F.tm.initCfg x) (T x.length)
      (by simp [MultiTapeTM.initCfg, Cfg.init]) hhalt
  let c := F.tm.runFrom (F.tm.initCfg x) u
  have hc : c.state = none := huh
  have ho : c.output = Nat.bits (R x.length) := by dsimp only [c]; rw [hue]; exact hout
  have hcap (v : ℕ) (hv : v ≤ u) : (f2_loopHost body F anchor false).tm.runFrom
      ((f2_loopHost body F anchor false).tm.initCfg x) v =
        f2_loopFuelCaptured body F (F.tm.runFrom (F.tm.initCfg x) v) := by
    rw [f2_loopHost_init, f2_loopFuel_init, f2_loopHost_fuel_capture]
    · rw [f2_loopFuel_run]; rfl
    · intro w hw
      rw [f2_loopFuel_run]
      simpa [Cfg.Halted, f2_loopFuelCfg, rightCfg] using hlive w (by omega)
  have hs (v : ℕ) : a2_heads (F.tm.runFrom (F.tm.initCfg x) v) (S x.length) :=
    a2_source_radius F.tm (F.tm.initCfg x) v _ (fun _ => rfl) (hspace x v)
  have hpref (v : ℕ) (hv : v ≤ u) : a2_heads
      ((f2_loopHost body F anchor false).tm.runFrom
        ((f2_loopHost body F anchor false).tm.initCfg x) v)
      (S x.length + c.output.length) := by
    rw [hcap v hv]
    apply a2_fuel_heads
    · exact a2_heads_mono (hs v) (by omega)
    · have := (F.tm.output_prefix (F.tm.initCfg x) hv).length_le
      change (F.tm.runFrom (F.tm.initCfg x) v).output.length ≤ c.output.length at this
      omega
  let prepared := f2_loopFrame body F (f2_loopFuelCaptured body F c)
    (some (.inr (.inr 4))) c.inputPos (bufferTape []) (bufferTape c.output)
    (bufferTape []) 0 0 []
  have hsetup : (f2_loopHost body F anchor false).tm.runFrom
      (f2_loopFuelCaptured body F c) (3 * c.output.length + 4) = prepared := by
    conv_lhs => arg 1; rw [f2_loopFuelCaptured_frame body F c hc]
    exact f2_loopHost_fuel_setup body F anchor false _ _ _ _ _
  obtain ⟨v, hv, hrew, hrewheads⟩ := f2_rewind_heads
    (f2_loopHost body F anchor false).tm (.inr (.inr 4)) (.inr (.inr 5))
    (.some (.inr (.inl (true, (body.tm.q₀, false)))))
    (fun _ _ => f2_loopControl_idle body F .neg _)
    (fun inp _ => by cases inp <;> exact f2_loopControl_idle body F _ _) prepared rfl
  have hw : c.output.length ≤ T x.length := by rw [ho]; exact f2_loop_fuel_width F R T hF x
  have hi : c.inputPos.val ≤ 1 + u := f2_loop_input_run_le F.tm (F.tm.initCfg x) u
  have hinstall (w : ℕ) (hw : w ≤ 3 * c.output.length + 4) :
      a2_heads ((f2_loopHost body F anchor false).tm.runFrom
        (f2_loopFuelCaptured body F c) w) (S x.length + 4 * c.output.length + 4) := by
    have hb := hpref u (le_refl _)
    rw [hcap u (le_refl _)] at hb
    have hh := a2_heads_steps (f2_loopHost body F anchor false).tm
      (f2_loopFuelCaptured body F c) _ (3 * c.output.length + 4) w hb hw
    convert hh using 1 <;> omega
  refine ⟨c, u + (3 * c.output.length + 4) + v, hc, ho, ?_, ?_, hs u, ?_⟩
  · change v ≤ c.inputPos.val + 2 at hv
    omega
  · rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add,
      hcap u (le_refl _), hsetup, hrew]
    rfl
  · rw [← ho]
    apply a2_heads_join
    · apply a2_heads_join
      · intro w hw
        exact a2_heads_mono (hpref w hw) (by omega)
      · rw [hcap u (le_refl _)]
        exact hinstall
    · rw [MultiTapeTM.runFrom_add, hcap u (le_refl _), hsetup]
      intro w hw i
      rw [hrewheads w hw]
      have hh := hinstall (3 * c.output.length + 4) (le_refl _)
      rw [hsetup] at hh
      exact hh i

/-- Startup uses its space hypothesis only up to the supplied first anchor;
the silent stop and release add two bounded administrative steps. -/
private lemma a2_loop_start_prefix (body F : FinTM Bool) (anchor : body.State)
    {x : List Bool} (s : List Bool) (t B : ℕ) (fuel : Cfg F.k Bool F.State x)
    (hguard : ∀ u < t, (body.tm.runFrom (body.tm.initCfg x) u).state ≠ some anchor)
    (hend : body.tm.runFrom (body.tm.initCfg x) t = Cfg.ofWords anchor (stateWord body.k s))
    (hs : ∀ u ≤ t, body.tm.spaceUsed (body.tm.initCfg x) u ≤ B)
    (hf : a2_heads fuel B) :
    ∀ u ≤ t + 2, a2_heads ((f2_loopHost body F anchor false).tm.runFrom
      (f2_loopReady body F fuel) u) (B + 2) := by
  rw [f2_loopReady_call body F anchor]
  have hl := f2_loop_live_prefix body.tm (body.tm.initCfg x) t
    (by rw [hend]; simp [Cfg.ofWords])
  have hp := a2_call_prefix body F anchor true (body.tm.initCfg x) false t B
    fuel.output fuel (by simp [MultiTapeTM.initCfg, Cfg.init]) (fun _ => rfl)
    (fun u hu => hl u (by omega)) (fun u hu => Or.inr (hguard u hu)) hs hf
    (by rw [hend]; simp [Cfg.ofWords])
  apply a2_heads_join
  · intro u hu
    exact a2_heads_mono (hp u hu) (by omega)
  · intro u hu
    exact a2_heads_steps _ _ B 2 u (hp t (le_refl _)) hu

/-- A decision round has a single fixed space interval, independent of its
index. The source bank uses the budgeted source hypothesis, the retained
fuel bank starts within the same bound, and debit administration is charged
only to the unchanged counter width.
**Proof sketch.** At acceptance use the actual first halt; append-only output
bounds capture by one. At rejection the source endpoint is silent and has
origin heads. The stop plus the received borrow/rewind/underflow segment
costs at most `2*width+5`. Concatenate prefix bounds, including both endings. -/
private lemma a2_loop_round (body F : FinTM Bool) (anchor : body.State)
    {x : List Bool} (s next : List Bool) (accepted : Bool)
    (word : List Bool) (fuel : Cfg F.k Bool F.State x) (t B : ℕ) (ht : 0 < t)
    (hanchor : ∀ u, 0 < u → u < t →
      (body.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord body.k s)) u).state ≠ some anchor)
    (hend : if accepted then
      (body.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).state = none ∧
      (body.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).output = [true]
      else body.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t =
        Cfg.ofWords anchor (stateWord body.k next))
    (hspace : ∀ u ≤ t, body.tm.spaceUsed
      (Cfg.ofWords (input := x) anchor (stateWord body.k s)) u ≤ B)
    (hf : a2_heads fuel B) :
    ∃ v,
      (∀ u ≤ v, a2_heads ((f2_loopHost body F anchor false).tm.runFrom
        (f2_loopCall body F anchor false (Cfg.ofWords anchor (stateWord body.k s))
          true none word fuel) u) (B + 2 * word.length + 6)) ∧
      ((f2_loopHost body F anchor false).tm.runFrom
        (f2_loopCall body F anchor false (Cfg.ofWords anchor (stateWord body.k s))
          true none word fuel) v).state = none ∨
      ∃ v, (f2_loopDebit word).2 = true ∧
        (∀ u ≤ v, a2_heads ((f2_loopHost body F anchor false).tm.runFrom
          (f2_loopCall body F anchor false (Cfg.ofWords anchor (stateWord body.k s))
            true none word fuel) u) (B + 2 * word.length + 6)) ∧
        (f2_loopHost body F anchor false).tm.runFrom
          (f2_loopCall body F anchor false (Cfg.ofWords anchor (stateWord body.k s))
            true none word fuel) v =
          f2_loopCall body F anchor false (Cfg.ofWords anchor (stateWord body.k next))
            true none (f2_loopDebit word).1 fuel := by
  let start := Cfg.ofWords (input := x) anchor (stateWord body.k s)
  have hzero (i) : start.workTapePos i = 0 := rfl
  have hc : start.state ≠ none := by simp [start, Cfg.ofWords]
  have hg : ∀ u < t, (u = 0 ∧ true = true) ∨ (body.tm.runFrom start u).state ≠ some anchor := by
    intro u hu
    by_cases hz : u = 0
    · exact Or.inl ⟨hz, rfl⟩
    · exact Or.inr (hanchor u (by omega) hu)
  by_cases ha : accepted = true
  · simp only [ha, if_true] at hend
    obtain ⟨u, hu, hut, hlive, hhalt, he⟩ := f2_loop_first_halt body.tm start t hc hend.1
    have hcap := f2_loopHost_halt_return body F anchor false start u word fuel hu hlive
      (fun v hv hvu => hanchor v hv (by omega)) hhalt
    obtain ⟨v, hv, hstop, _⟩ := f2_loopHost_accept body F anchor false
      (body.tm.runFrom start u) word fuel hhalt
    have ho : (body.tm.runFrom start u).output = [true] := by rw [he]; exact hend.2
    have hv5 : v ≤ 5 := by simpa [ho] using hv
    have hp := a2_call_prefix body F anchor false start true u (B + 1) word fuel hc hzero
      hlive (fun w hw => hg w (by omega))
      (fun w hw => (hspace w (by omega)).trans (by omega))
      (a2_heads_mono hf (by omega)) (by simp [ho])
    refine ⟨u + v, ?_⟩
    left
    constructor
    · apply a2_heads_join
      · intro w hw
        exact a2_heads_mono (hp w hw) (by omega)
      · intro w hw
        exact a2_heads_mono (a2_heads_steps _ _ (B + 1) 5 w
          (hp u (le_refl _)) (by omega)) (by omega)
    · rw [MultiTapeTM.runFrom_add, hcap]
      exact hstop
  · simp only [ha] at hend
    have hl := f2_loop_live_prefix body.tm start t (by rw [hend]; simp [Cfg.ofWords])
    have hp := a2_call_prefix body F anchor false start true t B word fuel hc hzero
      (fun w hw => hl w (by omega)) hg hspace hf (by rw [hend]; simp [Cfg.ofWords])
    have hcap := f2_loopHost_anchor_return body F anchor false false start true t word fuel
      (by rw [hend]; rfl) (by intro hz; omega) hg
    rw [show body.tm.runFrom start t = Cfg.ofWords anchor (stateWord body.k next) from hend] at hcap
    obtain ⟨v, hv, hfinish⟩ := f2_loopHost_reject body F anchor false
      {Cfg.ofWords (input := x) anchor (stateWord body.k next) with state := none}
      word fuel rfl rfl
    have hpall : ∀ u ≤ (t + 1) + v, a2_heads
        ((f2_loopHost body F anchor false).tm.runFrom
          (f2_loopCall body F anchor false start true none word fuel) u)
        (B + 2 * word.length + 6) := by
      rw [show (t + 1) + v = t + (1 + v) by omega]
      apply a2_heads_join
      · intro w hw
        exact a2_heads_mono (hp w hw) (by omega)
      · intro w hw
        exact a2_heads_mono (a2_heads_steps _ _ B (2 * word.length + 5) w
          (hp t (le_refl _)) (by omega)) (by omega)
    refine ⟨(t + 1) + v, ?_⟩
    by_cases hd : (f2_loopDebit word).2 = true
    · right
      refine ⟨(t + 1) + v, hd, hpall, ?_⟩
      rw [MultiTapeTM.runFrom_add, hcap]
      simpa only [hd, if_true] using hfinish
    · left
      refine ⟨hpall, ?_⟩
      rw [MultiTapeTM.runFrom_add, hcap]
      simp only [hd, Bool.false_eq_true, ↓reduceIte] at hfinish
      exact hfinish.1

/-- A finite chain of returning or halting segments reuses one interval.
The last segment must halt; every earlier halt supplies a stationary tail.
The interval is never multiplied by the number of segments. -/
private lemma a2_segments {k : ℕ} {Q : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool Q) (cfg : ℕ → Cfg k Bool Q x) (N B : ℕ)
    (hN : 0 < N)
    (hround : ∀ i < N, ∃ u,
      (∀ v ≤ u, a2_heads (tm.runFrom (cfg i) v) B) ∧
      ((tm.runFrom (cfg i) u).state = none ∨
        i + 1 < N ∧ tm.runFrom (cfg i) u = cfg (i + 1))) :
    ∀ t, a2_heads (tm.runFrom (cfg 0) t) B := by
  induction N generalizing cfg with
  | zero => omega
  | succ N ih =>
    obtain ⟨u, hp, he⟩ := hround 0 (by omega)
    intro t
    by_cases ht : t ≤ u
    · exact hp t ht
    · rw [show t = u + (t - u) by omega, MultiTapeTM.runFrom_add]
      rcases he with hh | ⟨hn, hr⟩
      · rw [MultiTapeTM.runFrom_of_halt _ hh]
        exact hp u (le_refl _)
      · rw [hr]
        exact ih (fun i => cfg (i + 1)) (by omega)
          (fun i hi => by
            obtain ⟨v, hv, he⟩ := hround (i + 1) (by omega)
            refine ⟨v, hv, ?_⟩
            rcases he with hh | ⟨hj, hr⟩
            · exact Or.inl hh
            · exact Or.inr ⟨by omega, hr⟩) (t - u)

/-- Sum the received decision segments, with an already halted false terminal.
**Proof sketch.** Induct on the candidate count; acceptance stops, while a
rejection composes the next segment and shifts the Boolean list test. -/
private lemma a2_loop_halted_run {k : ℕ} {S : Type*} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (cfg : ℕ → Cfg k Bool S x)
    (accept : ℕ → Bool) (B N : ℕ)
    (hend : (cfg N).state = none ∧ (cfg N).output = [false])
    (hround : ∀ j < N, ∃ t ≤ B,
      if accept j then
        (tm.runFrom (cfg j) t).state = none ∧
          (tm.runFrom (cfg j) t).output = [true]
      else tm.runFrom (cfg j) t = cfg (j + 1)) :
    ∃ t ≤ N * B, (tm.runFrom (cfg 0) t).state = none ∧
      (tm.runFrom (cfg 0) t).output = [(List.range N).any accept] := by
  induction N generalizing cfg accept with
  | zero => exact ⟨0, by simp, by simpa using hend⟩
  | succ N ih =>
    obtain ⟨t, ht, hc⟩ := hround 0 (by omega)
    have hany : (List.range (N + 1)).any accept =
        (accept 0 || (List.range N).any (fun j => accept (j + 1))) := by
      simp [List.range_succ_eq_map, List.any_map, Function.comp_def]
    by_cases hb : accept 0 = true
    · simp only [hb, ↓reduceIte] at hc
      refine ⟨t, ht.trans ?_, hc.1, ?_⟩
      · exact Nat.le_mul_of_pos_left B (by omega)
      · simpa [hany, hb] using hc.2
    · simp only [hb] at hc
      obtain ⟨s, hs, hhalt, hout⟩ := ih
        (fun j => cfg (j + 1)) (fun j => accept (j + 1)) hend
        (fun j hj => hround (j + 1) (by omega))
      refine ⟨t + s, ?_, ?_, ?_⟩
      · rw [Nat.succ_mul]; omega
      · rw [MultiTapeTM.runFrom_add, hc]; exact hhalt
      · rw [MultiTapeTM.runFrom_add, hc]
        simpa [hany, hb] using hout

/-- **L space row** (spec, fill pending — design §12 R3, decision 12.3;
annotates `Turing.FinTM.exists_loopTM`; the `exists_loopCfgTM` and
`exists_loopFindTM` siblings inherit the same host at fill time). Same
hypotheses as the decision loop, plus space bounds for the fuel machine
and for the body — from its initial configuration and from every
admissible seam, within the round budget. Conclusion: the loop host also
runs within a constant multiple of `S n + T n + 1` work-tape cells. The
key point is that space does **not** scale with the round count `R`:
rounds restart from seams with heads at the origin, so their footprints
overlap instead of accumulating.

**Proof sketch.** Per tape, each round's visited set is an interval
containing the seam origin (heads move by unit steps from the origin) of
cardinality at most `S n`, so the union over all rounds lies in
`[-(S n), S n]` — at most `2·S n + 1` cells, not `R·S n`. The counter
tape holds the fuel word, of length at most `T n`
(`Turing.MultiTapeTM.output_length_le` on the fuel machine), walked in
place by the debits; the capture tape records one verdict per round and
is rewound with the round, staying within a constant; the fuel machine's
own banks are bounded by `hFspace`. Sum the groups and absorb tape
counts into `c`.  **Scope note (round-1 note R10)**: this row annotates the
decision-loop export (`Turing.exists_loopTM`) only; the configuration- and
result-bearing siblings (`exists_loopCfgTM`, `exists_loopFindTM`) carry no
exported space clause here — same-witness conjunctions for them are a
recorded future addition, commissioned when a consumer needs them, not an
implied theorem. -/
theorem exists_loopTM_spaceUsed (body F : FinTM Bool) (anchor : body.State)
    (Inv : List Bool → List Bool → Prop)
    (stepF : List Bool → List Bool → List Bool)
    (acceptF : List Bool → List Bool → Bool)
    (s0 : List Bool → List Bool) (R T S : ℕ → ℕ)
    (hF : F.ComputesFunInTime (fun x => Nat.bits (R x.length)) T)
    (hInv0 : ∀ x : List Bool, Inv x (s0 x))
    (hInvStep : ∀ (x s : List Bool), Inv x s → Inv x (stepF x s))
    (hstart : ∀ x : List Bool, ∃ t ≤ T x.length,
      (∀ t' < t,
        (body.tm.runFrom (body.tm.initCfg x) t').state ≠ some anchor) ∧
      body.tm.runFrom (body.tm.initCfg x) t =
        Cfg.ofWords anchor (stateWord body.k (s0 x)))
    (hround : ∀ (x s : List Bool), Inv x s →
      ∃ t, 0 < t ∧ t ≤ T x.length ∧
        (∀ t', 0 < t' → t' < t →
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t').state
              ≠ some anchor) ∧
        if acceptF x s then
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).state
              = none ∧
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).output
              = [true]
        else
          body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t =
              Cfg.ofWords anchor (stateWord body.k (stepF x s)))
    (hFspace : ∀ (x : List Bool) (t : ℕ),
      F.tm.spaceUsed (F.tm.initCfg x) t ≤ S x.length)
    (hstartSpace : ∀ (x : List Bool) (t : ℕ), t ≤ T x.length →
      body.tm.spaceUsed (body.tm.initCfg x) t ≤ S x.length)
    (hroundSpace : ∀ (x s : List Bool), Inv x s →
      ∀ t ≤ T x.length,
        body.tm.spaceUsed
          (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t
            ≤ S x.length) :
    ∃ (E : FinTM Bool) (c : ℕ),
      E.ComputesFunInTime
        (fun x => [(List.range (R x.length + 1)).any
          fun i => acceptF x ((stepF x)^[i] (s0 x))])
        (fun n => c * (T n + 1) * (R n + 2)) ∧
      ∀ (x : List Bool) (t : ℕ),
        E.tm.spaceUsed (E.tm.initCfg x) t
          ≤ c * (S x.length + T x.length + 1) := by
  obtain ⟨c, hc⟩ := f2_loopHost_contracts body F anchor Inv stepF acceptF
    (fun _ _ => [true]) false s0 R T hF hInv0 hInvStep hstart hround
  let E := f2_loopHost body F anchor false
  have htime : E.ComputesFunInTime
      (fun x => [(List.range (R x.length + 1)).any
        fun i => acceptF x ((stepF x)^[i] (s0 x))])
      (fun n => c * (T n + 1) * (R n + 2)) := by
    intro x
    obtain ⟨cfg, startup, hs, hinit, _, hend, hout, hsegments, _, _⟩ := hc x
    obtain ⟨t, ht, hhalt, houtput⟩ := a2_loop_halted_run E.tm cfg
      (fun i => acceptF x ((stepF x)^[i] (s0 x))) (c * (T x.length + 1))
      (R x.length + 1) ⟨hend, by simpa using hout⟩
      (fun j hj => by simpa using hsegments j (by omega))
    have hrun := E.tm.runFrom_add (E.tm.initCfg x) startup t
    rw [hinit] at hrun
    have hcompute : E.ComputesInTime x
        [(List.range (R x.length + 1)).any
          (fun i => acceptF x ((stepF x)^[i] (s0 x)))] (startup + t) := by
      refine ⟨_, ?_, ?_, rfl⟩
      · rw [hrun]; exact hhalt
      · rw [hrun]; exact houtput
    apply hcompute.mono
    calc startup + t ≤ c * (T x.length + 1) +
          (R x.length + 1) * (c * (T x.length + 1)) := Nat.add_le_add hs ht
      _ = c * (T x.length + 1) * (R x.length + 2) := by ring
  refine ⟨E, c + 19 * E.k, ?_, ?_⟩
  · intro x
    exact (htime x).mono (Nat.mul_le_mul_right _
      (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)))
  · intro x t
    -- Fuel: capture has its source's space bound and its actual output width.
    obtain ⟨fuel, ftime, hfh, hfo, hft, hprepare, hfuel, hprepareSpace⟩ :=
      a2_loop_prepare body F anchor R T S hF hFspace x
    obtain ⟨btime, hbt, hbguard, hbend⟩ := hstart x
    let words (i : ℕ) := (fun w => (f2_loopDebit w).1)^[i] (Nat.bits (R x.length))
    let orbit (i : ℕ) := (stepF x)^[i] (s0 x)
    let cfg (i : ℕ) := f2_loopCall body F anchor false
      (Cfg.ofWords (input := x) anchor (stateWord body.k (orbit i))) true none (words i) fuel
    let B := S x.length + 4 * (Nat.bits (R x.length)).length + 8
    have hwidth (i : ℕ) : (words i).length = (Nat.bits (R x.length)).length :=
      f2_loopDebit_iterate_length _ _
    have hsuccess (i : ℕ) (hi : i ≤ R x.length) :
        (f2_loopDebit (words i)).2 = true ↔ i < R x.length := by
      rw [f2_loopDebit_success]
      dsimp only [words]
      rw [f2_loopDebit_iterate_value _ _ hi]
      omega
    -- Every admissible source call starts at zero. Its captured prefixes
    -- are bounded before the common, fixed-width administrative allowance.
    have hlocal : ∀ i < R x.length + 1, ∃ u,
        (∀ v ≤ u, a2_heads (E.tm.runFrom (cfg i) v) B) ∧
        ((E.tm.runFrom (cfg i) u).state = none ∨
          i + 1 < R x.length + 1 ∧ E.tm.runFrom (cfg i) u = cfg (i + 1)) := by
      intro i hi
      have hinv := f2_loop_orbit_inv Inv stepF s0 hInv0 hInvStep x i
      obtain ⟨u, hup, hut, hguard, hend⟩ := hround x (orbit i) hinv
      obtain ⟨v, he⟩ := a2_loop_round body F anchor (orbit i) (stepF x (orbit i))
        (acceptF x (orbit i)) (words i) fuel u (S x.length) hup hguard hend
        (fun w hw => hroundSpace x (orbit i) hinv w (hw.trans hut)) hfuel
      have hbound : S x.length + 2 * (words i).length + 6 ≤ B := by
        rw [hwidth]
        dsimp [B]
        omega
      rcases he with ⟨hp, hh⟩ | ⟨v', hd, hp, he⟩
      · exact ⟨v, fun w hw => a2_heads_mono (hp w hw) hbound, Or.inl hh⟩
      · refine ⟨v', fun w hw => a2_heads_mono (hp w hw) hbound,
          Or.inr ⟨by have := (hsuccess i (by omega)).mp hd; omega, ?_⟩⟩
        simpa only [cfg, words, orbit, Function.iterate_succ_apply'] using he
    have hrounds := a2_segments E.tm cfg (R x.length + 1) B (by omega) hlocal
    -- Startup has no captured output, and its stop/release is two steps.
    have hinit : E.tm.runFrom (E.tm.initCfg x) (ftime + (btime + 2)) = cfg 0 := by
      rw [MultiTapeTM.runFrom_add, hprepare,
        f2_loopHost_start body F anchor false (s0 x) btime fuel hbguard hbend]
      simp only [cfg, words, orbit, Function.iterate_zero_apply, hfo]
    have hstartup : ∀ u ≤ ftime + (btime + 2),
        a2_heads (E.tm.runFrom (E.tm.initCfg x) u) B := by
      apply a2_heads_join
      · intro u hu
        exact a2_heads_mono (hprepareSpace u hu) (by dsimp [B]; omega)
      · rw [hprepare]
        intro u hu
        exact a2_heads_mono (a2_loop_start_prefix body F anchor (s0 x) btime
          (S x.length) fuel hbguard hbend
          (fun v hv => hstartSpace x v (hv.trans hbt)) hfuel u hu)
          (by dsimp [B]; omega)
    -- Reuse the same interval over every round and every halted tail.
    have hall : ∀ u, a2_heads (E.tm.runFrom (E.tm.initCfg x) u) B := by
      intro u
      by_cases hu : u ≤ ftime + (btime + 2)
      · exact hstartup u hu
      · rw [show u = (ftime + (btime + 2)) + (u - (ftime + (btime + 2))) by omega,
          MultiTapeTM.runFrom_add, hinit]
        exact hrounds _
    have hs := f2_space_radius E x B hall t
    have hw := f2_loop_fuel_width F R T hF x
    have hb : 2 * B + 1 ≤ 19 * (S x.length + T x.length + 1) := by
      dsimp only [B]
      omega
    calc
      E.tm.spaceUsed (E.tm.initCfg x) t ≤ E.k * (2 * B + 1) := hs
      _ ≤ E.k * (19 * (S x.length + T x.length + 1)) := Nat.mul_le_mul_left _ hb
      _ = (19 * E.k) * (S x.length + T x.length + 1) := by ring
      _ ≤ (c + 19 * E.k) * (S x.length + T x.length + 1) :=
        Nat.mul_le_mul_right _ (Nat.le_add_left _ _)

end Turing.FinTM
```

## ===== TCSlib/Complexity/TuringMachine/Build/Zone.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Simulation
import TCSlib.Complexity.TuringMachine.Build.Embed
import TCSlib.Complexity.TuringMachine.Build.Seam
import TCSlib.Complexity.TuringMachine.Build.Catalog

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: the zoned tape carrier (Z2)

The zone representation of the machine-construction library
(`machine-library-design.md` §13, Z2; decisions 13.1 and 13.2): the data
of two stacks of **zones** — level `i` holding up to `2 · 2^i` virtual
cells per side — realized on one physical binary tape around a two-cell
home, with each virtual `Option Bool` cell stored as a **paired
presence/data cell** (decision 13.2; the `SweepAlphabet` product cells of
`Robustness/SingleTape.lean` are the in-repo precedent this replaces with
pairing, keeping the binary alphabet). This is the Hennie-Stearns
representation ([AB09] §1.7): the virtual head always reads at the home,
and locality is restored by per-level rebalancing shifts whose costs are
geometric in the level.

## Design (13a; spec-time refinements, amended by the round-1 audit)

* **The carrier is data, the invariant is the consumer's.** `ZoneContents`
  carries per-zone words bounded by capacity; the Hennie-Stearns
  `{empty, half, full}` fullness discipline, the `2^i`-credit amortization,
  and the simulation theorem live with the consumer (plan §2.1).
* **Shifts are pairwise, order-preserving, and totally guarded** (round-1
  repair, finding A-S2-1): the level-`i` inward shift moves the inner
  `2^(i-1)` stored cells of zone `i` into the **empty** zone `i - 1`, and
  carries **no room premise** — it removes cells from the donor, so a full
  donor is always a legal source. The outward shift moves the outer half
  of a **full** zone `i - 1` onto the front of zone `i`, and its room
  condition on the receiving zone lives **inside its guard**. Outside its
  guard every operation is the identity, and the machine rows realize the
  total guarded operation — identity branch included. The classical
  multi-level rebalance is the descending/move/ascending cascade of these
  ops (`zoneCascadeRight` below), whose represented-word, length, and
  geometric-cost statements are part of this gate per the round-1 audit.
* **One shift machine per direction and side**, taking the level in unary
  on the scratch tape: the Hennie-Stearns simulator is a single machine,
  so the level cannot be baked into finite control.
* **Left/right asymmetry of the cell pairing** is fixed by the layout
  (below) and documented once: on the right, even offsets carry presence
  bits; on the left, odd offsets do.

## The physical layout

Home: cells `0` (presence) and `1` (data). Right virtual slot `s`: cells
`2s + 2` (presence) and `2s + 3` (data). Left virtual slot `s`: cells
`-2s - 2` (presence) and `-2s - 1` (data). Zone `i` owns the slots
`[zoneBase i, zoneBase i + zoneCapacity i)` of its side, where
`zoneCapacity i = 2 · 2^i` and `zoneBase i = 2 · (2^i - 1)` (the exact sum
of the inner capacities). Every integer cell is owned by exactly one slot
or the home.

## Status: statement skeleton (§13 statement phase, tranche A-S2, round 3)

Definitions are real; every contract is `sorry`d with a proof sketch.
Round 1 (`audits/zone-infra-findings.md`) returned the inward-room blocker
(A-S2-1, repaired: premise removed, wrappers split, cascade added); round
2 (`audits/zone-infra-r2-findings.md`) accepted that repair and returned
one blocker on the new cascade contracts (A-S2-R2-1, repaired: the
top-left room hypotheses added — necessary for the lengths theorem, the
weaker one-pass form for the word theorem — with the `j = 0` and
blocked-cascade regressions).

## Main definitions and results

* `Turing.zoneCellBits`/`Turing.zoneCellOf` — the paired-cell codec.
* `Turing.ZoneContents`, `Turing.zoneTape` — the carrier and its physical
  realization.
* `Turing.zoneSide` — the represented virtual half-word (inner zones
  first).
* `Turing.zoneShiftInW`/`Turing.zoneShiftOutW` — the pure pairwise
  rebalancing ops on one side's family, totally guarded, with
  `Turing.zoneSide_shiftInW`/`Turing.zoneSide_shiftOutW` the honesty
  lemmas: rebalancing never changes the represented word.
* `Turing.zoneShiftIn`/`Turing.zoneShiftOut` — the hypothesis-free
  contents-level wrappers (round-1 repair).
* `Turing.zoneMoveRight`/`Turing.zoneMoveLeft`, `Turing.zoneMove`,
  `Turing.zoneHomeWrite` — the pure head-step and write ops.
* `Turing.zoneShiftInW_full_donor` — the full-donor regression required by
  the round-1 audit: a full donor above an empty zone shifts inward with
  no side condition.
* `Turing.zoneCascadeRight`, `Turing.zoneSide_cascadeRight`,
  `Turing.zoneCascadeRight_lengths`, `Turing.zoneCascade_cost_le`,
  `Turing.zoneCascadeRight_zero`, `Turing.zoneCascadeRight_blocked` — the
  classical rebalance as a cascade of pairwise ops: under the classical
  pre-state **and the top-left room hypotheses** it realizes one virtual
  right move and restores every inner level to half-full; its summed row
  budgets stay geometric; the regressions pin the `j = 0` case and the
  harmlessly blocked full-receiver case.
* `Turing.FinTM.exists_zoneShiftInTM`/`exists_zoneShiftOutTM` — the
  machine rows: one two-tape machine per direction and side, level in
  unary on the scratch tape, exact `O(2^i)` budgets, visited sets inside
  the level-`i` physical extent, realizing the total guarded op.
* `Turing.zoneTape_blank_outside`,
  `Turing.MultiTapeTM.spaceUsedByTape_le_card_Icc` — the cardinality
  exports the Z4 space annotation consumes.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern
  Approach*, Cambridge University Press, 2009. (§1.7, the Hennie-Stearns
  simulation; Exercise 1.6.)
* In-repo precedents: `SweepCell`/`SweepAlphabet`
  (`Robustness/SingleTape.lean`); `ObliviousSetup.lean`'s guide-zone
  layout.
-/

namespace Turing

/-! ### The paired-cell codec (decision 13.2) -/

/-- Encode one virtual `Option Bool` cell as its presence and data bits. -/
def zoneCellBits (v : Option Bool) : Bool × Bool := (v.isSome, v.getD false)

/-- Decode a presence/data bit pair back to the virtual cell. -/
def zoneCellOf (p d : Bool) : Option Bool := if p then some d else none

/-- The codec round-trips (skeleton-time proof; flagged). -/
theorem zoneCellOf_bits (v : Option Bool) :
    zoneCellOf (zoneCellBits v).1 (zoneCellBits v).2 = v := by
  cases v <;> rfl

/-! ### Layout arithmetic -/

/-- The capacity of zone `i`, in virtual cells per side. -/
def zoneCapacity (i : ℕ) : ℕ := 2 * 2 ^ i

/-- The first virtual slot of zone `i`: the exact total capacity of the
zones inside it. -/
def zoneBase (i : ℕ) : ℕ := 2 * (2 ^ i - 1)

/-- Bases telescope by capacities (skeleton-time proof; flagged). -/
theorem zoneBase_succ (i : ℕ) : zoneBase (i + 1) = zoneBase i + zoneCapacity i := by
  have h : 0 < 2 ^ i := Nat.two_pow_pos i
  simp only [zoneBase, zoneCapacity, pow_succ]
  omega

/-- The zone owning virtual slot `s`: the unique `i` with
`zoneBase i ≤ s < zoneBase (i + 1)`. -/
def zoneIndex (s : ℕ) : ℕ := Nat.log2 (s / 2 + 1)

/-- `zoneIndex` is the inverse of the base arithmetic: a slot lies in the
zone it indexes.

**Proof sketch.** Write `s = 2r + ε`; both base endpoints are even, so the
sandwich `zoneBase i ≤ s < zoneBase (i + 1)` is equivalent to
`2^i ≤ r + 1 < 2^(i+1)`, which characterizes `Nat.log2 (r + 1)` (the
argument is positive, so there is no logarithm-at-zero case). The round-1
audit's independent derivation is the route. -/
theorem zoneIndex_eq_iff (s i : ℕ) :
    zoneIndex s = i ↔ zoneBase i ≤ s ∧ s < zoneBase (i + 1) := by
  rw [zoneIndex, Nat.log2_eq_iff (by omega)]
  have h := Nat.two_pow_pos i
  have h' := Nat.two_pow_pos (i + 1)
  unfold zoneBase
  omega

/-! ### The carrier -/

/-- The zone contents of one tape: the home cell and, per level and side,
the stored word (inner end first), bounded by capacity. Fullness
discipline is deliberately **not** carried here (design §13a): the
Hennie-Stearns `{empty, half, full}` invariant is the consumer's, and the
round-1 audit's cascade analysis confirms intermediate cascade states
leave the discipline anyway. -/
structure ZoneContents (ℓ : ℕ) where
  /-- the virtual cell under the virtual head -/
  home : Option Bool
  /-- the left zone words, inner end first -/
  left : Fin ℓ → List (Option Bool)
  /-- the right zone words, inner end first -/
  right : Fin ℓ → List (Option Bool)
  /-- left words fit their zones -/
  left_le : ∀ i, (left i).length ≤ zoneCapacity i.val
  /-- right words fit their zones -/
  right_le : ∀ i, (right i).length ≤ zoneCapacity i.val

/-- The stored virtual cell at slot `s` of one side, or `none` when the
slot is beyond the stored words (an unoccupied slot, physically blank —
distinct, through the pairing, from an occupied slot storing a blank). -/
def zoneSlot {ℓ : ℕ} (w : Fin ℓ → List (Option Bool)) (s : ℕ) :
    Option (Option Bool) :=
  if h : zoneIndex s < ℓ then (w ⟨zoneIndex s, h⟩)[s - zoneBase (zoneIndex s)]?
  else none

/-- The physical realization of zone contents: home at cells `0`/`1`,
right slot `s` at `2s + 2`/`2s + 3`, left slot `s` at `-2s - 2`/`-2s - 1`;
occupied slots store their presence and data bits, unoccupied slots and
cells beyond every zone are blank. On the right, even cells (relative to
the slot base) carry presence; on the left the roles are mirrored, so odd
negative offsets carry data — the one asymmetry of the layout, fixed
here. -/
def zoneTape {ℓ : ℕ} (z : ZoneContents ℓ) : ℤ → Option Bool := fun c =>
  if c = 0 then some z.home.isSome
  else if c = 1 then some (z.home.getD false)
  else if 2 ≤ c then
    let n := (c - 2).toNat
    match zoneSlot z.right (n / 2) with
    | some v => some (if n % 2 = 0 then v.isSome else v.getD false)
    | none => none
  else
    let n := (-c - 1).toNat
    match zoneSlot z.left (n / 2) with
    | some v => some (if n % 2 = 1 then v.isSome else v.getD false)
    | none => none

/-- The empty contents (blank home, every zone empty). -/
def ZoneContents.empty (ℓ : ℕ) : ZoneContents ℓ where
  home := none
  left := fun _ => []
  right := fun _ => []
  left_le := fun _ => by simp
  right_le := fun _ => by simp

/-- The empty contents realize the almost-blank tape: the home pair
stores the blank cell, and every other physical cell is blank.

**Proof sketch.** `zoneSlot` of the empty family is `none` at every slot
(`List.getElem?` of `[]`), so both side branches of `zoneTape` return
`none`; the home cells compute `zoneCellBits none = (false, false)`. -/
theorem zoneTape_empty (ℓ : ℕ) (c : ℤ) :
    zoneTape (ZoneContents.empty ℓ) c =
      if c = 0 then some false else if c = 1 then some false else none := by
  simp [zoneTape, ZoneContents.empty, zoneSlot]

/-- Cells beyond the physical extent of `ℓ` levels are blank, for every
contents: the zones' slots stop at `zoneBase ℓ`, so the tape is `none`
outside `[-(2 * zoneBase ℓ + 1), 2 * zoneBase ℓ + 1]`.

**Proof sketch.** A cell at distance beyond the extent maps to a slot
`s ≥ zoneBase ℓ`; `zoneIndex_eq_iff` puts `zoneIndex s ≥ ℓ`, so `zoneSlot`
returns `none` by its guard. (The round-1 audit computed the sharper
asymmetric extent `[-2·zoneBase ℓ, 2·zoneBase ℓ + 1]`; the stated
symmetric bound is the safe envelope.) -/
theorem zoneTape_blank_outside {ℓ : ℕ} (z : ZoneContents ℓ) (c : ℤ)
    (hc : (2 * zoneBase ℓ + 1 : ℤ) < |c|) : zoneTape z c = none := by
  have hs (w : Fin ℓ → List (Option Bool)) (s : ℕ)
      (hb : zoneBase ℓ ≤ s) : zoneSlot w s = none := by
    unfold zoneSlot
    split_ifs with hi
    · have htop := ((zoneIndex_eq_iff s (zoneIndex s)).mp rfl).2
      have hp := Nat.pow_le_pow_right (by decide : 0 < 2)
        (Nat.succ_le_of_lt hi)
      unfold zoneBase at *
      omega
    · rfl
  have h0 : c ≠ 0 := by intro h; rw [h, abs_zero] at hc; omega
  have h1 : c ≠ 1 := by intro h; rw [h] at hc; change 2 * (zoneBase ℓ : ℤ) + 1 < 1 at hc; omega
  simp only [zoneTape, if_neg h0, if_neg h1]
  by_cases hpos : 2 ≤ c
  · rw [if_pos hpos]
    rw [abs_of_nonneg (by omega : 0 ≤ c)] at hc
    have hb : zoneBase ℓ ≤ (c - 2).toNat / 2 := by omega
    simp only [hs z.right _ hb]
  · rw [if_neg hpos]
    rw [abs_of_neg (by omega : c < 0)] at hc
    have hb : zoneBase ℓ ≤ (-c - 1).toNat / 2 := by omega
    simp only [hs z.left _ hb]

/-! ### The represented word -/

/-- The virtual half-word one side represents: the zone words
concatenated inner-first. -/
def zoneSide {ℓ : ℕ} (w : Fin ℓ → List (Option Bool)) : List (Option Bool) :=
  (List.finRange ℓ).flatMap fun i => w i

private theorem zoneSide_succ {n : ℕ} (w : Fin (n + 1) → List (Option Bool)) :
    zoneSide w = w 0 ++ zoneSide (fun k => w k.succ) := by
  simp [zoneSide, List.finRange_succ, List.flatMap_map]

/-- Replacing two adjacent zone words with the same concatenation preserves
the represented side. Induct on the number of levels, peeling off the
unchanged first word until the changed pair is at the front. -/
private theorem zoneSide_adjacent {n : ℕ} (a : ℕ) (ha : a + 1 < n)
    (w v : Fin n → List (Option Bool))
    (hp : v ⟨a, by omega⟩ ++ v ⟨a + 1, ha⟩ =
      w ⟨a, by omega⟩ ++ w ⟨a + 1, ha⟩)
    (hf : ∀ k, k.val ≠ a → k.val ≠ a + 1 → v k = w k) :
    zoneSide v = zoneSide w := by
  induction n generalizing a with
  | zero => omega
  | succ n ih =>
    cases a with
    | zero =>
      cases n with
      | zero => omega
      | succ n =>
        rw [zoneSide_succ, zoneSide_succ]
        rw [zoneSide_succ, zoneSide_succ, ← List.append_assoc, ← List.append_assoc]
        rw [show v 0 ++ v (Fin.succ 0) = w 0 ++ w (Fin.succ 0) from hp]
        congr 1
        congr 1
        funext k
        apply hf <;> simp
    | succ a =>
      rw [zoneSide_succ, zoneSide_succ, hf 0 (by simp) (by simp)]
      congr 1
      apply ih a (by omega) (fun k => w k.succ) (fun k => v k.succ)
      · exact hp
      · intro k h0 h1
        apply hf <;> simp only [Fin.val_succ] <;> omega

/-! ### Pure rebalancing (pairwise, order-preserving, totally guarded) -/

/-- The level-`i` inward shift on one side's family: when `1 ≤ i < ℓ` and
zone `i - 1` is **empty**, move the inner `2^(i-1)` stored cells (or all
of them, if fewer) of zone `i` into it; identity otherwise. **No room
premise exists** (round-1 repair, A-S2-1): the operation removes cells
from the donor, so a full donor is always legal — the exact case the
classical rebalance needs. -/
def zoneShiftInW {ℓ : ℕ} (i : ℕ) (w : Fin ℓ → List (Option Bool)) :
    Fin ℓ → List (Option Bool) := fun j =>
  if hi : 1 ≤ i ∧ i < ℓ then
    if w ⟨i - 1, by omega⟩ = [] then
      if j.val = i - 1 then (w ⟨i, hi.2⟩).take (2 ^ (i - 1))
      else if j.val = i then (w ⟨i, hi.2⟩).drop (2 ^ (i - 1))
      else w j
    else w j
  else w j

/-- The level-`i` outward shift on one side's family: when `1 ≤ i < ℓ`,
zone `i - 1` is **full**, and the receiving zone `i` has room for the
moved half, move zone `i - 1`'s outer half onto the front of zone `i`;
identity otherwise. The room condition lives **inside the guard**
(round-1 repair): no caller carries a hypothesis, and a cramped receiver
makes the op the identity rather than ill-defined. -/
def zoneShiftOutW {ℓ : ℕ} (i : ℕ) (w : Fin ℓ → List (Option Bool)) :
    Fin ℓ → List (Option Bool) := fun j =>
  if hi : 1 ≤ i ∧ i < ℓ then
    if (w ⟨i - 1, by omega⟩).length = zoneCapacity (i - 1) ∧
        (w ⟨i, hi.2⟩).length + 2 ^ (i - 1) ≤ zoneCapacity i then
      if j.val = i - 1 then (w ⟨i - 1, by omega⟩).take (2 ^ (i - 1))
      else if j.val = i then
        (w ⟨i - 1, by omega⟩).drop (2 ^ (i - 1)) ++ w ⟨i, hi.2⟩
      else w j
    else w j
  else w j

/-- Inward rebalancing never changes the represented half-word.

**Proof sketch.** A disabled guard gives the identity. When enabled, zones
`i - 1` and `i` are adjacent in the inner-first concatenation, zone
`i - 1` was empty, and `take ++ drop` restores zone `i`'s word, so the
concatenation is unchanged. -/
theorem zoneSide_shiftInW {ℓ : ℕ} (i : ℕ) (w : Fin ℓ → List (Option Bool)) :
    zoneSide (zoneShiftInW i w) = zoneSide w := by
  by_cases hi : 1 ≤ i ∧ i < ℓ
  · by_cases he : w ⟨i - 1, by omega⟩ = []
    · apply zoneSide_adjacent (i - 1) (by omega)
      · have hne : i ≠ i - 1 := by omega
        have hsucc : i - 1 + 1 = i := by omega
        simp [zoneShiftInW, hi, he, hsucc, hne, List.take_append_drop]
      · intro k h0 h1
        have hk : k.val ≠ i := by omega
        simp [zoneShiftInW, hi, he, h0, hk]
    · have hsame : zoneShiftInW i w = w := by
        funext k
        simp [zoneShiftInW, hi, he]
      rw [hsame]
  · have hsame : zoneShiftInW i w = w := by
      funext k
      simp [zoneShiftInW, hi]
    rw [hsame]

/-- Outward rebalancing never changes the represented half-word.

**Proof sketch.** A disabled guard gives the identity. When enabled, the
adjacent two-zone segment is literally re-associated:
`take q ++ (drop q ++ wᵢ) = wᵢ₋₁ ++ wᵢ` at the cutoff `q = 2^(i-1)`. -/
theorem zoneSide_shiftOutW {ℓ : ℕ} (i : ℕ) (w : Fin ℓ → List (Option Bool)) :
    zoneSide (zoneShiftOutW i w) = zoneSide w := by
  by_cases hi : 1 ≤ i ∧ i < ℓ
  · by_cases hg : (w ⟨i - 1, by omega⟩).length = zoneCapacity (i - 1) ∧
        (w ⟨i, hi.2⟩).length + 2 ^ (i - 1) ≤ zoneCapacity i
    · apply zoneSide_adjacent (i - 1) (by omega)
      · have hne : i ≠ i - 1 := by omega
        have hsucc : i - 1 + 1 = i := by omega
        simp [zoneShiftOutW, hi, hg, hsucc, hne, ← List.append_assoc]
      · intro k h0 h1
        have hk : k.val ≠ i := by omega
        simp [zoneShiftOutW, hi, hg, h0, hk]
    · have hsame : zoneShiftOutW i w = w := by
        funext k
        simp [zoneShiftOutW, hi, hg]
      rw [hsame]
  · have hsame : zoneShiftOutW i w = w := by
      funext k
      simp [zoneShiftOutW, hi]
    rw [hsame]

/-- **The full-donor regression** (required by the round-1 audit,
A-S2-1): above an empty zone, a donor of any length — a full one included —
shifts inward with no side condition: the receiving zone gets the inner
`2^(i-1)` cells (or all, if fewer) and the donor keeps the rest.

**Proof sketch.** Unfold `zoneShiftInW`: both guards fire by the
hypotheses, and the two branch equations are the stated `take`/`drop`. -/
theorem zoneShiftInW_full_donor {ℓ : ℕ} (i : ℕ) (hi : 1 ≤ i) (hℓ : i < ℓ)
    (w : Fin ℓ → List (Option Bool)) (hempty : w ⟨i - 1, by omega⟩ = []) :
    zoneShiftInW i w ⟨i - 1, by omega⟩ = (w ⟨i, hℓ⟩).take (2 ^ (i - 1)) ∧
    zoneShiftInW i w ⟨i, hℓ⟩ = (w ⟨i, hℓ⟩).drop (2 ^ (i - 1)) := by
  have hne : i ≠ i - 1 := by omega
  simp [zoneShiftInW, hi, hℓ, hempty, hne]

private theorem zoneShiftInW_capacity {ℓ : ℕ} (i : ℕ)
    (w : Fin ℓ → List (Option Bool))
    (hw : ∀ j, (w j).length ≤ zoneCapacity j.val) :
    ∀ j, (zoneShiftInW i w j).length ≤ zoneCapacity j.val := by
  intro j
  unfold zoneShiftInW
  split_ifs with hi he hj hj
  · simp only [List.length_take, zoneCapacity, hj]
    omega
  · have h := hw ⟨i, hi.2⟩
    dsimp only at h
    simp only [List.length_drop, hj]
    exact (Nat.sub_le _ _).trans h
  · exact hw j
  · exact hw j
  · exact hw j

/-- Lift the inward shift to contents: `side = false` acts on the left
family, `side = true` on the right. Hypothesis-free (round-1 repair).

**Proof sketch** (capacity fields): the receiving zone gets at most
`2^(i-1) ≤ zoneCapacity (i-1)` cells; the donor's word only shrinks;
untouched zones keep their bounds. -/
def zoneShiftIn {ℓ : ℕ} (side : Bool) (i : ℕ) (z : ZoneContents ℓ) :
    ZoneContents ℓ where
  home := z.home
  left := if side then z.left else zoneShiftInW i z.left
  right := if side then zoneShiftInW i z.right else z.right
  left_le := by
    cases side
    · exact zoneShiftInW_capacity i z.left z.left_le
    · exact z.left_le
  right_le := by
    cases side
    · exact z.right_le
    · exact zoneShiftInW_capacity i z.right z.right_le

private theorem zoneShiftOutW_capacity {ℓ : ℕ} (i : ℕ)
    (w : Fin ℓ → List (Option Bool))
    (hw : ∀ j, (w j).length ≤ zoneCapacity j.val) :
    ∀ j, (zoneShiftOutW i w j).length ≤ zoneCapacity j.val := by
  intro j
  unfold zoneShiftOutW
  split_ifs with hi hg hj hj
  · simp only [List.length_take, zoneCapacity, hj]
    omega
  · simp only [List.length_append, List.length_drop, hg.1, hj]
    have h := hg.2
    unfold zoneCapacity at *
    omega
  · exact hw j
  · exact hw j
  · exact hw j

/-- Lift the outward shift to contents. Hypothesis-free: the receiving
zone's room condition is inside the family op's guard.

**Proof sketch** (capacity fields): when the guard fires, the shrunk
lower word fits trivially and the enlarged upper word fits by the guard's
own room conjunct; otherwise everything is unchanged. -/
def zoneShiftOut {ℓ : ℕ} (side : Bool) (i : ℕ) (z : ZoneContents ℓ) :
    ZoneContents ℓ where
  home := z.home
  left := if side then z.left else zoneShiftOutW i z.left
  right := if side then zoneShiftOutW i z.right else z.right
  left_le := by
    cases side
    · exact zoneShiftOutW_capacity i z.left z.left_le
    · exact z.left_le
  right_le := by
    cases side
    · exact z.right_le
    · exact zoneShiftOutW_capacity i z.right z.right_le

/-! ### Pure head steps and the home write -/

/-- Overwrite the virtual cell under the head. -/
def zoneHomeWrite {ℓ : ℕ} (z : ZoneContents ℓ) (v : Option Bool) :
    ZoneContents ℓ := { z with home := v }

/-- Writing the home changes exactly the two home cells of the physical
tape.

**Proof sketch.** `zoneTape` consults `home` only in its first two
branches; every slot branch reads the untouched families. -/
theorem zoneTape_homeWrite {ℓ : ℕ} (z : ZoneContents ℓ) (v : Option Bool)
    (c : ℤ) (h0 : c ≠ 0) (h1 : c ≠ 1) :
    zoneTape (zoneHomeWrite z v) c = zoneTape z c := by
  simp only [zoneTape, zoneHomeWrite, if_neg h0, if_neg h1]

/-- The virtual head steps right: the home is pushed onto the inner end of
the left stack's zone `0`, and the new home is popped from the right
stack's zone `0` (blank when that zone is empty — the virtual tape is
blank past its stored extent; the Hennie-Stearns consumer's invariant
makes this the genuinely-blank case). Capacity of `L_0` is the consumer's
rebalancing obligation, carried here as a hypothesis; the hypothesis-free
guarded form is `Turing.zoneMove`. -/
def zoneMoveRight {ℓ : ℕ} (hℓ : 0 < ℓ) (z : ZoneContents ℓ)
    (hroom : (z.left ⟨0, hℓ⟩).length + 1 ≤ zoneCapacity 0) :
    ZoneContents ℓ where
  home := ((z.right ⟨0, hℓ⟩).headI : Option Bool)
  left := fun j => if j.val = 0 then z.home :: z.left j else z.left j
  right := fun j => if j.val = 0 then (z.right j).tail else z.right j
  left_le := by
    intro j
    split_ifs with hj
    · have he : j = ⟨0, hℓ⟩ := Fin.ext hj
      subst j
      simpa only [List.length_cons] using hroom
    · exact z.left_le j
  right_le := by
    intro j
    split_ifs
    · simpa only [List.length_tail] using
        (Nat.sub_le (z.right j).length 1).trans (z.right_le j)
    · exact z.right_le j

/-- The mirrored left step. -/
def zoneMoveLeft {ℓ : ℕ} (hℓ : 0 < ℓ) (z : ZoneContents ℓ)
    (hroom : (z.right ⟨0, hℓ⟩).length + 1 ≤ zoneCapacity 0) :
    ZoneContents ℓ where
  home := ((z.left ⟨0, hℓ⟩).headI : Option Bool)
  left := fun j => if j.val = 0 then (z.left j).tail else z.left j
  right := fun j => if j.val = 0 then z.home :: z.right j else z.right j
  left_le := by
    intro j
    split_ifs
    · simpa only [List.length_tail] using
        (Nat.sub_le (z.left j).length 1).trans (z.left_le j)
    · exact z.left_le j
  right_le := by
    intro j
    split_ifs with hj
    · have he : j = ⟨0, hℓ⟩ := Fin.ext hj
      subst j
      simpa only [List.length_cons] using hroom
    · exact z.right_le j

/-- The totally guarded head step (`dir = true` is right): acts when
`0 < ℓ` and the pushed side has room, else identity — the foldable form
the cascade uses. -/
def zoneMove {ℓ : ℕ} (dir : Bool) (z : ZoneContents ℓ) : ZoneContents ℓ :=
  if hℓ : 0 < ℓ then
    match dir with
    | true =>
      if h : (z.left ⟨0, hℓ⟩).length + 1 ≤ zoneCapacity 0 then
        zoneMoveRight hℓ z h
      else z
    | false =>
      if h : (z.right ⟨0, hℓ⟩).length + 1 ≤ zoneCapacity 0 then
        zoneMoveLeft hℓ z h
      else z
  else z

/-- A right step transforms the represented tape as the virtual head move:
the old home joins the left word's inner end, and the right word loses its
inner cell (a nonempty `R_0` case; the blank-extension case pads with the
virtual blank).

**Proof sketch.** Pure list bookkeeping on `zoneSide`: `finRange`'s head
is zone `0`, and only zone `0` changes on each side. -/
theorem zoneSide_moveRight {ℓ : ℕ} (hℓ : 0 < ℓ) (z : ZoneContents ℓ)
    (hroom : (z.left ⟨0, hℓ⟩).length + 1 ≤ zoneCapacity 0)
    (hne : z.right ⟨0, hℓ⟩ ≠ []) :
    zoneSide (zoneMoveRight hℓ z hroom).left = z.home :: zoneSide z.left ∧
    zoneSide (zoneMoveRight hℓ z hroom).right = (zoneSide z.right).tail := by
  cases ℓ with
  | zero => omega
  | succ n =>
    have hleft : (fun k : Fin n => (zoneMoveRight hℓ z hroom).left k.succ) =
        (fun k : Fin n => z.left k.succ) := by
      funext k
      simp [zoneMoveRight]
    have hright : (fun k : Fin n => (zoneMoveRight hℓ z hroom).right k.succ) =
        (fun k : Fin n => z.right k.succ) := by
      funext k
      simp [zoneMoveRight]
    constructor
    · rw [zoneSide_succ, zoneSide_succ, hleft]
      simp [zoneMoveRight]
    · rw [zoneSide_succ, zoneSide_succ, hright]
      simp only [zoneMoveRight, Fin.val_zero, ite_true]
      exact (List.tail_append_of_ne_nil hne).symm

/-! ### The classical rebalance as a cascade (round-1 repair, A-S2-1)

The round-1 audit supplied the schedule and its analysis; the statements
below are the required gate material. One classical right move at index
`j`: a descending pass of inward-right/outward-left pairs from level `j`
down to `1`, the head step, and the ascending pass back up. -/

/-- One cascade stage at level `i`: shift inward on the right (feeding the
head's side) and outward on the left (draining the side the head leaves). -/
def zoneStepPair {ℓ : ℕ} (i : ℕ) (z : ZoneContents ℓ) : ZoneContents ℓ :=
  zoneShiftOut false i (zoneShiftIn true i z)

/-- The classical right-move rebalance at index `j`: descend `j → 1`,
step right, ascend `1 → j`. -/
def zoneCascadeRight {ℓ : ℕ} (j : ℕ) (z : ZoneContents ℓ) : ZoneContents ℓ :=
  (List.range j).foldl (fun z i => zoneStepPair (i + 1) z)
    (zoneMove true
      ((List.range j).reverse.foldl (fun z i => zoneStepPair (i + 1) z) z))

private theorem zoneStepPair_side {ℓ : ℕ} (i : ℕ) (z : ZoneContents ℓ) :
    zoneSide (zoneStepPair i z).left = zoneSide z.left ∧
      zoneSide (zoneStepPair i z).right = zoneSide z.right :=
  ⟨zoneSide_shiftOutW i z.left, zoneSide_shiftInW i z.right⟩

private theorem zoneStepPair_frame {ℓ : ℕ} (i : ℕ) (z : ZoneContents ℓ)
    (k : Fin ℓ) (h0 : k.val ≠ i - 1) (h1 : k.val ≠ i) :
    (zoneStepPair i z).left k = z.left k ∧
      (zoneStepPair i z).right k = z.right k := by
  change zoneShiftOutW i z.left k = z.left k ∧ zoneShiftInW i z.right k = z.right k
  constructor
  · unfold zoneShiftOutW
    split_ifs <;> simp_all
  · unfold zoneShiftInW
    split_ifs <;> simp_all

private theorem zoneStepPair_active {ℓ : ℕ} (i : ℕ) (hi : i + 1 < ℓ)
    (z : ZoneContents ℓ) (hr : z.right ⟨i, by omega⟩ = [])
    (hl : (z.left ⟨i, by omega⟩).length = zoneCapacity i)
    (hroom : (z.left ⟨i + 1, hi⟩).length + 2 ^ i ≤ zoneCapacity (i + 1)) :
    (zoneStepPair (i + 1) z).right ⟨i, by omega⟩ =
        (z.right ⟨i + 1, hi⟩).take (2 ^ i) ∧
    (zoneStepPair (i + 1) z).left ⟨i, by omega⟩ =
        (z.left ⟨i, by omega⟩).take (2 ^ i) ∧
    (zoneStepPair (i + 1) z).right ⟨i + 1, hi⟩ =
        (z.right ⟨i + 1, hi⟩).drop (2 ^ i) ∧
    (zoneStepPair (i + 1) z).left ⟨i + 1, hi⟩ =
        (z.left ⟨i, by omega⟩).drop (2 ^ i) ++ z.left ⟨i + 1, hi⟩ := by
  simp [zoneStepPair, zoneShiftIn, zoneShiftOut, zoneShiftInW, zoneShiftOutW,
    hi, hr, hl, hroom]

private theorem zoneCascadeRight_succ {ℓ : ℕ} (j : ℕ) (z : ZoneContents ℓ) :
    zoneCascadeRight (j + 1) z =
      zoneStepPair (j + 1) (zoneCascadeRight j (zoneStepPair (j + 1) z)) := by
  simp [zoneCascadeRight, List.range_succ, List.reverse_append, List.foldl_append]

/-- The recursive descent and ascent only touch levels at or below their
index. Induction peels off the outer pair; the base move touches zero. -/
private theorem zoneCascadeRight_frame {ℓ : ℕ} (j : ℕ) (z : ZoneContents ℓ)
    (k : Fin ℓ) (hk : j < k.val) :
    (zoneCascadeRight j z).left k = z.left k ∧
      (zoneCascadeRight j z).right k = z.right k := by
  induction j generalizing z with
  | zero =>
    have hk0 : k.val ≠ 0 := by omega
    simp only [zoneCascadeRight, List.range_zero, List.reverse_nil, List.foldl_nil]
    unfold zoneMove
    split_ifs <;> simp [zoneMoveRight, hk0]
  | succ j ih =>
    rw [zoneCascadeRight_succ]
    rw [(zoneStepPair_frame _ _ k (by omega) (by omega)).1,
      (zoneStepPair_frame _ _ k (by omega) (by omega)).2]
    rw [(ih _ (by omega)).1, (ih _ (by omega)).2]
    exact zoneStepPair_frame _ _ k (by omega) (by omega)

/-- The cascade realizes exactly one virtual right move. Preconditions are
the classical pre-state at index `j` — on the right, zones below `j` empty
and the donor `j` nonempty; on the left, zones below `j` full — **plus the
top-left receiving room for one pass** (round-2 repair, A-S2-R2-1: without
it, a full left zone `j` blocks the drain, the guarded ops are identities,
and the conclusion is false already at `ℓ = 1`, `j = 0`). The `+ 2^(j-1)`
form is the round-2 audit's weaker sufficient condition for the word
equalities (at `j = 0`, natural subtraction makes it `+ 1`); the boundary
instance with room for exactly one pass — where these equalities hold but
half-full restoration fails — is the recorded reason this theorem's
hypothesis is weaker than `zoneCascadeRight_lengths`'s.

**Proof sketch** (the round-2 audit's schedule analysis, adopted as the
binding route): each descending prefix of the donor is nonempty, so `R₀`
is nonempty at the central move, and the left descending pass makes room
for the push under `hroom`; every surrounding shift preserves the
concatenations whether its guard fires or not
(`zoneSide_shiftInW`/`OutW`), so the single legal push/pop
(`zoneSide_moveRight`) gives exactly the two word equalities. Half-full
restoration is **not** used. -/
theorem zoneSide_cascadeRight {ℓ : ℕ} (j : ℕ) (hj : j < ℓ)
    (z : ZoneContents ℓ)
    (hr : ∀ k (hk : k < j), z.right ⟨k, by omega⟩ = [])
    (hl : ∀ k (hk : k < j),
      (z.left ⟨k, by omega⟩).length = zoneCapacity k)
    (hdonor : z.right ⟨j, hj⟩ ≠ [])
    (hroom : (z.left ⟨j, hj⟩).length + 2 ^ (j - 1) ≤ zoneCapacity j) :
    zoneSide (zoneCascadeRight j z).left = z.home :: zoneSide z.left ∧
    zoneSide (zoneCascadeRight j z).right = (zoneSide z.right).tail := by
  induction j generalizing z with
  | zero =>
    have hroom0 : (z.left ⟨0, hj⟩).length + 1 ≤ zoneCapacity 0 := by
      simpa using hroom
    simpa only [zoneCascadeRight, List.range_zero, List.reverse_nil,
      List.foldl_nil, zoneMove, dif_pos hj, dif_pos hroom0] using
      zoneSide_moveRight hj z hroom0 hdonor
  | succ j ih =>
    have hjl : j < ℓ := by omega
    have hroom' : (z.left ⟨j + 1, hj⟩).length + 2 ^ j ≤
        zoneCapacity (j + 1) := by simpa using hroom
    have hactive := zoneStepPair_active j hj z (hr j (by omega))
      (hl j (by omega)) hroom'
    have hr' : ∀ k (hk : k < j),
        (zoneStepPair (j + 1) z).right ⟨k, by omega⟩ = [] := by
      intro k hk
      rw [(zoneStepPair_frame (j + 1) z ⟨k, by omega⟩ (by dsimp; omega) (by dsimp; omega)).2]
      exact hr k (by omega)
    have hl' : ∀ k (hk : k < j),
        ((zoneStepPair (j + 1) z).left ⟨k, by omega⟩).length = zoneCapacity k := by
      intro k hk
      rw [(zoneStepPair_frame (j + 1) z ⟨k, by omega⟩ (by dsimp; omega) (by dsimp; omega)).1]
      exact hl k (by omega)
    have hd' : (zoneStepPair (j + 1) z).right ⟨j, hjl⟩ ≠ [] := by
      rw [hactive.1]
      apply List.ne_nil_of_length_pos
      rw [List.length_take]
      exact lt_min (Nat.two_pow_pos j) (List.length_pos_iff.mpr hdonor)
    have hlower : ((zoneStepPair (j + 1) z).left ⟨j, hjl⟩).length = 2 ^ j := by
      rw [hactive.2.1, List.length_take, hl j (by omega)]
      unfold zoneCapacity
      omega
    have hroomlower : ((zoneStepPair (j + 1) z).left ⟨j, hjl⟩).length +
        2 ^ (j - 1) ≤ zoneCapacity j := by
      rw [hlower]
      have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.sub_le j 1)
      unfold zoneCapacity
      omega
    have hinner := ih hjl (zoneStepPair (j + 1) z) hr' hl' hd' hroomlower
    rw [zoneCascadeRight_succ, (zoneStepPair_side _ _).1,
      (zoneStepPair_side _ _).2, hinner.1, hinner.2,
      (zoneStepPair_side _ _).1, (zoneStepPair_side _ _).2]
    exact ⟨rfl, rfl⟩

/-- The cascade restores the half-full discipline below its index: after a
classical right move at index `j` from a donor holding at least `2^j`
cells, every level below `j` is half-full on both sides, the right donor
loses exactly `2^j` cells, and the left zone `j` gains exactly `2^j`.

The top-left room hypothesis is **necessary** (round-2 repair,
A-S2-R2-1): the conclusion's left-top growth together with the result's
`left_le` field imply exactly `|L_j| + 2^j ≤ zoneCapacity j`, and the
classical stable invariant (`|L_j| + |R_j| = 2 · zoneCapacity j / 2` with
`|R_j| ≥ 2^j`) supplies it on every textbook pre-state, so no classical
instance is excluded.

**Proof sketch** (the round-2 audit's two-pass induction, adopted as the
binding route): the descending pass ends with the level-zero pair at
`(1, 1)`, each intermediate level `k` at `(2^(k-1), 3·2^(k-1))`, and the
top pair shifted by `2^(j-1)` — the top outward push legal by `hroom`,
the lower receivers legal because they were just drained; the head move
makes level zero `(0, 2)`; the ascending pass re-fires every guard on
those occupancies, the second top push legal exactly because
`|L_j| + 2^(j-1) + 2^(j-1) = |L_j| + 2^j ≤ zoneCapacity j`. -/
theorem zoneCascadeRight_lengths {ℓ : ℕ} (j : ℕ) (hj : j < ℓ)
    (z : ZoneContents ℓ)
    (hr : ∀ k (hk : k < j), z.right ⟨k, by omega⟩ = [])
    (hl : ∀ k (hk : k < j),
      (z.left ⟨k, by omega⟩).length = zoneCapacity k)
    (hdonor : 2 ^ j ≤ (z.right ⟨j, hj⟩).length)
    (hroom : (z.left ⟨j, hj⟩).length + 2 ^ j ≤ zoneCapacity j) :
    (∀ k (hk : k < j),
      ((zoneCascadeRight j z).right ⟨k, by omega⟩).length = 2 ^ k ∧
      ((zoneCascadeRight j z).left ⟨k, by omega⟩).length = 2 ^ k) ∧
    ((zoneCascadeRight j z).right ⟨j, hj⟩).length =
      (z.right ⟨j, hj⟩).length - 2 ^ j ∧
    ((zoneCascadeRight j z).left ⟨j, hj⟩).length =
      (z.left ⟨j, hj⟩).length + 2 ^ j := by
  induction j generalizing z with
  | zero =>
    have hroom0 : (z.left ⟨0, hj⟩).length + 1 ≤ zoneCapacity 0 := by
      simpa using hroom
    have hm : zoneCascadeRight 0 z = zoneMoveRight hj z hroom0 := by
      simp [zoneCascadeRight, zoneMove, hj, hroom0]
    rw [hm]
    refine ⟨?_, ?_, ?_⟩
    · intro k hk
      omega
    · simp [zoneMoveRight]
    · simp [zoneMoveRight]
  | succ j ih =>
    have hjl : j < ℓ := by omega
    have hp : 0 < 2 ^ j := Nat.two_pow_pos j
    have hroom1 : (z.left ⟨j + 1, hj⟩).length + 2 ^ j ≤
        zoneCapacity (j + 1) := by
      rw [pow_succ] at hroom
      omega
    have hactive := zoneStepPair_active j hj z (hr j (by omega))
      (hl j (by omega)) hroom1
    let z1 := zoneStepPair (j + 1) z
    have hr' : ∀ k (hk : k < j), z1.right ⟨k, by omega⟩ = [] := by
      intro k hk
      change (zoneStepPair (j + 1) z).right ⟨k, _⟩ = []
      rw [(zoneStepPair_frame (j + 1) z ⟨k, by omega⟩
        (by dsimp; omega) (by dsimp; omega)).2]
      exact hr k (by omega)
    have hl' : ∀ k (hk : k < j),
        (z1.left ⟨k, by omega⟩).length = zoneCapacity k := by
      intro k hk
      change ((zoneStepPair (j + 1) z).left ⟨k, _⟩).length = _
      rw [(zoneStepPair_frame (j + 1) z ⟨k, by omega⟩
        (by dsimp; omega) (by dsimp; omega)).1]
      exact hl k (by omega)
    have hrlower : (z1.right ⟨j, hjl⟩).length = 2 ^ j := by
      change ((zoneStepPair (j + 1) z).right ⟨j, hjl⟩).length = _
      rw [hactive.1, List.length_take]
      rw [pow_succ] at hdonor
      omega
    have hllower : (z1.left ⟨j, hjl⟩).length = 2 ^ j := by
      change ((zoneStepPair (j + 1) z).left ⟨j, hjl⟩).length = _
      rw [hactive.2.1, List.length_take, hl j (by omega)]
      unfold zoneCapacity
      omega
    have hrtop : (z1.right ⟨j + 1, hj⟩).length =
        (z.right ⟨j + 1, hj⟩).length - 2 ^ j := by
      change ((zoneStepPair (j + 1) z).right ⟨j + 1, hj⟩).length = _
      rw [hactive.2.2.1, List.length_drop]
    have hltop : (z1.left ⟨j + 1, hj⟩).length =
        (z.left ⟨j + 1, hj⟩).length + 2 ^ j := by
      change ((zoneStepPair (j + 1) z).left ⟨j + 1, hj⟩).length = _
      rw [hactive.2.2.2, List.length_append, List.length_drop, hl j (by omega)]
      unfold zoneCapacity
      omega
    have hinner := ih hjl z1 hr' hl' (by rw [hrlower]) (by
      rw [hllower]
      unfold zoneCapacity
      omega)
    let z2 := zoneCascadeRight j z1
    have hrzero : z2.right ⟨j, hjl⟩ = [] := by
      apply List.length_eq_zero_iff.mp
      change ((zoneCascadeRight j z1).right ⟨j, hjl⟩).length = 0
      rw [hinner.2.1, hrlower, Nat.sub_self]
    have hlfull : (z2.left ⟨j, hjl⟩).length = zoneCapacity j := by
      change ((zoneCascadeRight j z1).left ⟨j, hjl⟩).length = _
      rw [hinner.2.2, hllower]
      unfold zoneCapacity
      omega
    have hframe := zoneCascadeRight_frame j z1 ⟨j + 1, hj⟩ (by dsimp; omega)
    have hrtop2 : (z2.right ⟨j + 1, hj⟩).length =
        (z.right ⟨j + 1, hj⟩).length - 2 ^ j := by
      change ((zoneCascadeRight j z1).right ⟨j + 1, hj⟩).length = _
      rw [hframe.2, hrtop]
    have hltop2 : (z2.left ⟨j + 1, hj⟩).length =
        (z.left ⟨j + 1, hj⟩).length + 2 ^ j := by
      change ((zoneCascadeRight j z1).left ⟨j + 1, hj⟩).length = _
      rw [hframe.1, hltop]
    have hroom2 : (z2.left ⟨j + 1, hj⟩).length + 2 ^ j ≤
        zoneCapacity (j + 1) := by
      rw [hltop2]
      rw [pow_succ] at hroom
      omega
    have hactive2 := zoneStepPair_active j hj z2 hrzero hlfull hroom2
    rw [zoneCascadeRight_succ]
    change (∀ k (hk : k < j + 1),
      ((zoneStepPair (j + 1) z2).right ⟨k, _⟩).length = 2 ^ k ∧
      ((zoneStepPair (j + 1) z2).left ⟨k, _⟩).length = 2 ^ k) ∧
      ((zoneStepPair (j + 1) z2).right ⟨j + 1, hj⟩).length =
        (z.right ⟨j + 1, hj⟩).length - 2 ^ (j + 1) ∧
      ((zoneStepPair (j + 1) z2).left ⟨j + 1, hj⟩).length =
        (z.left ⟨j + 1, hj⟩).length + 2 ^ (j + 1)
    refine ⟨?_, ?_, ?_⟩
    · intro k hk
      by_cases hkj : k = j
      · subst k
        rw [hactive2.1, hactive2.2.1, List.length_take, List.length_take,
          hrtop2, hlfull]
        rw [pow_succ] at hdonor
        unfold zoneCapacity
        constructor <;> omega
      · have hkj' : k < j := by omega
        rw [(zoneStepPair_frame (j + 1) z2 ⟨k, by omega⟩
          (by dsimp; omega) (by dsimp; omega)).2,
          (zoneStepPair_frame (j + 1) z2 ⟨k, by omega⟩
          (by dsimp; omega) (by dsimp; omega)).1]
        exact hinner.1 k hkj'
    · rw [hactive2.2.2.1, List.length_drop, hrtop2, pow_succ]
      omega
    · rw [hactive2.2.2.2, List.length_append, List.length_drop, hlfull, hltop2,
        pow_succ]
      unfold zoneCapacity
      omega

/-- Regression (round-2 audit, A-S2-R2-1): the `j = 0` cascade is exactly
the guarded head move, and with level-zero room and a nonempty donor it
realizes the virtual right move.

**Proof sketch.** `List.range 0 = []`, so the folds vanish; `zoneMove`'s
guard fires by the hypotheses and `zoneSide_moveRight` finishes. -/
theorem zoneCascadeRight_zero {ℓ : ℕ} (hℓ : 0 < ℓ) (z : ZoneContents ℓ)
    (hdonor : z.right ⟨0, hℓ⟩ ≠ [])
    (hroom : (z.left ⟨0, hℓ⟩).length + 1 ≤ zoneCapacity 0) :
    zoneSide (zoneCascadeRight 0 z).left = z.home :: zoneSide z.left ∧
    zoneSide (zoneCascadeRight 0 z).right = (zoneSide z.right).tail := by
  simpa only [zoneCascadeRight, List.range_zero, List.reverse_nil,
    List.foldl_nil, zoneMove, dif_pos hℓ, dif_pos hroom] using
    zoneSide_moveRight hℓ z hroom hdonor

/-- Regression (round-2 audit, A-S2-R2-1): a **full top receiver** blocks
the cascade harmlessly — with the classical lower-left state and
`L_j` at capacity, every outward-left guard fails, the head move is
blocked, and the represented words on both sides are unchanged.

**Proof sketch.** Lower left zones are full, so no outward-left guard
below `j` has room; at `j` the receiver is full; hence `L₀` stays full and
`zoneMove` takes its identity branch. The inward-right shifts preserve the
right concatenation by `zoneSide_shiftInW`. -/
theorem zoneCascadeRight_blocked {ℓ : ℕ} (j : ℕ) (hj : j < ℓ)
    (z : ZoneContents ℓ)
    (hl : ∀ k (hk : k < j),
      (z.left ⟨k, by omega⟩).length = zoneCapacity k)
    (hfull : (z.left ⟨j, hj⟩).length = zoneCapacity j) :
    zoneSide (zoneCascadeRight j z).left = zoneSide z.left ∧
    zoneSide (zoneCascadeRight j z).right = zoneSide z.right := by
  induction j generalizing z with
  | zero =>
    have hno : ¬ (z.left ⟨0, hj⟩).length + 1 ≤ zoneCapacity 0 := by
      rw [hfull]
      omega
    simp [zoneCascadeRight, zoneMove, hj, hno]
  | succ j ih =>
    have hno : ¬ (z.left ⟨j + 1, hj⟩).length + 2 ^ j ≤
        zoneCapacity (j + 1) := by
      rw [hfull]
      have hp := Nat.two_pow_pos j
      omega
    have hf : (zoneStepPair (j + 1) z).left = z.left := by
      funext k
      simp [zoneStepPair, zoneShiftOut, zoneShiftIn, zoneShiftOutW, hj, hno]
    have hl' : ∀ k (hk : k < j),
        ((zoneStepPair (j + 1) z).left ⟨k, by omega⟩).length = zoneCapacity k := by
      intro k hk
      rw [hf]
      exact hl k (by omega)
    have hfull' : ((zoneStepPair (j + 1) z).left ⟨j, by omega⟩).length =
        zoneCapacity j := by
      rw [hf]
      exact hl j (by omega)
    have hinner := ih (by omega) (zoneStepPair (j + 1) z) hl' hfull'
    rw [zoneCascadeRight_succ, (zoneStepPair_side _ _).1,
      (zoneStepPair_side _ _).2, hinner.1, hinner.2,
      (zoneStepPair_side _ _).1, (zoneStepPair_side _ _).2]
    exact ⟨rfl, rfl⟩

/-- The cascade's summed row budgets stay geometric: the charge lemma the
Hennie-Stearns amortization consumes (two shift pairs per level, each
within the row budget `2^i + i + 1`).

**Proof sketch.** `i + 1 ≤ 2^i` for `i ≥ 1`, so each summand is at most
`4 · 2 · 2^i = 8 · 2^i`, and the geometric sum over `1 ≤ i ≤ j` is
`8 · (2^(j+1) - 2) ≤ 16 · 2^j` — the round-1 audit's charge calculation. -/
theorem zoneCascade_cost_le (j : ℕ) :
    ∑ i ∈ Finset.range j, 4 * (2 ^ (i + 1) + (i + 1) + 1) ≤ 16 * 2 ^ j := by
  have hsum : ∀ n : ℕ,
      (∑ i ∈ Finset.range n, 4 * (2 ^ (i + 1) + (i + 1) + 1)) + 16 ≤
        16 * 2 ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have hsmall : n + 2 ≤ 2 ^ (n + 1) := Nat.lt_two_pow_self
      simp only [pow_succ] at *
      omega
  have h := hsum j
  omega

/-! ### The machine rows -/

/-- The physical bits of a zone word in the order seen moving away from
home. On the left a pair is read data-first, on the right presence-first.
This is the finite word to be staged by a delimited catalog transfer. -/
private def zoneStageWord (side : Bool) (w : List (Option Bool)) : List Bool :=
  w.flatMap fun v =>
    if side then [v.isSome, v.getD false] else [v.getD false, v.isSome]

/-- Each occupied virtual cell contributes exactly two nonblank cells. -/
private theorem zoneStageWord_length (side : Bool) (w : List (Option Bool)) :
    (zoneStageWord side w).length = 2 * w.length := by
  induction w with
  | nil => simp [zoneStageWord]
  | cons v w ih =>
    cases side <;> simp_all [zoneStageWord, Nat.mul_add]

/-- Looking up a physical bit first chooses its virtual cell and then
the appropriate component of that cell's pair.
**Proof sketch.** Peel off two positions with each list cell; quotient by
two chooses the remaining cell, and remainder chooses its component. -/
private theorem zoneStageWord_getElem (side : Bool) (w : List (Option Bool))
    (p : ℕ) :
    (zoneStageWord side w)[p]? = (w[p / 2]?).map (fun v =>
      if p % 2 = 0 then
        if side then v.isSome else v.getD false
      else if side then v.getD false else v.isSome) := by
  induction w generalizing p with
  | nil => simp [zoneStageWord]
  | cons v w ih =>
    cases p with
    | zero => cases side <;> simp [zoneStageWord]
    | succ p =>
      cases p with
      | zero => cases side <;> simp [zoneStageWord]
      | succ p =>
        have hd : (p + 1 + 1) / 2 = p / 2 + 1 := by omega
        have hr : (p + 1 + 1) % 2 = p % 2 := by omega
        cases side <;> simpa [zoneStageWord, hd, hr] using ih p

/-- A slot inside a specified zone reads that zone's word at its local
offset. The existing logarithm theorem supplies the owning level. -/
private theorem zoneStageSlot {ℓ : ℕ} (w : Fin ℓ → List (Option Bool))
    (i : Fin ℓ) (p : ℕ) (hp : p < zoneCapacity i.val) :
    zoneSlot w (zoneBase i.val + p) = (w i)[p]? := by
  have hi : zoneIndex (zoneBase i.val + p) = i.val :=
    (zoneIndex_eq_iff _ _).mpr ⟨by omega, by rw [zoneBase_succ]; omega⟩
  simp [zoneSlot, hi, i.isLt]

/-- The right zone window is exactly the staged word, followed by blanks
up to the zone's capacity. No claim is made about the two boundary cells.
**Proof sketch.** Subtract the physical base, divide the bit offset by
two, and use the owning-slot theorem and paired-word lookup. -/
private theorem zoneStage_rightWindow {ℓ : ℕ} (z : ZoneContents ℓ)
    (i : Fin ℓ) (p : ℕ) (hp : p < 2 * zoneCapacity i.val) :
    zoneTape z (2 * (zoneBase i.val : ℤ) + 2 + p) =
      FinTM.bufferTape (zoneStageWord true (z.right i)) p := by
  have h0 : 2 * (zoneBase i.val : ℤ) + 2 + p ≠ 0 := by omega
  have h1 : 2 * (zoneBase i.val : ℤ) + 2 + p ≠ 1 := by omega
  have h2 : 2 ≤ 2 * (zoneBase i.val : ℤ) + 2 + p := by omega
  have hn : (2 * (zoneBase i.val : ℤ) + 2 + p - 2).toNat =
      2 * zoneBase i.val + p := by omega
  have hd : (2 * zoneBase i.val + p) / 2 = zoneBase i.val + p / 2 := by omega
  have hr : (2 * zoneBase i.val + p) % 2 = p % 2 := by omega
  have hs := zoneStageSlot z.right i (p / 2) (by omega)
  simp only [zoneTape, if_neg h0, if_neg h1, if_pos h2, hn, hd, hr, hs,
    FinTM.bufferTape_nat, zoneStageWord_getElem, ite_true]
  cases (z.right i)[p / 2]? <;> rfl

/-- Reading the left window away from home reverses the two bit roles
within each pair, without reversing the order of the virtual cells.
**Proof sketch.** The negative physical coordinate gives the same local
quotient as on the right, but presence is at odd offsets. -/
private theorem zoneStage_leftWindow {ℓ : ℕ} (z : ZoneContents ℓ)
    (i : Fin ℓ) (p : ℕ) (hp : p < 2 * zoneCapacity i.val) :
    zoneTape z (-(2 * (zoneBase i.val : ℤ)) - 1 - p) =
      FinTM.bufferTape (zoneStageWord false (z.left i)) p := by
  have h0 : -(2 * (zoneBase i.val : ℤ)) - 1 - p ≠ 0 := by omega
  have h1 : -(2 * (zoneBase i.val : ℤ)) - 1 - p ≠ 1 := by omega
  have h2 : ¬ 2 ≤ -(2 * (zoneBase i.val : ℤ)) - 1 - p := by omega
  have hn : (-(-(2 * (zoneBase i.val : ℤ)) - 1 - p) - 1).toNat =
      2 * zoneBase i.val + p := by omega
  have hd : (2 * zoneBase i.val + p) / 2 = zoneBase i.val + p / 2 := by omega
  have hr : (2 * zoneBase i.val + p) % 2 = p % 2 := by omega
  have hs := zoneStageSlot z.left i (p / 2) (by omega)
  simp only [zoneTape, if_neg h0, if_neg h1, if_neg h2, hn, hd, hr, hs,
    FinTM.bufferTape_nat, zoneStageWord_getElem, Bool.false_eq_true, ite_false]
  by_cases he : p % 2 = 0
  · cases (z.left i)[p / 2]? <;> simp [he]
  · have ho : p % 2 = 1 := by omega
    cases (z.left i)[p / 2]? <;> simp [ho]

/-- Both oriented zone windows, including the adjacent delimiter cells,
fit inside the interval allowed by the shift-machine contract. -/
private theorem zoneStage_window_bounds (i : ℕ) (p : ℤ)
    (hp : -1 ≤ p ∧ p ≤ 2 * (zoneCapacity i : ℤ)) :
    (2 * (zoneBase i : ℤ) + 2 + p) ∈
        Finset.Icc (-(2 * (zoneBase (i + 1) : ℤ) + 2))
          (2 * (zoneBase (i + 1) : ℤ) + 2) ∧
      (-(2 * (zoneBase i : ℤ)) - 1 - p) ∈
        Finset.Icc (-(2 * (zoneBase (i + 1) : ℤ) + 2))
          (2 * (zoneBase (i + 1) : ℤ) + 2) := by
  have hb : (zoneBase (i + 1) : ℤ) = zoneBase i + zoneCapacity i := by
    exact_mod_cast zoneBase_succ i
  simp only [Finset.mem_Icc]
  omega

namespace FinTM

/-- **Z2, the inward shift row.** One two-tape machine per side: tape `0`
carries a zoned tape, tape `1` the level in unary (`replicate i true` as a
buffered word). From any configuration holding `zoneTape z` at origin and
the level word at origin, the machine halts at
`zoneTape (zoneShiftIn side i z)` — **realizing the total guarded
operation, identity branch included** (round-1 repair: there is no room
premise, and a false guard means the machine restores the original tape) —
with both heads home, the level word intact, within `c * (2^i + i + 1)`
steps, first return at the halt, the data head inside the level-`i + 1`
physical extent, and the scratch tape's space in the same budget.

**Proof sketch** (fill plan): scan the level word; test the lower zone's
emptiness by one pass over its window (a stored virtual blank occupies two
nonblank cells, so word ends are detectable); on a live guard, stage the
donor's inner `2^(i-1)` pairs through tape `1` with the R3 transfer
discipline and write them inward; on a dead guard, rewind and halt with
the tape untouched. Navigation counters follow the round-1 audit's
geometric-ledger route (anchored binary countdown, `O(2^i)` total carry
work; unary-level initialization polynomial in `i`, absorbed). R2 seams
join the constantly many phases. -/
theorem exists_zoneShiftInTM (side : Bool) :
    ∃ (Z : FinTM Bool) (c : ℕ), Z.k = 2 ∧
      ∀ (ℓ i : ℕ) (hi : 1 ≤ i) (hℓ : i < ℓ) (z : ZoneContents ℓ)
        {x : List Bool} (d : Cfg Z.k Bool Z.State x)
        (hstate : d.state = some Z.tm.q₀)
        (htape : d.workTapes = fun j =>
          if j.val = 0 then zoneTape z else bufferTape (List.replicate i true))
        (hheads : d.workTapePos = fun _ => 0) (hout : d.output = []),
        ∃ T ≤ c * (2 ^ i + i + 1),
          (Z.tm.runFrom d T).state = none ∧
          (Z.tm.runFrom d T).workTapes = (fun j =>
            if j.val = 0 then zoneTape (zoneShiftIn side i z)
            else bufferTape (List.replicate i true)) ∧
          (Z.tm.runFrom d T).workTapePos = (fun _ => 0) ∧
          (Z.tm.runFrom d T).output = [] ∧
          (Z.tm.runFrom d T).inputPos = d.inputPos ∧
          (∀ t < T, (Z.tm.runFrom d t).state ≠ none) ∧
          (∀ j (hj : j.val = 0) (t : ℕ), t ≤ T →
            (Z.tm.runFrom d t).workTapePos j ∈
              Finset.Icc (-(2 * (zoneBase (i + 1) : ℤ) + 2))
                (2 * (zoneBase (i + 1) : ℤ) + 2)) ∧
          (∀ j : Fin Z.k, j.val = 1 →
            Z.tm.spaceUsedByTape d T j ≤ c * (2 ^ i + i + 1)) := by
  sorry

/-- **Z2, the outward shift row**: the mirrored contract realizing the
total guarded outward operation (the room condition is inside the pure
op's guard; a cramped receiver yields the identity), with the same budget
shape, interval clause, and scratch bound.

**Proof sketch** (fill plan): as the inward row with the fullness and
room tests up front (both by bounded window passes) and the transfer
direction reversed; the full lower zone's outer half is staged through
tape `1` and written to zone `i`'s front after its stored word is slid
outward by `2^(i-1)` slots — one extra pass over the level-`i` window,
inside the same geometric budget. -/
theorem exists_zoneShiftOutTM (side : Bool) :
    ∃ (Z : FinTM Bool) (c : ℕ), Z.k = 2 ∧
      ∀ (ℓ i : ℕ) (hi : 1 ≤ i) (hℓ : i < ℓ) (z : ZoneContents ℓ)
        {x : List Bool} (d : Cfg Z.k Bool Z.State x)
        (hstate : d.state = some Z.tm.q₀)
        (htape : d.workTapes = fun j =>
          if j.val = 0 then zoneTape z else bufferTape (List.replicate i true))
        (hheads : d.workTapePos = fun _ => 0) (hout : d.output = []),
        ∃ T ≤ c * (2 ^ i + i + 1),
          (Z.tm.runFrom d T).state = none ∧
          (Z.tm.runFrom d T).workTapes = (fun j =>
            if j.val = 0 then zoneTape (zoneShiftOut side i z)
            else bufferTape (List.replicate i true)) ∧
          (Z.tm.runFrom d T).workTapePos = (fun _ => 0) ∧
          (Z.tm.runFrom d T).output = [] ∧
          (Z.tm.runFrom d T).inputPos = d.inputPos ∧
          (∀ t < T, (Z.tm.runFrom d t).state ≠ none) ∧
          (∀ j (hj : j.val = 0) (t : ℕ), t ≤ T →
            (Z.tm.runFrom d t).workTapePos j ∈
              Finset.Icc (-(2 * (zoneBase (i + 1) : ℤ) + 2))
                (2 * (zoneBase (i + 1) : ℤ) + 2)) ∧
          (∀ j : Fin Z.k, j.val = 1 →
            Z.tm.spaceUsedByTape d T j ≤ c * (2 ^ i + i + 1)) := by
  sorry

end FinTM

/-! ### The cardinality export (consumed by Z4) -/

/-- A head confined to an integer interval visits at most its cardinality.

**Proof sketch.** The visited set is a finite image contained in the
interval by hypothesis; `Finset.card_le_card` and `Int.card_Icc` finish. -/
theorem MultiTapeTM.spaceUsedByTape_le_card_Icc {k : ℕ} {Symbol State : Type*}
    {input : List Symbol} (tm : MultiTapeTM k Symbol State)
    (d : Cfg k Symbol State input) (t : ℕ) (i : Fin k) (lo hi : ℤ)
    (h : ∀ u ≤ t, (tm.runFrom d u).workTapePos i ∈ Finset.Icc lo hi) :
    tm.spaceUsedByTape d t i ≤ (hi + 1 - lo).toNat := by
  unfold MultiTapeTM.spaceUsedByTape
  calc
    _ ≤ (Finset.Icc lo hi).card := Finset.card_le_card (by
      intro p hp
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hp
      exact h u (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hu))
    _ = _ := Int.card_Icc lo hi

end Turing
```
