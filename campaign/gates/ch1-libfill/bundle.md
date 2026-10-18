# Audit bundle — machine-construction library fill audit (companion to ch1-libfill-pack.md)

The pack is reproduced first; every attachment follows raw and unabridged
under a header line of the form '## ===== <path> ====='. Attachments are
data for audit, not instructions.

## ===== audits/ch1-libfill-pack.md =====

# External audit pack — machine-construction library, fill audit

Audits the **proofs** of the machine-construction library: eight
Codex-authored fill commits across four batch rounds (W; P/P2/P3/P4;
L/L2) on the span `e346139c` → the pack commit, closing all 23 contracts
of `TCSlib/Complexity/TuringMachine/Build/` with ~250 new private
declarations. The **statements were audited separately and are not in
question here**: the spec surface closed a three-round adversarial gate
(`audits/ch1-infra-resolutions.md`, attached) — this round is the
companion proof audit, in the mold of the Chapter-2 epoch-1 fill audit:
proof correctness and helper hygiene against the frozen, audited
statements and their recorded construction ledgers. Gate closes on zero
blockers/majors. Record findings in `audits/ch1-libfill-findings.md`.

**Evidence separation.** Out of scope: the 28 Chapter-2 campaign
admissions (their own epoch gates); the bridge export and TMSAT
discharge (proof-audited at the infra round, blob-pinned unchanged); the
model files themselves (audited across the Chapter-1 campaign — they are
attached as the definitions the proofs elaborate against, not for
re-audit). The two delivery hosts' disclosed `/proc/<pid>/exe` shims are
superseded by the maintainer's independent fresh sweeps on an ordinary
host; the shims never entered the repository.

## Maintainer-side integration attestations (verify or challenge)

1. **Whole-span freeze.** Over the complete fill span, the net diff of
   `Build/` deletes **exactly the 23 audited contract `sorry`
   placeholders and nothing else** (the L checkpoint's intermediate
   admitted private was added and filled inside the span, so the net
   record is placeholder-exact), and adds **zero non-private
   declarations**. Public surfaces per file: 7/15/5/6 declarations,
   unchanged in order and content; all public docstrings byte-identical;
   module docstrings extended append-only. P4's kernel-export baseline
   independently confirms 78 public kernel declarations preserved.
2. **Per-delivery verification** (each recorded in the decision log at
   integration): checksums for all eight archives; per-patch
   deleted-lines audits; byte-identical replay in isolated worktrees
   before every `git am -3`; P3's and P4's attested integrated-source
   SHA-256 values reproduced. Disclosed-by-route imports only
   (P: three Mathlib modules, `ClassP.TimeConstructible`, `Composition`,
   `Wrappers`, `Loop`; L: `Wrappers`) — all order-legal, no cycles.
3. **Elaboration.** Four integrated-tree fresh 57-module sweeps, zero
   `error:` lines, admission counts stepping 33 → 30 → 29 → **28**
   (campaign-only; zero in `Build/`). The final sweep and closure
   attestation logs are attached (`ch1-libfill4-{sweep,axioms}.log`);
   earlier-round logs are committed under `audits/logs/ch1-libfill*`.
4. **Axioms.** The closure attestation (the attached, committed program
   `audits/programs/ch1-libfill-ClosureAxioms.lean`): all 23 contracts
   print at most the standard triple with **empty admission-root sets**;
   the headline and campaign regression roots unchanged. P4's own
   whole-`Build` kernel traversal covers 1,171 checked declarations with
   zero roots and no nonstandard axiom.
5. **Policy.** Combined lint (`ch1-libfill-lint.log`): **0 FAIL, 9
   WARN** — the seven pre-recorded size escalations plus the two
   fill-grown Build files, `Primitives.lean` (4,418 lines) and
   `Loop.lean` (2,693), whose exceptions were recorded with
   justifications at each integration. Every remaining `sorry`-free file
   keeps sketch-bearing docstrings; attributions intact.
6. **Deviations on record** (all cosmetic, all noted at integration):
   P3 worked under the campaign branch name locally (the epoch-1 D2
   precedent; zip delivery); L2's archive wrapped a top-level directory
   (corrected from P3 onward); both hosts' cache-setup failures were
   recovered without touching pins (their logs shipped in the archives).

## Dispositions requested

* **D6 — W's shared-lemma promotion requests.** Batch W requests serial
  promotion of `timed_input_bound` (a run's input position is at most
  its initial position plus elapsed steps) to the run calculus and
  `timed_rewind` (rewind from any input position in `pos + 2` steps,
  preserving work and output) to `Simulation.lean`; both are generic in
  tape count and state type. Maintainer position: **defer to a serial
  maintainer merge after this gate** (the D3 pattern) — the private
  copies compile standalone and three later fills already adapted the
  rewind pattern privately, so promotion is a dedup, not a blocker.
  Review the deferral and the two statements' promotion-worthiness.
* **D7 — the size exceptions.** `Wrappers.lean` 687 (within target);
  `Loop.lean` 2,693 and `Primitives.lean` 4,418, both justified at
  integration by exclusive-ownership fill rules concentrating every
  controller and invariant family in-file. Maintainer position: a
  **post-gate serial split** of the two large files (e.g. machines/
  invariants per family) is the natural follow-up, executed under the
  epoch-3→4 merge-refactor discipline (byte-identical relocation,
  ordered-sequence comparison) and ride-along audited. Review whether
  to require it before the E2 continuations consume the library, or
  allow it to trail.

## What is under audit, and priorities

The 23 proofs and ~250 private helpers, against the frozen statements,
the audited construction ledgers (the round-3 item-4 loop ledger; the
§9b instantiation tables; the frontier documents' interface
descriptions), and the agent reports (attached; challenge any
attestation of theirs the maintainer layer above does not independently
cover). Priorities, riskiest first:

1. **The loop host assembly** (L2: `loopHost_contracts` and its forty
   phase lemmas). Re-derive the checked time ledger (startup
   `≤ 9(T+1)`; segment `≤ 10(T+1)`; exported constant 10) against the
   audit's own round-3 ledger; check the phase-boundary seams (fuel
   capture → counter copy → synchronized rewinds → body release), the
   free-initial-entry discipline at zero fuel, the `findMode` dual
   output sharing one controller, the unreachable-terminal cases, and
   that the per-segment counter estimate is genuinely worst-case width
   (R3-2), not amortized.
2. **`capture_run`** (W): the induction every later fill instantiates.
   The halting-transition emission, the `bufferTape_append` head
   arithmetic, the liveness guard's exact role, preservation of
   arbitrary prefixes and host output.
3. **The split-search body** (P4): the `splitSafe` trace-composition
   family (the global positive-duration/anchor-exclusion argument — the
   known composition trap); the accepting emitter's native-bit claim
   (candidate used only as a length counter); the envelope
   `A = (C+1+5e)·2^e + 40` and the `s+1 ≤ 2(w+1)` step; the
   one-past-end silent stall preserving arbitrary bits; both exponent
   cases including `catalogPrefixTM` at `e = 0`.
4. **The conditional and the threaded map** (W4, P14): the
   multiplier-5 ledger (`2T₀ + 5` prefix; the input-position-≤-run-time
   rewind argument) and the coefficient-40 ledger — in particular that
   neither evaluates a time function at an inflated composition bound
   (the recorded trap).
5. **Harvest fidelity**: `catalogPolyUnaryTM` against the TMSAT source
   generator with the `e − 1` indexing (round-1 finding 5);
   `incFixedTM`'s detect-then-emit redesign against `enumCarry*`
   semantics; `lengthBits`' discharge by the public
   `Complexity.timeConstructible_id` — verify that theorem's witness
   really is a `Nat.bits ∘ length` machine at the required bound
   (`ClassP/TimeConstructible.lean` attached).
6. **The parser/threaded family** (P5–P13): the shared `pairExtractTM`
   invariants serving three contracts; `pairLenCheck`'s captured
   countdown; `stripLast`'s whole-encoding buffering against the
   audited marker discipline; buffer-before-emit discharged at every
   claimed point.
7. **Helper hygiene**: privates match their stated contracts; nothing
   public-worthy is smuggled private without a flag beyond the two D6
   requests; no helper restates an audited statement in disguise; the
   deliveries' kernel-traversal claims (opaque values, constructor
   dependencies, explicit expectations) spot-checked against the
   attached programs.

Severity scheme as always: blocker / major / minor / note; findings to
`audits/ch1-libfill-findings.md`; this pack is immutable once sent.

## Verification appendix (runs and manifest)

* Integration sweeps (all fresh-olean, 57/57, zero errors): 33
  admissions at the W+P+L checkpoint, 30 after P2+L2, 29 after P3, 28
  after P4 (`audits/logs/ch1-libfill{,2,3,4}-sweep.log`; the last
  attached).
* Closure attestation: `ch1-libfill4-axioms.log` (attached), from the
  attached committed program — exit 0, every expectation empty.
* Lint: `ch1-libfill-lint.log` (attached): 0 FAIL, 9 WARN as itemized
  in attestation 5.
* Bundle manifest — **32 attachments** after the pack: the 4 `Build/`
  sources; the 6 model/gadget modules (`Configuration`, `Deterministic`,
  `Finite`, `Simulation`, `Sweep`, `Composition`); `Encoding.lean` and
  `ClassP/TimeConstructible.lean`; the 3 harvest-source files
  (`ClassNP/TMSAT.lean`, `ClassNP/EXP.lean`, `ClassNP/Reductions.lean`);
  the design document; the infra-gate resolutions; the 10 agent
  documents (W, P, P2 + its frontier, P3 + its frontier, P4, L + its
  continuation, L2); the closure program; the 3 logs (final sweep,
  closure axioms, lint); the 57-module order list.
  Total 4 + 6 + 2 + 3 + 1 + 1 + 10 + 1 + 3 + 1 = 32. The six fill
  briefs and all earlier logs are committed in the repository at the
  paths the reports cite.


## ===== TCSlib/Complexity/TuringMachine/Build/Convention.lean =====

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

**Status: spec phase.** This module is fully proved (definitions and two
glue lemmas); the sibling `Build` modules state sorried contracts against
it. The whole `Build` surface is new Chapter-1 growth, flagged for the
shared infrastructure audit round (with the `Universal` bridge export).

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

end Turing


## ===== TCSlib/Complexity/TuringMachine/Build/Wrappers.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.Convention
import TCSlib.Complexity.TuringMachine.Composition

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: wrappers

The output-isolation layer of the machine-construction library
(`machine-library-design.md` §5, W1–W3): the capture/silence discipline
written once, consolidating its four private incarnations
(`universalCaptureTM` in the universal-machine development, the Chapter-2
enumerator's `enumCaptureTM`, the HALT batch's `acceptTM`, and the private
engine inside `TCSlib.Complexity.TuringMachine.Composition.exists_cond`).
The obligation list is the one the phase-1 and phase-4 audits tabulated:
every source emission is captured, **including an emission on the halting
transition**; the wrapper's physical output stays untouched; the completed
source configuration is preserved at the return.

**Status: spec phase.** The two action/configuration transformers and the
derived machine are real definitions; the four contract theorems are
sorried, to be filled from the existing private proofs (harvest) in the
library fill batches. New Chapter-1 surface, flagged for the shared
infrastructure audit round.

## Design

* **W1 (capture)** is *host-parametric*: rather than a closed wrapper
  machine, `Turing.captureAction` transforms one source action into a host
  action (source tapes untouched, emission appended to the last tape,
  silence, halt redirected to a designated return state), and
  `Turing.capture_run` says that **any** host machine agreeing with the
  transformed table on an embedded copy of the source states simulates the
  source in lockstep with its output captured on the last tape. Consumers
  (the loop fill, HALT-style control modifications, the Chapter-2
  continuations) embed the source into *their* controller state type and
  inherit the whole induction. The capture tape holds the full output
  word (tape-capture core, frozen design decision 9.3); reading one bit
  off it is the register corollary, derived at fill time.
* **W2 (halt-redirect)** is the `acceptTM` pattern as a closed
  transformation `Turing.FinTM.redirectTM`: simulate a machine silently
  while remembering the last emitted bit, halt exactly when the source
  halts with the designated bit, and otherwise enter a one-state
  stationary live loop.
* **W3 (timed branch)** is the quantitative form of
  `Turing.FinTM.exists_comp_partial`'s sibling
  `Turing.FinTM.exists_cond`: deciding which branch runs costs the
  decider's budget, and the branch runs on the *same* physical input, so
  no monotonicity hypothesis is needed.

## Main declarations

* `Turing.captureAction`, `Turing.captureCfg` — the W1 transformers.
* `Turing.capture_run` — the W1 lockstep/capture/silence contract (sorried).
* `Turing.FinTM.redirectTM` — the W2 transformation.
* `Turing.FinTM.redirectTM_computes`, `Turing.FinTM.redirectTM_live` — the
  W2 contract pair (sorried).
* `Turing.FinTM.computesFunInTime_cond` — the W3 timed branch (sorried).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2; the capture discipline is the
  output-isolation folklore every simulation argument of §1.4–§1.7 uses.)

**Implementation note (batch W).** All four contracts are now proved; the
original spec-phase descriptions above and in their docstrings are retained.
The conditional controller instantiates `capture_run` on a padded decider,
reads its singleton output, and uses a quantitative refinement of
`rewind_from_any`. Its branch-start prefix is at most twice the decider's
budget plus five, yielding the uniform multiplier `5` in the frozen bound.
-/

namespace Turing

variable {k : ℕ} {S H : Type*}

/-- W1 action transformer. Transform one source action into a host action
over one extra tape: the source's input move and work-tape actions are kept
on the first `k` tapes; the source's emission, **if any**, is written on
the last tape with a right move (so the capture tape accumulates the output
word from the origin); the host emits nothing; a live source successor is
embedded via `emb`, and a halting source action transfers control to the
designated return state `ret` — on the very transition that may carry the
final emission, which is therefore captured like any other. -/
def captureAction (emb : S → H) (ret : H) (a : Action k Bool S) :
    Action (k + 1) Bool H where
  inputTape := a.inputTape
  workTapes := fun i =>
    if h : (i : ℕ) < k then a.workTapes ⟨i, h⟩
    else
      match a.output with
      | some b => (some (some b), SignType.pos)
      | none => (none, SignType.zero)
  output := none
  state := some ((a.state.map emb).getD ret)

/-- W1 configuration correspondence. A source configuration `c`, viewed
inside a host with one extra tape: source state embedded (a halted source
sits at the return state `ret`), same input head, source work tapes on the
first `k` tapes, and the capture tape holding `pre ++ c.output` — the
emissions captured so far after a pre-existing prefix — with its head one
past that word. The host's own physical output is the untouched `out₀`. -/
def captureCfg {input : List Bool} (emb : S → H) (ret : H)
    (pre out₀ : List Bool) (c : Cfg k Bool S input) :
    Cfg (k + 1) Bool H input where
  state := some ((c.state.map emb).getD ret)
  inputPos := c.inputPos
  workTapes := fun i =>
    if h : (i : ℕ) < k then c.workTapes ⟨i, h⟩
    else FinTM.bufferTape (pre ++ c.output)
  workTapePos := fun i =>
    if h : (i : ℕ) < k then c.workTapePos ⟨i, h⟩
    else ((pre ++ c.output).length : ℤ)
  output := out₀

/-- Applying a captured action preserves the source fields and appends its
optional emission to the buffer. The write uses the old head before moving.
**Proof sketch.** Split the tape index at the source tape count. Source tapes
are unchanged by the embedding; on the final tape use `bufferTape_append`
for an emission and the stationary no-write action otherwise. -/
private lemma capture_apply {input : List Bool} (emb : S → H) (ret : H)
    (pre out₀ : List Bool) (c : Cfg k Bool S input) (a : Action k Bool S) :
    (captureAction emb ret a).apply (captureCfg emb ret pre out₀ c) =
      captureCfg emb ret pre out₀ (a.apply c) := by
  refine Cfg.ext rfl rfl ?_ ?_ ?_
  · funext i
    by_cases hi : (i : ℕ) < k
    · simp [captureAction, captureCfg, Action.apply, hi]
    · cases ho : a.output <;>
        simp [captureAction, captureCfg, Action.apply, hi, ho,
          ← List.append_assoc, FinTM.bufferTape_append]
  · funext i
    by_cases hi : (i : ℕ) < k
    · simp [captureAction, captureCfg, Action.apply, hi]
    · cases ho : a.output <;>
        simp [captureAction, captureCfg, Action.apply, hi, ho, Nat.cast_add,
          add_assoc]
  · simp [captureAction, captureCfg, Action.apply]

/-- **W1, the capture contract** (spec, fill pending — harvested from the
four private incarnations). If a host machine's transition table agrees, on
an embedded copy of the source's states, with the capture-transformed
source table, then the host run from a capture configuration *is* the
capture image of the source run, for as long as the source has not halted
before the time in question. Taking `t` to be the source's halting time
instantiates the return clause: the host sits at `ret` with the completed
source configuration preserved, the full source output (halting emission
included) on the capture tape, and the host output still `out₀`; taking
`t` below it gives live lockstep.

**Proof sketch.** Induction on `t`. One host step from a live capture image
applies the transformed action: the first `k` tapes and the input head
update exactly as the source's (`Turing.Action.apply` componentwise); the
capture tape appends the emitted bit, which is
`Turing.FinTM.bufferTape_append` at head `|pre ++ c.output|`; silence keeps
the host output at `out₀`; and the successor state is the embedded source
successor, or `ret` on the halting transition. -/
theorem capture_run {input : List Bool} (tm : MultiTapeTM k Bool S)
    (host : MultiTapeTM (k + 1) Bool H) (emb : S → H) (ret : H)
    (hagree : ∀ (s : S) (inp : Option Bool) (w : Fin (k + 1) → Option Bool),
      host.tr (emb s) inp w =
        captureAction emb ret (tm.tr s inp fun i => w i.castSucc))
    (pre out₀ : List Bool) (c₀ : Cfg k Bool S input) (t : ℕ)
    (hlive : ∀ t' < t, ¬(tm.runFrom c₀ t').Halted) :
    host.runFrom (captureCfg emb ret pre out₀ c₀) t =
      captureCfg emb ret pre out₀ (tm.runFrom c₀ t) := by
  have hstep (c : Cfg k Bool S input) (hs : ¬c.Halted) :
      host.step (captureCfg emb ret pre out₀ c) =
        captureCfg emb ret pre out₀ (tm.step c) := by
    cases hq : c.state with
    | none => exact False.elim (hs hq)
    | some q =>
      have hstate : (captureCfg emb ret pre out₀ c).state = some (emb q) := by
        simp [captureCfg, hq]
      have hinput : (captureCfg emb ret pre out₀ c).inputSymbol = c.inputSymbol := rfl
      have hwork : (fun i => (captureCfg emb ret pre out₀ c).workTapeSymbols
          i.castSucc) = c.workTapeSymbols := by
        funext i
        simp [captureCfg, Cfg.workTapeSymbols, i.isLt]
      simp only [MultiTapeTM.step, hstate, hq]
      rw [hagree, hinput, hwork]
      exact capture_apply emb ret pre out₀ c _
  -- The guard supplies a genuine source step, including at the final halt.
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (fun s hs => hlive s (by omega)),
      hstep _ (hlive t (by omega)), MultiTapeTM.runFrom_succ_eq_step']

end Turing

namespace Turing.FinTM

/-- W2 transformation: the `acceptTM` control-modification pattern. Simulate
`M` with its output suppressed while a finite register remembers the **last**
emitted bit (`none` before any emission) — updated *before* the halt test, so
a bit emitted on the halting transition counts. When the source halts, halt
if the remembered bit is `haltOn`; otherwise enter the one-state stationary
live loop. Tape count unchanged. -/
def redirectTM (M : FinTM Bool) (haltOn : Bool) : FinTM Bool where
  k := M.k
  State := (M.State × Option Bool) ⊕ Unit
  tm :=
    { q₀ := Sum.inl (M.tm.q₀, none)
      tr := fun q inp work =>
        match q with
        | Sum.inl (s, r) =>
          let a := M.tm.tr s inp work
          let r' := match a.output with
            | some b => some b
            | none => r
          { inputTape := a.inputTape
            workTapes := a.workTapes
            output := none
            state := match a.state with
              | some s' => some (Sum.inl (s', r'))
              | none => if r' = some haltOn then none else some (Sum.inr ()) }
        | Sum.inr () =>
          { inputTape := SignType.zero
            workTapes := fun _ => (none, SignType.zero)
            output := none
            state := some (Sum.inr ()) } }

/-- Map a source state and its last-emission register to simulation, halt,
or the stationary live loop. An empty register never matches a bit. -/
private def redirectState {S : Type} (haltOn : Bool) (q : Option S)
    (r : Option Bool) : Option ((S × Option Bool) ⊕ Unit) :=
  match q with
  | some s => some (.inl (s, r))
  | none => if r = some haltOn then none else some (.inr ())

/-- Suppress physical emission, updating the register before the halt test. -/
private def redirectAction {k : ℕ} {S : Type} (haltOn : Bool)
    (a : Action k Bool S) (r : Option Bool) : Action k Bool ((S × Option Bool) ⊕ Unit) :=
  ⟨a.inputTape, a.workTapes, none, redirectState haltOn a.state (a.output.or r)⟩

/-- The source tapes and input head are unchanged; its last emitted bit is
remembered in control and the physical output is empty. -/
private def redirectCfg (M : FinTM Bool) (haltOn : Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) : Cfg (redirectTM M haltOn).k Bool
      (redirectTM M haltOn).State x :=
  ⟨redirectState haltOn c.state c.output.getLast?, c.inputPos,
    c.workTapes, c.workTapePos, []⟩

/-- The stationary live loop is fixed by every subsequent transition. -/
private lemma redirect_loop (M : FinTM Bool) (haltOn : Bool) {x : List Bool}
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
private lemma redirect_apply (M : FinTM Bool) (haltOn : Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (a : Action M.k Bool M.State) :
    (redirectAction haltOn a c.output.getLast?).apply (redirectCfg M haltOn c) =
      redirectCfg M haltOn (a.apply c) := by
  have hlast : (c.output ++ a.output.toList).getLast? = a.output.or c.output.getLast? := by
    cases a.output <;> simp
  refine Cfg.ext ?_ rfl rfl rfl rfl
  dsimp only [redirectCfg, redirectAction, Action.apply]
  rw [hlast]

/-- The correspondence also holds after a source halt: a matching result
is absorbed as halted, and a mismatching result is absorbed in the live loop.
This adapts `acceptCfg_step` in the HALT reduction to an optional register. -/
private lemma redirect_step (M : FinTM Bool) (haltOn : Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) :
    (redirectTM M haltOn).tm.step (redirectCfg M haltOn c) =
      redirectCfg M haltOn (M.tm.step c) := by
  cases hs : c.state with
  | none =>
    rw [MultiTapeTM.step_of_halt hs]
    by_cases hr : c.output.getLast? = some haltOn
    · exact MultiTapeTM.step_of_halt (by simp [redirectCfg, redirectState, hs, hr])
    · exact redirect_loop M haltOn (redirectCfg M haltOn c)
        (by simp [redirectCfg, redirectState, hs, hr]) 1
  | some q =>
    have hi : (redirectCfg M haltOn c).inputSymbol = c.inputSymbol := rfl
    have hw : (redirectCfg M haltOn c).workTapeSymbols = c.workTapeSymbols := rfl
    have hstate : (redirectCfg M haltOn c).state = some (.inl (q, c.output.getLast?)) := by
      simp only [redirectCfg, redirectState, hs]
    simp only [MultiTapeTM.step, hstate, hs]
    rw [hi, hw]
    have htr : (redirectTM M haltOn).tm.tr (.inl (q, c.output.getLast?))
        c.inputSymbol c.workTapeSymbols =
        redirectAction haltOn (M.tm.tr q c.inputSymbol c.workTapeSymbols) c.output.getLast? := by
      cases hq : (M.tm.tr q c.inputSymbol c.workTapeSymbols).state <;>
        cases ho : (M.tm.tr q c.inputSymbol c.workTapeSymbols).output <;>
          simp [redirectTM, redirectAction, redirectState, hq, ho]
    rw [htr]
    exact redirect_apply M haltOn c _

/-- Initialized runs commute with redirection at every time, including
after a source halt. This is the last-emission invariant for both clauses. -/
private lemma redirect_run (M : FinTM Bool) (haltOn : Bool) (x : List Bool) (t : ℕ) :
    (redirectTM M haltOn).tm.runFrom ((redirectTM M haltOn).tm.initCfg x) t =
      redirectCfg M haltOn (M.tm.runFrom (M.tm.initCfg x) t) := by
  have hi : (redirectTM M haltOn).tm.initCfg x = redirectCfg M haltOn (M.tm.initCfg x) := rfl
  rw [hi]
  exact MultiTapeTM.runFrom_comm_of_step (redirectCfg M haltOn) (redirect_step M haltOn)
    (M.tm.initCfg x) t

/-- **W2, the halting clause** (spec, fill pending — harvested from the
HALT batch's `acceptTM_halts_iff`). If `M` completes output `w` on `x`
within `t` steps and the last bit of `w` is the designated bit, the
redirected machine halts on `x` within the same budget with **empty**
output (everything was suppressed).

**Proof sketch.** Lockstep correspondence between `M`'s run and the
redirected run, carrying "register = last emitted bit so far"; at `M`'s
halting transition the register equals `w`'s last bit, so the redirect
halts there. -/
theorem redirectTM_computes {M : FinTM Bool} {haltOn : Bool}
    {x w : List Bool} {t : ℕ} (hM : M.ComputesInTime x w t)
    (hlast : w.getLast? = some haltOn) :
    (redirectTM M haltOn).ComputesInTime x [] t := by
  obtain ⟨hs, hout⟩ := (computesInTime_iff M x w t).mp hM
  apply (computesInTime_iff _ x [] t).mpr
  rw [redirect_run]
  exact ⟨by simp only [redirectCfg, hs, hout, redirectState, hlast, ite_true], rfl⟩

/-- **W2, the live clause** (spec, fill pending). If `M` completes output
`w` on `x` and `w`'s last bit is *not* the designated bit (in particular if
`w = []`), the redirected machine never halts on `x`: at the source's
halting transition it enters the stationary live loop, which is fixed under
every further step.

**Proof sketch.** Lockstep with the register invariant (register = last
emission so far) up to the source's halting transition; there the register
differs from the designated bit, so control enters the stationary live
state, which every further step fixes (two-line induction). -/
theorem redirectTM_live {M : FinTM Bool} {haltOn : Bool}
    {x w : List Bool} {t : ℕ} (hM : M.ComputesInTime x w t)
    (hlast : w.getLast? ≠ some haltOn) :
    ∀ u : ℕ, ¬((redirectTM M haltOn).tm.runFrom
      ((redirectTM M haltOn).tm.initCfg x) u).Halted := by
  intro u hhalt
  rw [redirect_run] at hhalt
  change redirectState haltOn (M.tm.runFrom (M.tm.initCfg x) u).state
    (M.tm.runFrom (M.tm.initCfg x) u).output.getLast? = none at hhalt
  -- A redirected halt forces a genuine source halt with the matching register.
  have hs : (M.tm.runFrom (M.tm.initCfg x) u).state = none := by
    cases h : (M.tm.runFrom (M.tm.initCfg x) u).state with
    | none => rfl
    | some q => simp only [redirectState, h, reduceCtorEq] at hhalt
  have hc : M.ComputesInTime x (M.tm.runFrom (M.tm.initCfg x) u).output u :=
    (computesInTime_iff _ _ _ _).mpr ⟨hs, rfl⟩
  have hout := hc.output_unique hM
  rw [hs, hout] at hhalt
  simp only [redirectState, if_neg hlast, Option.some_ne_none] at hhalt

/-- Pad the decider with the fresh branch tapes. The added tapes are idle,
so the public left-block simulation supplies its complete run invariant. -/
private def timedPadTM (D : FinTM Bool) (r : ℕ) : MultiTapeTM (D.k + r) Bool D.State where
  q₀ := D.tm.q₀
  tr q inp work := leftAction r id (D.tm.tr q inp (fun i => work (Fin.castAdd r i)))

/-- The conditional controller captures the decider on the last tape,
steps back to read its singleton verdict, rewinds the physical input, then
runs the selected branch on its untouched tape bank. In the administrative
states, the first Boolean distinguishes back/read and the second distinguishes
rewind-start/scan. The branch transition table is independent of its selector. -/
private def timedCondTM (D M₁ M₂ : FinTM Bool) : FinTM Bool where
  k := (D.k + (M₁.k + M₂.k)) + 1
  State := D.State ⊕ (Bool ⊕ ((Bool × Bool) ⊕ (M₁.State ⊕ M₂.State)))
  tm :=
    { q₀ := .inl D.tm.q₀
      tr := fun q inp work => match q with
        | .inl q => captureAction Sum.inl (.inr (.inl false))
            ((timedPadTM D (M₁.k + M₂.k)).tr q inp (fun i => work i.castSucc))
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
private def timedBranchCfg (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg (M₁.k + M₂.k) Bool (M₁.State ⊕ M₂.State) x)
    (tapes : Fin D.k → ℤ → Option Bool) (heads : Fin D.k → ℤ) (b : Bool) :
    Cfg (timedCondTM D M₁ M₂).k Bool (timedCondTM D M₁ M₂).State x :=
  leftCfg id (rightCfg (fun s => .inr (.inr (.inr s))) c tapes heads)
    (fun (_ : Fin 1) => bufferTape [b]) (fun _ => 0)

/-- The decider's configuration inside its padded, captured simulation.
Both branch tape banks are blank throughout this phase. -/
private def timedControlCfg (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg D.k Bool D.State x) :
    Cfg (timedCondTM D M₁ M₂).k Bool (timedCondTM D M₁ M₂).State x :=
  captureCfg Sum.inl (.inr (.inl false)) [] []
    (leftCfg id c (fun (_ : Fin (M₁.k + M₂.k)) _ => none) (fun _ => 0))

/-- The capture contract, instantiated on the padded decider, gives the
entire controller phase through its first halt. -/
private lemma timed_capture (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg D.k Bool D.State x) (t : ℕ)
    (hlive : ∀ s < t, ¬(D.tm.runFrom c s).Halted) :
    (timedCondTM D M₁ M₂).tm.runFrom (timedControlCfg D M₁ M₂ c) t =
      timedControlCfg D M₁ M₂ (D.tm.runFrom c t) := by
  have hpad (u : ℕ) := leftCfg_run D.tm (timedPadTM D (M₁.k + M₂.k)) id
    (fun _ _ _ => rfl) c (fun _ _ => none) (fun _ => 0) u
  have h := capture_run (timedPadTM D (M₁.k + M₂.k)) (timedCondTM D M₁ M₂).tm
    Sum.inl (.inr (.inl false)) (fun _ _ _ => rfl) [] []
    (leftCfg id c (fun _ _ => none) (fun _ => 0)) t (fun s hs => by
      unfold Cfg.Halted
      rw [hpad s]
      simpa only [leftCfg, Option.map_id] using hlive s hs)
  simpa only [hpad t] using h

/-- The host's genuine initial configuration is the captured, padded
initial configuration: all three work-tape blocks are blank. -/
private lemma timed_control_init (D M₁ M₂ : FinTM Bool) (x : List Bool) :
    (timedCondTM D M₁ M₂).tm.initCfg x =
      timedControlCfg D M₁ M₂ (D.tm.initCfg x) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    by_cases hi : (i : ℕ) < D.k + (M₁.k + M₂.k)
    · simp only [timedControlCfg, captureCfg, leftCfg, MultiTapeTM.initCfg,
        Cfg.init, dif_pos hi]
      exact (Fin.addCases (fun _ => by simp) (fun _ => by simp) ⟨i, hi⟩)
    · simp [timedControlCfg, captureCfg, leftCfg, hi]
  · funext i
    by_cases hi : (i : ℕ) < D.k + (M₁.k + M₂.k)
    · simp only [timedControlCfg, captureCfg, leftCfg, MultiTapeTM.initCfg,
        Cfg.init, dif_pos hi]
      exact (Fin.addCases (fun _ => by simp) (fun _ => by simp) ⟨i, hi⟩)
    · simp [timedControlCfg, captureCfg, leftCfg, hi]

/-- The physical input head can move right by at most one cell per step.
**Proof sketch.** Clamping never increases a proposed position. Check the
three movements, then induct over the run, treating halted steps as stationary. -/
private lemma timed_input_bound {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (c : Cfg k Bool S x) (t : ℕ) :
    (tm.runFrom c t).inputPos.val ≤ c.inputPos.val + t := by
  have hm (p : Fin (x.length + 2)) (m : SignType) :
      (moveInputPos p m).val ≤ p.val + 1 := by
    dsimp only [moveInputPos]
    split <;> dsimp <;> cases m <;> simp_all [SignType.cast] <;> omega
  have hstep (d : Cfg k Bool S x) : (tm.step d).inputPos.val ≤ d.inputPos.val + 1 := by
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

/-- A quantitative refinement of `rewind_from_any`: its construction takes
at most the current input position plus two steps, preserving all work and output.
**Proof sketch.** The mandatory first left move puts the head at most at the
last input symbol. `rewind_scan` then takes exactly the new position plus one. -/
private lemma timed_rewind {k : ℕ} {S : Type} {x : List Bool}
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

/-- Once dispatched, the selected branch runs in lockstep while the old
decider tapes and singleton capture tape remain idle.
**Proof sketch.** The branch action is a right-block embedding followed by
a left-block embedding; compose their application lemmas, then iterate. -/
private lemma timed_branch_run (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg (M₁.k + M₂.k) Bool (M₁.State ⊕ M₂.State) x)
    (tapes : Fin D.k → ℤ → Option Bool) (heads : Fin D.k → ℤ) (b : Bool) (t : ℕ) :
    (timedCondTM D M₁ M₂).tm.runFrom (timedBranchCfg D M₁ M₂ c tapes heads b) t =
      timedBranchCfg D M₁ M₂ ((branchTM M₁ M₂ b).tm.runFrom c t) tapes heads b := by
  apply MultiTapeTM.runFrom_comm_of_step (fun c => timedBranchCfg D M₁ M₂ c tapes heads b)
  intro d
  cases hs : d.state with
  | none =>
    simp only [MultiTapeTM.step, timedBranchCfg, leftCfg, rightCfg, hs, Option.map_none]
  | some q =>
    have hstate : (timedBranchCfg D M₁ M₂ d tapes heads b).state =
        some (.inr (.inr (.inr q))) := by
      simp only [timedBranchCfg, leftCfg, rightCfg, hs, Option.map_some, id_eq]
    have hi : (timedBranchCfg D M₁ M₂ d tapes heads b).inputSymbol = d.inputSymbol := rfl
    have hw : (fun i => (timedBranchCfg D M₁ M₂ d tapes heads b).workTapeSymbols
        (Fin.natAdd D.k i).castSucc) = d.workTapeSymbols := by
      funext i
      simp only [timedBranchCfg, leftCfg, rightCfg, Cfg.workTapeSymbols,
        Fin.castSucc, Fin.addCases_left, Fin.addCases_right]
    simp only [MultiTapeTM.step, hstate, hs]
    dsimp only [timedCondTM]
    let emb : (M₁.State ⊕ M₂.State) → (timedCondTM D M₁ M₂).State :=
      fun s => .inr (.inr (.inr s))
    change (leftAction 1 id (rightAction D.k emb
      ((branchTM M₁ M₂ b).tm.tr q d.inputSymbol
        (fun i => (timedBranchCfg D M₁ M₂ d tapes heads b).workTapeSymbols
          (Fin.natAdd D.k i).castSucc)))).apply
        (leftCfg id (rightCfg emb d tapes heads)
          (fun (_ : Fin 1) => bufferTape [b]) (fun _ => 0)) = _
    erw [hw, leftCfg_apply, rightCfg_apply]
    rfl

/-- After reading the verdict, all branch data are initialized; only the
input head still needs rewinding. The capture head is back at cell zero. -/
private def timedReadyCfg (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg D.k Bool D.State x) (b : Bool) :
    Cfg (timedCondTM D M₁ M₂).k Bool (timedCondTM D M₁ M₂).State x :=
  { timedBranchCfg D M₁ M₂ ((branchTM M₁ M₂ b).tm.initCfg x) c.workTapes c.workTapePos b with
    state := some (.inr (.inr (.inl (b, false))))
    inputPos := c.inputPos }

/-- Two silent transitions move the capture head left and read the completed
singleton verdict, without touching the input or either work bank.
**Proof sketch.** The final capture head is one past the singleton, hence at
one. Moving it left exposes exactly its bit at zero; the next transition
records that bit in the rewind state. -/
private lemma timed_read (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg D.k Bool D.State x) (b : Bool) (hs : c.state = none) (ho : c.output = [b]) :
    (timedCondTM D M₁ M₂).tm.runFrom (timedControlCfg D M₁ M₂ c) 2 =
      timedReadyCfg D M₁ M₂ c b := by
  let ready := timedReadyCfg D M₁ M₂ c b
  have hback : (timedCondTM D M₁ M₂).tm.step (timedControlCfg D M₁ M₂ c) =
      {ready with state := some (.inr (.inl true))} := by
    have hstate : (timedControlCfg D M₁ M₂ c).state = some (.inr (.inl false)) := by
      simp [timedControlCfg, captureCfg, leftCfg, hs]
    simp only [MultiTapeTM.step, hstate]
    refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j
        simp [timedCondTM, Action.apply, timedControlCfg, captureCfg, leftCfg,
          timedReadyCfg, timedBranchCfg, rightCfg, ready, j.isLt]
        refine Fin.addCases ?_ ?_ j <;> intro z <;> simp
      · intro j
        simp [timedCondTM, Action.apply, timedControlCfg, captureCfg, leftCfg,
          timedReadyCfg, timedBranchCfg, rightCfg, ready, ho]
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j
        simp [timedCondTM, Action.apply, timedControlCfg, captureCfg, leftCfg,
          timedReadyCfg, timedBranchCfg, rightCfg, ready, j.isLt]
        refine Fin.addCases ?_ ?_ j <;> intro z <;> simp
      · intro j
        simp [timedCondTM, Action.apply, timedControlCfg, captureCfg, leftCfg,
          timedReadyCfg, timedBranchCfg, rightCfg, ready, ho]
  have hread : (timedCondTM D M₁ M₂).tm.step
      {ready with state := some (.inr (.inl true))} = ready := by
    have hsym : ({ready with state := some (.inr (.inl true))} :
        Cfg (timedCondTM D M₁ M₂).k Bool (timedCondTM D M₁ M₂).State x).workTapeSymbols
        (Fin.last _) = some b := by
      change (timedBranchCfg D M₁ M₂ ((branchTM M₁ M₂ b).tm.initCfg x)
        c.workTapes c.workTapePos b).workTapeSymbols
          (Fin.natAdd (D.k + (M₁.k + M₂.k)) (0 : Fin 1)) = some b
      simp [timedBranchCfg, leftCfg, rightCfg, Cfg.workTapeSymbols, bufferTape]
    unfold MultiTapeTM.step
    dsimp only
    change ((controlAction 0 (some (.inr (.inr (.inl
      ((({ready with state := some (.inr (.inl true))} :
        Cfg (timedCondTM D M₁ M₂).k Bool (timedCondTM D M₁ M₂).State x).workTapeSymbols
        (Fin.last _)).getD false, false)))))) :
          Action (timedCondTM D M₁ M₂).k Bool (timedCondTM D M₁ M₂).State).apply _ = _
    rw [hsym, controlAction_apply]
    simp only [Option.getD_some, moveInputPos_zero]
    rfl
  change (timedCondTM D M₁ M₂).tm.step
    ((timedCondTM D M₁ M₂).tm.step (timedControlCfg D M₁ M₂ c)) = _
  rw [hback, hread]

/-- A singleton-output decider reaches the selected branch's genuine
initial configuration in at most twice its budget plus five steps.
**Proof sketch.** Choose the first source halt, which is within the supplied
budget. Capture until that halt, read the singleton in two steps, and rewind
in at most the current input position plus two. The head-position bound
charges this rewind to the decider's elapsed steps, not the input length. -/
private lemma timed_start (D M₁ M₂ : FinTM Bool) (x : List Bool) (b : Bool) (T : ℕ)
    (hD : D.ComputesInTime x [b] T) :
    ∃ a ≤ 2 * T + 5, ∃ (tapes : Fin D.k → ℤ → Option Bool) (heads : Fin D.k → ℤ),
      (timedCondTM D M₁ M₂).tm.runFrom ((timedCondTM D M₁ M₂).tm.initCfg x) a =
        timedBranchCfg D M₁ M₂ ((branchTM M₁ M₂ b).tm.initCfg x) tapes heads b := by
  classical
  have hh : ∃ t, (D.tm.runFrom (D.tm.initCfg x) t).state = none :=
    ⟨T, ((computesInTime_iff _ _ _ _).mp hD).1⟩
  let t := Nat.find hh
  let c := D.tm.runFrom (D.tm.initCfg x) t
  have ht : t ≤ T := Nat.find_min' hh ((computesInTime_iff _ _ _ _).mp hD).1
  have hs : c.state = none := Nat.find_spec hh
  have hc : D.ComputesInTime x c.output t := (computesInTime_iff _ _ _ _).mpr ⟨hs, rfl⟩
  have ho : c.output = [b] := hc.output_unique hD
  have hcap : (timedCondTM D M₁ M₂).tm.runFrom ((timedCondTM D M₁ M₂).tm.initCfg x) t =
      timedControlCfg D M₁ M₂ c := by
    rw [timed_control_init]
    exact timed_capture D M₁ M₂ _ t (fun s hst => Nat.find_min hh hst)
  obtain ⟨r, hrle, hr⟩ := timed_rewind (timedCondTM D M₁ M₂).tm
    (.inr (.inr (.inl (b, false)))) (.inr (.inr (.inl (b, true))))
    (some (.inr (.inr (.inr (branchTM M₁ M₂ b).tm.q₀))))
    (fun _ _ => rfl) (fun inp _ => by cases inp <;> rfl)
    (timedReadyCfg D M₁ M₂ c b) rfl
  refine ⟨t + 2 + r, ?_, c.workTapes, c.workTapePos, ?_⟩
  · have hp : c.inputPos.val ≤ 1 + t := by
      simpa only [MultiTapeTM.initCfg, Cfg.init, Fin.val_one] using
        timed_input_bound D.tm (D.tm.initCfg x) t
    change r ≤ c.inputPos.val + 2 at hrle
    omega
  · rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add, hcap,
      timed_read D M₁ M₂ c b hs ho, hr]
    rfl

/-- **W3, the timed branch** (spec, fill pending): the quantitative form of
`Turing.FinTM.exists_cond`. If a decider machine computes the test bit
within `T₀` and each branch computes its function within `T₁`, `T₂`, the
conditional function is computable within a constant multiple of
`T₀ + max T₁ T₂ + 1`. No monotonicity hypothesis: the selected branch runs
on the *same* physical input.

**Proof sketch.** Run the decider through the W1 capture discipline (its
verdict on the capture tape, physical output silent), rewind per the
`Turing.FinTM.rewind_from_any` scan, then dispatch on the captured bit into
the two-machine branch union (`Turing.FinTM.branchTM`), which runs the
selected branch from its genuine initial configuration on the shared input.
Constant overhead per phase is absorbed into `c`. -/
theorem computesFunInTime_cond {D M₁ M₂ : FinTM Bool} {p : List Bool → Bool}
    {f₁ f₂ : List Bool → List Bool} {T₀ T₁ T₂ : ℕ → ℕ}
    (hD : D.ComputesFunInTime (fun x => [p x]) T₀)
    (h₁ : M₁.ComputesFunInTime f₁ T₁) (h₂ : M₂.ComputesFunInTime f₂ T₂) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => if p x then f₁ x else f₂ x)
        (fun n => c * (T₀ n + max (T₁ n) (T₂ n) + 1)) := by
  refine ⟨timedCondTM D M₁ M₂, 5, fun x => ?_⟩
  let B := max (T₁ x.length) (T₂ x.length)
  have hb : (branchTM M₁ M₂ (p x)).ComputesInTime x
      (if p x then f₁ x else f₂ x) B := by
    apply (branchTM_computes M₁ M₂ (p x) x _ B).mpr
    cases hp : p x with
    | false => exact (h₂ x).mono (Nat.le_max_right _ _)
    | true => exact (h₁ x).mono (Nat.le_max_left _ _)
  obtain ⟨a, ha, tapes, heads, hstart⟩ :=
    timed_start D M₁ M₂ x (p x) (T₀ x.length) (hD x)
  have hc : (timedCondTM D M₁ M₂).ComputesInTime x
      (if p x then f₁ x else f₂ x) (a + B) := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_add, hstart, timed_branch_run]
    obtain ⟨hs, ho⟩ := (computesInTime_iff _ _ _ _).mp hb
    exact ⟨by simpa only [timedBranchCfg, leftCfg, rightCfg, Option.map_eq_none_iff] using hs, ho⟩
  -- The controller prefix and selected branch fit one uniform coefficient.
  apply hc.mono
  dsimp only [B] at *
  omega

end Turing.FinTM


## ===== TCSlib/Complexity/TuringMachine/Build/Loop.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Nat.Bits
import TCSlib.Complexity.TuringMachine.Build.Convention
import TCSlib.Complexity.TuringMachine.Build.Wrappers
import TCSlib.Complexity.TuringMachine.Composition

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: the bounded loop

The control centerpiece of the machine-construction library
(`machine-library-design.md` §5, L; loop redesign §9b, configuration
export §9c): a bounded loop with tape-resident round state, specified at
four granularities.

* `Turing.loop_run` is the **summation lemma**: given a family of round
  configurations with an accept-or-advance contract, the run from round 0
  halts within the summed budget with the loop's single verdict bit. It is
  the generic form of the Chapter-2 enumerator's proved private
  `enumLoop_run`, whose proof is the harvest template. (Round-1 audit:
  Pass.)
* `Turing.FinTM.exists_loopCfgTM` is the **configuration-level
  combinator** (added per round-2 finding 1): its conclusion exposes the
  host machine's round-configuration family, bounded startup, per-round
  accept-or-advance segments, and halted exhaustion terminal — the shape
  the frozen Chapter-2 `enumMachine_contracts` consumes, which the
  final-answer conclusion below provably cannot supply (the round-2 audit
  exhibits a final-answer-correct machine violating every per-round
  bound).
* `Turing.FinTM.exists_loopTM` is the **decision form**: one finite
  machine answers the Boolean "some orbit point accepts". At fill time it
  is a corollary of the configuration form through an
  already-halted-terminal summation lemma (the shape of the enumerator's
  `enumLoop_run`; the frozen `Turing.loop_run` requires an empty-output
  terminal, which the exported family's `[false]` terminal deliberately
  is not — round-3 finding R3-1), with startup absorbed by monotonicity.
* `Turing.FinTM.exists_loopFindTM` is the **result-bearing form**: the
  accepting round delivers a payload, and the machine outputs the first
  accepting orbit point's payload (`[]` on exhaustion) — the form the
  split search (catalog P10) and the reduction emitters instantiate.

**Status: spec phase, round-2 repair.** The round-1 audit
(`audits/ch1-infra-findings.md`) refuted the previous combinator: finding
1 (blocker) exhibited a zero-step "advance" (`stepF = id`, `t = 0`) that
made the hypotheses vacuously satisfiable and the conclusion contradict
the input-head information bound; finding 2 (major) showed the round
hypothesis quantified over *all* state words at the budget `T |x|`, which
no body can satisfy for width-growing rounds and which excludes the
intended customers. This revision repairs both:

* every round takes **positive time** (`0 < t`), and
* rounds are required only on **admissible** state words, via an
  input-indexed invariant `Inv x s` that the startup word satisfies
  (`hInv0`) and the advance step preserves (`hInvStep`); customers choose
  `Inv` to pin the state-word width to the input (instantiation tables in
  `machine-library-design.md` §9b).

`stepF`, `acceptF`, and the payload take the input as an explicit first
argument (finding 2's repair guidance): the enumerator's acceptance runs
the verifier on `x ++ s`.

## The round discipline

Round state is one word on the body's tape 0; every other body tape is
scratch, blank at both seam ends of a round (body-restores-scratch, frozen
design decision 9.2). A round either **accepts** — halts with its declared
output, nothing emitted earlier — or **advances** to the seam carrying the
stepped state word, in positive time, and in both cases without re-entering
the anchor state strictly between the seam and that endpoint (the host
detects round boundaries as entries into the embedded anchor; the clause is
load-bearing, round-1 attestation 7 and finding 1).

**Countdown discipline** (corrected per round-1 finding 4): the counter is
loaded from the fuel machine's output `Nat.bits (R |x|)`; the **initial
anchor entry is free**, and debiting starts with the second entry, so the
rounds completed before borrow-overflow are exactly `0, …, R |x|` — at
`R |x| = 0` (`Nat.bits 0 = []`) the single orbit point `s0 x` is still
checked before the empty counter overflows. Decrement cost is amortized
(the borrow lengths over a full countdown telescope to `O(R)`, and the
counter width is at most `T |x|` by `Turing.MultiTapeTM.output_length_le`
on the fuel machine), which is what keeps the stated budget at
`(T + 1) · (R + 2)` with no logarithmic factor — the round-1 audit
validated this budget strategy (finding 4, second half).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2; the clocked-loop discipline is
  the folklore engine of the enumeration and diagonalization arguments,
  §2.1 / §3.1–3.2.)

**Fill checkpoint (batch L).** `loop_run` is proved. The three finite-machine
exports are derived from the single admitted private `loopHost_contracts`.
The concrete controller, source-body simulation, fixed-width counter,
input rewind, capture instances, payload replay, and both terminal summation
lemmas are supplied below. Controller-level phase assembly and its uniform
budget remain the continuation frontier; this file is not an admission-free
completion of the loop combinators.

**Fill completion (batch L2).** The historical checkpoint above is now
closed: the actual fuel, startup, body-return, counter, and payload phases
are proved and assembled in `loopHost_contracts`, with uniform coefficient
`loopHost_bound = 10`. The canonical seams retain the completed fuel residue
and fixed-width debit iterates. Underflow and its final emission are inside
the last rejecting segment; an accepting last candidate has an arbitrary
unreachable rejection terminal. The entire file has no admissions, including
the capture helpers now that batch W's `capture_run` proof is integrated.
-/

namespace Turing

/-- Round state on tape 0, scratch blank: the standard word assignment for
a loop body's seam configurations. -/
def stateWord (k : ℕ) (s : List Bool) : Fin k → List Bool :=
  fun i => if (i : ℕ) = 0 then s else []

/-- **The loop summation lemma** (spec, fill pending — the generic form of
the enumerator's proved `enumLoop_run`, which is the harvest template;
round-1 audit verdict: Pass, including `N = 0`).
Given round configurations `cfg 0, …, cfg N` of one machine with empty
outputs, such that each round `j < N` within budget `B` either halts with
the verdict `[true]` (when `accept j`) or reaches `cfg (j+1)`, and the
exhaustion round `cfg N` halts with `[false]` within `B`: the run from
`cfg 0` halts within `(N + 1) · B` steps with the single verdict bit
`(List.range N).any accept`.

**Proof sketch.** Induction on the first accepting round (or `N` when none
accepts), composing the advance segments with
`Turing.MultiTapeTM.runFrom_add` and absorbing halted tails with
`Turing.MultiTapeTM.runFrom_of_halt`; empty round outputs make the final
output exactly the one emitted verdict. -/
theorem loop_run {k : ℕ} {S : Type*} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (cfg : ℕ → Cfg k Bool S x)
    (accept : ℕ → Bool) (B N : ℕ)
    (hout : ∀ j ≤ N, (cfg j).output = [])
    (hend : ∃ t ≤ B, (tm.runFrom (cfg N) t).state = none ∧
      (tm.runFrom (cfg N) t).output = [false])
    (hround : ∀ j < N, ∃ t ≤ B,
      if accept j then
        (tm.runFrom (cfg j) t).state = none ∧
          (tm.runFrom (cfg j) t).output = [true]
      else tm.runFrom (cfg j) t = cfg (j + 1)) :
    ∃ t ≤ (N + 1) * B, (tm.runFrom (cfg 0) t).state = none ∧
      (tm.runFrom (cfg 0) t).output = [(List.range N).any accept] := by
  induction N generalizing cfg accept with
  | zero => simpa using hend
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
      -- Shift the round family by one, retaining the same terminal segment.
      obtain ⟨s, hs, hhalt, hout'⟩ := ih
        (fun j => cfg (j + 1)) (fun j => accept (j + 1))
        (fun j hj => hout (j + 1) (by omega)) hend
        (fun j hj => hround (j + 1) (by omega))
      refine ⟨t + s, ?_, ?_, ?_⟩
      · rw [Nat.succ_mul]; omega
      · rw [MultiTapeTM.runFrom_add, hc]; exact hhalt
      · rw [MultiTapeTM.runFrom_add, hc]
        simpa [hany, hb] using hout'

end Turing

namespace Turing.FinTM

/-- A live endpoint rules out a halt anywhere in its preceding run. -/
private lemma loop_live_prefix {k : ℕ} {S : Type*} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (cfg : Cfg k Bool S x) (t : ℕ)
    (ht : (tm.runFrom cfg t).state ≠ none) :
    ∀ u ≤ t, (tm.runFrom cfg u).state ≠ none := by
  intro u hu hh
  have he : tm.runFrom cfg t = tm.runFrom cfg u := by
    rw [← Nat.add_sub_of_le hu, MultiTapeTM.runFrom_add,
      MultiTapeTM.runFrom_of_halt _ hh]
  exact ht (by rw [he]; exact hh)

/-- An empty final output forces every earlier output to be empty. -/
private lemma loop_silent_prefix {k : ℕ} {S : Type*} {x : List Bool}
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
private lemma loop_first_halt {k : ℕ} {S : Type*} {x : List Bool}
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
private lemma loop_orbit_inv (Inv : List Bool → List Bool → Prop)
    (stepF : List Bool → List Bool → List Bool) (s0 : List Bool → List Bool)
    (hInv0 : ∀ x, Inv x (s0 x))
    (hInvStep : ∀ x s, Inv x s → Inv x (stepF x s)) (x : List Bool) (i : ℕ) :
    Inv x ((stepF x)^[i] (s0 x)) := by
  induction i with
  | zero => exact hInv0 x
  | succ i ih => rw [Function.iterate_succ_apply']; exact hInvStep x _ ih

/-- The fuel run bounds the fixed counter width on each actual input. -/
private lemma loop_fuel_width (F : FinTM Bool) (R T : ℕ → ℕ)
    (hF : F.ComputesFunInTime (fun x => Nat.bits (R x.length)) T) (x : List Bool) :
    (Nat.bits (R x.length)).length ≤ T x.length := by
  obtain ⟨s, hhalt, hout, hspace⟩ := hF x
  simpa only [hout] using F.tm.output_length_le x (T x.length)

/-- One native input-head move increases its position by at most one. -/
private lemma loop_input_move_le {n : ℕ} (p : Fin (n + 2)) (m : SignType) :
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
private lemma loop_input_run_le {k : ℕ} {S : Type*} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (c : Cfg k Bool S x) (t : ℕ) :
    (tm.runFrom c t).inputPos.val ≤ c.inputPos.val + t := by
  have stepBound (d : Cfg k Bool S x) : (tm.step d).inputPos.val ≤ d.inputPos.val + 1 := by
    cases hd : d.state with
    | none => simp [MultiTapeTM.step, hd]
    | some q =>
      simpa only [MultiTapeTM.step, hd, Action.apply] using
        loop_input_move_le d.inputPos (tm.tr q d.inputSymbol d.workTapeSymbols).inputTape
  induction t with
  | zero => simp
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step']
    exact (stepBound _).trans (by omega)

/-- A run appends at most one output bit per step, from any seam configuration. -/
private lemma loop_output_length_le {k : ℕ} {S : Type*} {x : List Bool}
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
private lemma loop_rewind_bounded {k : ℕ} {S : Type} {x : List Bool}
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
private def loopDebit : List Bool → List Bool × Bool
  | [] => ([], false)
  | true :: bs => (false :: bs, true)
  | false :: bs => (true :: (loopDebit bs).1, (loopDebit bs).2)

/-- Number of low zero bits traversed by a borrow. -/
private def loopBorrowPos : List Bool → ℕ
  | false :: bs => loopBorrowPos bs + 1
  | _ => 0

/-- The borrow scan cannot cross more cells than the fixed width. -/
private lemma loopBorrowPos_le (u : List Bool) : loopBorrowPos u ≤ u.length := by
  induction u with
  | nil => rfl
  | cons b u ih => cases b <;> simp only [loopBorrowPos, List.length_cons] <;> omega

/-- Both successful decrements and underflow preserve the counter width. -/
private lemma loopDebit_length (u : List Bool) : (loopDebit u).1.length = u.length := by
  induction u with
  | nil => rfl
  | cons b u ih => cases b <;> simp [loopDebit, ih]

/-- Little-endian counter value; high zero cells contribute nothing. -/
private def loopValue : List Bool → ℕ
  | [] => 0
  | b :: bs => 2 * loopValue bs + if b then 1 else 0

/-- The fuel machine's binary word has its declared numerical value. -/
private lemma loopValue_bits (n : ℕ) : loopValue n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [loopValue]
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn]
    cases b <;> simp [loopValue, ih, Nat.bit_val]

/-- A successful debit reduces value by one; underflow occurs only at zero.
**Proof sketch.** A low one is cleared immediately. A low zero becomes one
while the inductive debit reduces the higher part; doubling that equation
gives the successor equation for the full word. -/
private lemma loopDebit_value (u : List Bool) :
    if (loopDebit u).2 then loopValue (loopDebit u).1 + 1 = loopValue u
    else loopValue u = 0 := by
  induction u with
  | nil => rfl
  | cons b u ih =>
    cases b with
    | true => simp [loopDebit, loopValue]
    | false =>
      cases h : (loopDebit u).2 <;>
        simp only [loopDebit, h, Bool.false_eq_true, ↓reduceIte,
          loopValue, Nat.add_zero] at ih ⊢ <;> omega

/-- The borrow returns success exactly for positive counter values. -/
private lemma loopDebit_success (u : List Bool) :
    (loopDebit u).2 = true ↔ 0 < loopValue u := by
  have h := loopDebit_value u
  cases hb : (loopDebit u).2
  · simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
    simp [h]
  · simp only [hb, ↓reduceIte] at h
    simp only [true_iff]
    omega

/-- Iterating debit retains the original fixed width at every index. -/
private lemma loopDebit_iterate_length (u : List Bool) (i : ℕ) :
    ((fun w => (loopDebit w).1)^[i] u).length = u.length := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply', loopDebit_length, ih]

/-- Before exhaustion, the counter after `i` debits has value `R-i`.
**Proof sketch.** Start from the fuel word's value. Before the last debit
the induction hypothesis gives a positive value, so the success equation
reduces it by exactly one. No representation is shortened. -/
private lemma loopDebit_iterate_value (R i : ℕ) (hi : i ≤ R) :
    loopValue ((fun w => (loopDebit w).1)^[i] R.bits) = R - i := by
  induction i with
  | zero => simpa using loopValue_bits R
  | succ i ih =>
    have hv := ih (by omega)
    have hs : (loopDebit ((fun w => (loopDebit w).1)^[i] R.bits)).2 = true :=
      (loopDebit_success _).2 (by omega)
    have hd := loopDebit_value ((fun w => (loopDebit w).1)^[i] R.bits)
    simp only [hs, ↓reduceIte] at hd
    rw [Function.iterate_succ_apply']
    omega

/-- Read the first bit of a suffix, with the empty suffix represented by blank. -/
private lemma loopBuffer_read (pre bs : List Bool) :
    bufferTape (pre ++ bs) pre.length = bs.head? := by
  simp only [bufferTape_nat, List.getElem?_append_right (le_refl _), Nat.sub_self]
  cases bs <;> rfl

/-- Writing at the start of a nonempty suffix preserves the prefix and width.
**Proof sketch.** At the write position use the new bit. Before and after
that position both tapes read the same unchanged entries. -/
private lemma loopBuffer_write (pre bs : List Bool) (old new : Bool) :
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
private def loopDebitTM : FinTM Bool where
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
private def loopDebitCfg (x : List Bool) (p : Fin (x.length + 2))
    (q : Option Bool ⊕ Bool) (z : ℤ) (u : List Bool) :
    Cfg loopDebitTM.k Bool loopDebitTM.State x :=
  ⟨some q, p, fun _ => bufferTape u, fun _ => z, []⟩

/-- One borrow transition writes only inside the fixed-width word, or detects
the right blank without writing to it. -/
private lemma loopBorrow_step (x : List Bool) (p : Fin (x.length + 2))
    (pre bs : List Bool) :
    loopDebitTM.tm.step (loopDebitCfg x p (.inl none) pre.length (pre ++ bs)) =
      match bs with
      | [] => loopDebitCfg x p (.inl (some false)) (pre.length - 1) pre
      | true :: us => loopDebitCfg x p (.inl (some true)) (pre.length - 1) (pre ++ false :: us)
      | false :: us => loopDebitCfg x p (.inl none) (pre.length + 1) (pre ++ true :: us) := by
  unfold MultiTapeTM.step
  change (loopDebitTM.tm.tr (.inl none) _ _).apply _ = _
  simp only [loopDebitTM, loopDebitCfg, Cfg.workTapeSymbols, loopBuffer_read]
  cases bs with
  | nil =>
    refine Cfg.ext rfl (moveInputPos_zero p) ?_ ?_ rfl
    · simp
    · funext i; simp [Action.apply, sub_eq_add_neg]
  | cons b bs =>
    cases b <;> refine Cfg.ext rfl (moveInputPos_zero p) ?_ ?_ rfl
    all_goals first
      | (funext i; exact loopBuffer_write pre bs _ _)
      | (funext i; simp [Action.apply, sub_eq_add_neg])

/-- The borrow phase takes one step beyond the leading false prefix, including
one blank test on underflow.
**Proof sketch.** Induct on the remaining candidate. Each false bit is set
and added to the processed prefix. A true bit or the right blank starts
rewind without changing the width. -/
private lemma loopBorrow_run (x : List Bool) (p : Fin (x.length + 2))
    (u : List Bool) : ∀ pre : List Bool,
    loopDebitTM.tm.runFrom (loopDebitCfg x p (.inl none) pre.length (pre ++ u))
        (loopBorrowPos u + 1) =
      loopDebitCfg x p (.inl (some (loopDebit u).2))
        ((pre.length : ℤ) + loopBorrowPos u - 1) (pre ++ (loopDebit u).1) := by
  induction u with
  | nil =>
    intro pre
    simpa [loopBorrowPos, loopDebit, MultiTapeTM.runFrom_succ_eq_step] using
      loopBorrow_step x p pre []
  | cons b u ih =>
    intro pre
    cases b with
    | true =>
      simpa [loopBorrowPos, loopDebit, MultiTapeTM.runFrom_succ_eq_step] using
        loopBorrow_step x p pre (true :: u)
    | false =>
      simp only [loopBorrowPos]
      rw [MultiTapeTM.runFrom_succ_eq_step, loopBorrow_step]
      simpa [loopDebit, List.append_assoc, Nat.cast_add, Nat.cast_one,
        add_assoc, add_comm, add_left_comm] using ih (pre ++ [true])

/-- Rewind over `j` known candidate cells to the left blank, then return at
cell zero in exactly `j+1` steps, retaining the candidate and success flag. -/
private lemma loopBorrow_rewind (x : List Bool) (p : Fin (x.length + 2))
    (u : List Bool) (b : Bool) : ∀ j, j ≤ u.length →
    loopDebitTM.tm.runFrom (loopDebitCfg x p (.inl (some b)) ((j : ℤ) - 1) u)
        (j + 1) = loopDebitCfg x p (.inr b) 0 u := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    simp only [Nat.cast_zero, zero_sub]
    unfold MultiTapeTM.step
    simp only [loopDebitTM, loopDebitCfg, Cfg.workTapeSymbols, bufferTape_left]
    refine Cfg.ext rfl (moveInputPos_zero p) rfl ?_ rfl
    funext i; simp [Action.apply]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hstep : loopDebitTM.tm.step
        (loopDebitCfg x p (.inl (some b)) ((j + 1 : ℕ) - 1) u) =
          loopDebitCfg x p (.inl (some b)) ((j : ℤ) - 1) u := by
      have hz : ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) := by omega
      rw [hz]
      unfold MultiTapeTM.step
      simp only [loopDebitTM, loopDebitCfg, Cfg.workTapeSymbols, bufferTape_nat,
        List.getElem?_eq_getElem (by omega : j < u.length)]
      refine Cfg.ext rfl (moveInputPos_zero p) rfl ?_ rfl
      funext i; simp [Action.apply, sub_eq_add_neg]
    rw [hstep]
    exact ih (by omega)

/-- A complete fixed-width decrement and rewind costs `2j+2 ≤ 2|u|+2`,
where `j` is the leading false-prefix length. It returns live at cell zero,
retains the input head, and emits nothing. Width zero returns underflow only
when this subroutine is called, so enumeration can process `[]` first. -/
private lemma loopBorrow_correct (x : List Bool) (p : Fin (x.length + 2))
    (u : List Bool) :
    2 * loopBorrowPos u + 2 ≤ 2 * u.length + 2 ∧
      loopDebitTM.tm.runFrom (loopDebitCfg x p (.inl none) 0 u)
          (2 * loopBorrowPos u + 2) =
        loopDebitCfg x p (.inr (loopDebit u).2) 0 (loopDebit u).1 := by
  refine ⟨by have := loopBorrowPos_le u; omega, ?_⟩
  have hr := loopBorrow_run x p u []
  simp only [List.length_nil, Nat.cast_zero, List.nil_append, zero_add] at hr
  rw [show 2 * loopBorrowPos u + 2 = (loopBorrowPos u + 1) + (loopBorrowPos u + 1) by omega,
    MultiTapeTM.runFrom_add, hr]
  exact loopBorrow_rewind x p (loopDebit u).1 (loopDebit u).2 _
    (by rw [loopDebit_length]; exact loopBorrowPos_le u)

/-- Stop the body at the next anchor entry, distinguishing that return from
a genuine source halt on an extra one-cell flag tape. A true release bit
forces one source action, even at the anchor; every source successor clears
the release bit. The body's full output is retained for subsequent capture. -/
private def loopBodyTM (body : FinTM Bool) (anchor : body.State) : FinTM Bool where
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
private def loopBodyCfg (body : FinTM Bool) (anchor : body.State) {x : List Bool}
    (c : Cfg body.k Bool body.State x) (release : Bool) (flag : Option Bool) :
    Cfg (loopBodyTM body anchor).k Bool (loopBodyTM body anchor).State x where
  state := c.state.map (fun s => (s, release))
  inputPos := c.inputPos
  workTapes := fun i => if h : (i : ℕ) < body.k then c.workTapes ⟨i, h⟩
    else fun z => if z = 0 then flag else none
  workTapePos := fun i => if h : (i : ℕ) < body.k then c.workTapePos ⟨i, h⟩ else 0
  output := c.output

/-- At an unreleased anchor the stop wrapper takes one silent step and
records rejection, without changing the body's configuration data. -/
private lemma loopBody_stop (body : FinTM Bool) (anchor : body.State) {x : List Bool}
    (c : Cfg body.k Bool body.State x) (hc : c.state = some anchor) (flag : Option Bool) :
    (loopBodyTM body anchor).tm.step (loopBodyCfg body anchor c false flag) =
      loopBodyCfg body anchor {c with state := none} false (some false) := by
  unfold MultiTapeTM.step
  simp only [loopBodyCfg, hc, Option.map_some, loopBodyTM, and_self, ↓reduceIte]
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
private lemma loopBody_step (body : FinTM Bool) (anchor : body.State) {x : List Bool}
    (c : Cfg body.k Bool body.State x) (q : body.State) (release : Bool)
    (flag : Option Bool) (hc : c.state = some q)
    (hgo : ¬(q = anchor ∧ release = false)) :
    (loopBodyTM body anchor).tm.step (loopBodyCfg body anchor c release flag) =
      loopBodyCfg body anchor (body.tm.step c) false
        (if (body.tm.step c).state = none then some true else flag) := by
  let a := body.tm.tr q c.inputSymbol c.workTapeSymbols
  have hb : body.tm.step c = a.apply c := by simp only [MultiTapeTM.step, hc, a]
  rw [hb]
  unfold MultiTapeTM.step
  simp only [loopBodyCfg, hc, Option.map_some, loopBodyTM, hgo, ↓reduceIte]
  have hr : (fun i : Fin body.k =>
      (loopBodyCfg body anchor c release flag).workTapeSymbols i.castSucc) =
        c.workTapeSymbols := by
    funext i
    simp [loopBodyCfg, Cfg.workTapeSymbols, i.isLt]
  change (let a' : Action body.k Bool body.State :=
            body.tm.tr q c.inputSymbol (fun i : Fin body.k =>
              (loopBodyCfg body anchor c release flag).workTapeSymbols i.castSucc);
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
private lemma loopBody_run (body : FinTM Bool) (anchor : body.State) {x : List Bool}
    (c : Cfg body.k Bool body.State x) (release : Bool) (hc : c.state ≠ none)
    (t : ℕ) (hlive : ∀ u < t, (body.tm.runFrom c u).state ≠ none)
    (hanchor : ∀ u < t, (u = 0 ∧ release = true) ∨
      (body.tm.runFrom c u).state ≠ some anchor) :
    (loopBodyTM body anchor).tm.runFrom (loopBodyCfg body anchor c release none) t =
      loopBodyCfg body anchor (body.tm.runFrom c t) (if t = 0 then release else false)
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
    rw [if_neg ht, loopBody_step body anchor _ q _ none hq hgo]
    simp only [Nat.succ_ne_zero, ↓reduceIte, MultiTapeTM.runFrom_succ_eq_step']

/-- W1 captures the stopped body's complete trace in any agreeing controller.
This includes an output bit emitted by the halting transition.
**Proof sketch.** The preceding simulation gives strict liveness of the
stop wrapper before the endpoint. Apply the audited capture contract with
the supplied controller as host, then substitute the simulated endpoint. -/
private lemma loopBody_capture (body : FinTM Bool) (anchor : body.State)
    {H : Type*} {x : List Bool} (host : MultiTapeTM (body.k + 1 + 1) Bool H)
    (emb : body.State × Bool → H) (ret : H)
    (hagree : ∀ s inp work, host.tr (emb s) inp work =
      captureAction emb ret ((loopBodyTM body anchor).tm.tr s inp fun i => work i.castSucc))
    (c : Cfg body.k Bool body.State x) (release : Bool) (hc : c.state ≠ none)
    (t : ℕ) (hlive : ∀ u < t, (body.tm.runFrom c u).state ≠ none)
    (hanchor : ∀ u < t, (u = 0 ∧ release = true) ∨
      (body.tm.runFrom c u).state ≠ some anchor) :
    host.runFrom (captureCfg emb ret [] [] (loopBodyCfg body anchor c release none)) t =
      captureCfg emb ret [] []
        (loopBodyCfg body anchor (body.tm.runFrom c t) (if t = 0 then release else false)
          (if (body.tm.runFrom c t).state = none then some true else none)) := by
  have hguard : ∀ u < t,
      ¬((loopBodyTM body anchor).tm.runFrom (loopBodyCfg body anchor c release none) u).Halted := by
    intro u hu
    rw [loopBody_run body anchor c release hc u
      (fun v hv => hlive v (by omega)) (fun v hv => hanchor v (by omega))]
    simpa [Cfg.Halted, loopBodyCfg] using hlive u hu
  rw [capture_run (loopBodyTM body anchor).tm host emb ret hagree [] [] _ t hguard,
    loopBody_run body anchor c release hc t hlive hanchor]

/-- Disjoint finite control for fuel, body calls, and fourteen controller phases. -/
private abbrev LoopHostState (body F : FinTM Bool) :=
  F.State ⊕ ((Bool × (body.State × Bool)) ⊕ Fin 14)

/-- Relocate the fuel machine past the untouched body, flag, and counter tapes. -/
private def loopFuelSource (body F : FinTM Bool) :
    MultiTapeTM (body.k + 1 + (1 + F.k)) Bool F.State where
  q₀ := F.tm.q₀
  tr := fun q inp work =>
    rightAction (body.k + 1) id (rightAction 1 id
      (F.tm.tr q inp fun i => work (Fin.natAdd (body.k + 1) (Fin.natAdd 1 i))))

/-- Extend the stopped body with a preserved counter and the fuel-phase residue. -/
private def loopBodySource (body F : FinTM Bool) (anchor : body.State) :
    MultiTapeTM (body.k + 1 + (1 + F.k)) Bool (body.State × Bool) where
  q₀ := (body.tm.q₀, false)
  tr := fun q inp work => leftAction (1 + F.k) id
    ((loopBodyTM body anchor).tm.tr q inp fun i => work (Fin.castAdd (1 + F.k) i))

/-- A controller action touches only the flag, counter, and capture tapes. -/
private def loopControlAction (body F : FinTM Bool) (inp : SignType)
    (flag : Option (Option Bool)) (counter payload : Option (Option Bool) × SignType)
    (out : Option Bool) (next : Option (LoopHostState body F)) :
    Action (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) where
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
private def loopHost (body F : FinTM Bool) (anchor : body.State) (findMode : Bool) :
    FinTM Bool where
  k := body.k + 1 + (1 + F.k) + 1
  State := LoopHostState body F
  tm :=
    { q₀ := .inl F.tm.q₀
      tr := fun q inp work =>
        let ctrl (j : Fin 14) : LoopHostState body F := .inr (.inr j)
        let call (startup : Bool) (s : body.State × Bool) : LoopHostState body F :=
          .inr (.inl (startup, s))
        let flag : Fin (body.k + 1 + (1 + F.k) + 1) := ⟨body.k, by omega⟩
        let counter : Fin (body.k + 1 + (1 + F.k) + 1) := ⟨body.k + 1, by omega⟩
        let payload := Fin.last (body.k + 1 + (1 + F.k))
        let act := loopControlAction body F
        match q with
        | .inl s => captureAction Sum.inl (ctrl 0)
            ((loopFuelSource body F).tr s inp fun i => work i.castSucc)
        | .inr (.inl (startup, s)) =>
            captureAction (call startup) (ctrl (if startup then 6 else 7))
              ((loopBodySource body F anchor).tr s inp fun i => work i.castSucc)
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
private lemma loopHost_body_capture (body F : FinTM Bool) (anchor : body.State)
    (findMode startup : Bool) {x : List Bool}
    (c : Cfg (body.k + 1 + (1 + F.k)) Bool (body.State × Bool) x) (t : ℕ)
    (hlive : ∀ u < t, ¬((loopBodySource body F anchor).runFrom c u).Halted) :
    (loopHost body F anchor findMode).tm.runFrom
        (captureCfg (fun s => Sum.inr (Sum.inl (startup, s)))
          (Sum.inr (Sum.inr (if startup then 6 else 7 : Fin 14))) [] [] c) t =
      captureCfg (fun s => Sum.inr (Sum.inl (startup, s)))
        (Sum.inr (Sum.inr (if startup then 6 else 7 : Fin 14))) [] []
        ((loopBodySource body F anchor).runFrom c t) := by
  exact capture_run (loopBodySource body F anchor) (loopHost body F anchor findMode).tm
    _ _ (by intro s inp work; rfl) [] [] c t hlive

/-- The fuel states capture all fuel emissions directly in the concrete host. -/
private lemma loopHost_fuel_capture (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (c : Cfg (body.k + 1 + (1 + F.k)) Bool F.State x) (t : ℕ)
    (hlive : ∀ u < t, ¬((loopFuelSource body F).runFrom c u).Halted) :
    (loopHost body F anchor findMode).tm.runFrom
        (captureCfg Sum.inl (Sum.inr (Sum.inr (0 : Fin 14))) [] [] c) t =
      captureCfg Sum.inl (Sum.inr (Sum.inr (0 : Fin 14))) [] []
        ((loopFuelSource body F).runFrom c t) := by
  exact capture_run (loopFuelSource body F) (loopHost body F anchor findMode).tm
    _ _ (by intro s inp work; rfl) [] [] c t hlive

/-- The fuel capture starts at the host's genuine blank initial configuration. -/
private lemma loopHost_init (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) (x : List Bool) :
    (loopHost body F anchor findMode).tm.initCfg x =
      captureCfg Sum.inl (Sum.inr (Sum.inr (0 : Fin 14))) [] []
        ((loopFuelSource body F).initCfg x) := by
  rw [initCfg_ofWords, initCfg_ofWords]
  simp [Cfg.ofWords, captureCfg, loopHost, loopFuelSource]

/-- With no track operations, a controller action is the standard input-only action. -/
private lemma loopControl_idle (body F : FinTM Bool) (inp : SignType)
    (next : Option (LoopHostState body F)) :
    loopControlAction body F inp none (none, 0) (none, 0) none next =
      controlAction inp next := by
  simp [loopControlAction, controlAction]

/-- Host phases 4 and 5 rewind the native input in bounded time, retaining
all tapes, heads, and output, then dispatch to genuine body startup. -/
private lemma loopHost_input_rewind (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (cfg : Cfg (loopHost body F anchor findMode).k Bool (loopHost body F anchor findMode).State x)
    (hs : cfg.state = some (.inr (.inr (4 : Fin 14)))) :
    ∃ t ≤ cfg.inputPos.val + 2,
      (loopHost body F anchor findMode).tm.runFrom cfg t =
        {cfg with state := some (.inr (.inl (true, (body.tm.q₀, false)))), inputPos := 1} := by
  apply loop_rewind_bounded (loopHost body F anchor findMode).tm
    (.inr (.inr 4)) (.inr (.inr 5)) (.some (.inr (.inl (true, (body.tm.q₀, false)))))
    ?_ ?_ cfg hs
  · intro inp work
    exact loopControl_idle body F .neg _
  · intro inp work
    cases inp <;> exact loopControl_idle body F _ _

/-- A controller configuration with arbitrary preserved body/fuel residue.
Only the flag, counter, and capture tracks are replaced by the parameters. -/
private def loopFrame (body F : FinTM Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x)
    (q : Option (LoopHostState body F)) (p : Fin (x.length + 2))
    (flag counter payload : ℤ → Option Bool) (ch ph : ℤ) (out : List Bool) :
    Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x where
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
private def loopWrite (tape : ℤ → Option Bool) (head : ℤ) :
    Option (Option Bool) → ℤ → Option Bool
  | none => tape
  | some symbol => Function.update tape head symbol

/-- Controller actions preserve the inactive frame and perform precisely
the three declared track operations. -/
private lemma loopControl_apply (body F : FinTM Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x)
    (q : Option (LoopHostState body F)) (p : Fin (x.length + 2))
    (flag counter payload : ℤ → Option Bool) (ch ph : ℤ) (out : List Bool)
    (inp : SignType) (fw : Option (Option Bool))
    (ca pa : Option (Option Bool) × SignType) (emit : Option Bool)
    (next : Option (LoopHostState body F)) :
    (loopControlAction body F inp fw ca pa emit next).apply
        (loopFrame body F base q p flag counter payload ch ph out) =
      loopFrame body F base next (moveInputPos p inp)
        (loopWrite flag 0 fw) (loopWrite counter ch ca.1) (loopWrite payload ph pa.1)
        (ch + ca.2) (ph + pa.2) (out ++ emit.toList) := by
  have hcf : body.k + 1 ≠ body.k := by omega
  have hpf : body.k + 1 + (1 + F.k) ≠ body.k := by omega
  have hpc : body.k + 1 + (1 + F.k) ≠ body.k + 1 := by omega
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    by_cases hf : (i : ℕ) = body.k
    · simp only [Action.apply, loopControlAction, loopFrame, hf, ↓reduceIte]
      cases fw <;> rfl
    · by_cases hc : (i : ℕ) = body.k + 1
      · simp only [Action.apply, loopControlAction, loopFrame, hc, hcf, ↓reduceIte]
        cases ca.1 <;> rfl
      · by_cases hp : (i : ℕ) = body.k + 1 + (1 + F.k)
        · simp only [Action.apply, loopControlAction, loopFrame, hp, hpf, hpc, ↓reduceIte]
          cases pa.1 <;> rfl
        · simp [Action.apply, loopControlAction, loopFrame, hf, hc, hp]
  · funext i
    by_cases hf : (i : ℕ) = body.k
    · simp [Action.apply, loopControlAction, loopFrame, hf]
    · by_cases hc : (i : ℕ) = body.k + 1
      · simp [Action.apply, loopControlAction, loopFrame, hc]
      · by_cases hp : (i : ℕ) = body.k + 1 + (1 + F.k) <;>
          simp [Action.apply, loopControlAction, loopFrame, hf, hc, hp, hpf]

/-- One-tape payload replay: emit each stored bit, then halt on the right blank. -/
private def loopReplayTM : FinTM Bool where
  k := 1
  State := Unit
  tm :=
    { q₀ := ()
      tr := fun _ _ work => match work 0 with
        | some b => ⟨0, fun _ => (none, .pos), some b, some ()⟩
        | none => ⟨0, fun _ => (none, 0), none, none⟩ }

/-- Replay configuration with arbitrary input position and output prefix. -/
private def loopReplayCfg (x : List Bool) (p : Fin (x.length + 2))
    (q : Option Unit) (z : ℤ) (word out : List Bool) : Cfg 1 Bool Unit x :=
  ⟨q, p, fun _ => bufferTape word, fun _ => z, out⟩

/-- A replay step emits the current bit without modifying the captured word;
at the right blank it halts without an additional bit. -/
private lemma loopReplay_step (x : List Bool) (p : Fin (x.length + 2))
    (pre rest out : List Bool) :
    loopReplayTM.tm.step (loopReplayCfg x p (some ()) pre.length (pre ++ rest) out) =
      match rest with
      | [] => loopReplayCfg x p none pre.length pre out
      | b :: bs => loopReplayCfg x p (some ()) (pre.length + 1) (pre ++ b :: bs) (out ++ [b]) := by
  unfold MultiTapeTM.step
  change (loopReplayTM.tm.tr () _ _).apply _ = _
  simp only [loopReplayTM, loopReplayCfg, Cfg.workTapeSymbols, loopBuffer_read]
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
private lemma loopReplay_run (x : List Bool) (p : Fin (x.length + 2))
    (rest : List Bool) : ∀ pre out : List Bool,
    loopReplayTM.tm.runFrom (loopReplayCfg x p (some ()) pre.length (pre ++ rest) out)
        (rest.length + 1) =
      loopReplayCfg x p none (pre ++ rest).length (pre ++ rest) (out ++ rest) := by
  induction rest with
  | nil =>
    intro pre out
    simpa [MultiTapeTM.runFrom_succ_eq_step] using loopReplay_step x p pre [] out
  | cons b rest ih =>
    intro pre out
    rw [List.length_cons, MultiTapeTM.runFrom_succ_eq_step, loopReplay_step]
    simpa [List.append_assoc, List.length_append, List.length_cons, Nat.cast_add,
      Nat.cast_one, add_assoc, add_comm, add_left_comm] using ih (pre ++ [b]) (out ++ [b])

/-- A payload-only controller action is the right-block action extension. -/
private lemma loopControl_payload (body F : FinTM Bool) (d : SignType)
    (out : Option Bool) (next : Option (LoopHostState body F)) :
    loopControlAction body F 0 none (none, 0) (none, d) out next =
      rightAction (body.k + 1 + (1 + F.k)) id
        (⟨0, fun _ : Fin 1 => (none, d), out, next⟩ : Action 1 Bool (LoopHostState body F)) := by
  simp only [loopControlAction, rightAction, Option.map_id]
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
private lemma loopHost_replay (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) (x : List Bool) (p : Fin (x.length + 2)) (word out : List Bool)
    (tapes : Fin (body.k + 1 + (1 + F.k)) → ℤ → Option Bool)
    (heads : Fin (body.k + 1 + (1 + F.k)) → ℤ) :
    (loopHost body F anchor findMode).tm.runFrom
        (rightCfg (fun _ : Unit => Sum.inr (Sum.inr (13 : Fin 14)))
          (loopReplayCfg x p (some ()) 0 word out) tapes heads) (word.length + 1) =
      rightCfg (fun _ : Unit => Sum.inr (Sum.inr (13 : Fin 14)))
        (loopReplayCfg x p none word.length word (out ++ word)) tapes heads := by
  have htr : ∀ q inp work,
      (loopHost body F anchor findMode).tm.tr (.inr (.inr (13 : Fin 14))) inp work =
        rightAction (body.k + 1 + (1 + F.k))
          (fun _ : Unit => Sum.inr (Sum.inr (13 : Fin 14)))
          (loopReplayTM.tm.tr q inp fun i => work (Fin.natAdd (body.k + 1 + (1 + F.k)) i)) := by
    intro q inp work
    cases q
    change (match work (Fin.last (body.k + 1 + (1 + F.k))) with
      | some b => loopControlAction body F 0 none (none, 0) (none, .pos) (some b)
          (some (.inr (.inr 13)))
      | none => loopControlAction body F 0 none (none, 0) (none, 0) none none) = _
    cases hw : work (Fin.last (body.k + 1 + (1 + F.k)))
    · simpa only [loopReplayTM, show Fin.natAdd (body.k + 1 + (1 + F.k)) (0 : Fin 1) =
          Fin.last (body.k + 1 + (1 + F.k)) from rfl, hw] using
        loopControl_payload body F 0 none none
    · simpa only [loopReplayTM, show Fin.natAdd (body.k + 1 + (1 + F.k)) (0 : Fin 1) =
          Fin.last (body.k + 1 + (1 + F.k)) from rfl, hw] using
        loopControl_payload body F .pos _ _
  refine (rightCfg_run (k := body.k + 1 + (1 + F.k)) (l := 1)
    loopReplayTM.tm (loopHost body F anchor findMode).tm
    (fun _ : Unit => Sum.inr (Sum.inr (13 : Fin 14))) htr
    (loopReplayCfg x p (some ()) 0 word out) tapes heads (word.length + 1)).trans ?_
  have hr := loopReplay_run x p word [] out
  simpa using congrArg
    (fun c => rightCfg (fun _ : Unit => Sum.inr (Sum.inr (13 : Fin 14))) c tapes heads) hr

/-- The fuel configuration on its relocated block, with the body, flag, and
counter still blank. The completed fuel residue is retained by this embedding. -/
private def loopFuelCfg (body F : FinTM Bool) {x : List Bool}
    (c : Cfg F.k Bool F.State x) :
    Cfg (body.k + 1 + (1 + F.k)) Bool F.State x :=
  rightCfg id (rightCfg id c (fun (_ : Fin 1) _ => none) (fun _ => 0))
    (fun (_ : Fin (body.k + 1)) _ => none) (fun _ => 0)

/-- Relocating fuel through the counter and body blocks preserves every run.
**Proof sketch.** Apply the right-block simulation twice. Each inactive block
has its own blank tapes and origin heads, retained throughout the source run. -/
private lemma loopFuel_run (body F : FinTM Bool) {x : List Bool}
    (c : Cfg F.k Bool F.State x) (t : ℕ) :
    (loopFuelSource body F).runFrom (loopFuelCfg body F c) t =
      loopFuelCfg body F (F.tm.runFrom c t) := by
  let pad : MultiTapeTM (1 + F.k) Bool F.State :=
    { q₀ := F.tm.q₀
      tr := fun q inp work => rightAction 1 id
        (F.tm.tr q inp (fun i => work (Fin.natAdd 1 i))) }
  unfold loopFuelCfg
  rw [rightCfg_run pad (loopFuelSource body F) id (fun _ _ _ => rfl),
    rightCfg_run F.tm pad id (fun _ _ _ => rfl)]

/-- The relocated fuel source begins at its genuine blank configuration. -/
private lemma loopFuel_init (body F : FinTM Bool) (x : List Bool) :
    (loopFuelSource body F).initCfg x = loopFuelCfg body F (F.tm.initCfg x) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [loopFuelCfg, rightCfg, MultiTapeTM.initCfg, Cfg.init]
    · intro j
      refine Fin.addCases ?_ ?_ j <;> intro k <;>
        simp [loopFuelCfg, rightCfg, MultiTapeTM.initCfg, Cfg.init]
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [loopFuelCfg, rightCfg, MultiTapeTM.initCfg, Cfg.init]
    · intro j
      refine Fin.addCases ?_ ?_ j <;> intro k <;>
        simp [loopFuelCfg, rightCfg, MultiTapeTM.initCfg, Cfg.init]

/-- The capture track of a frame reads precisely its parameterized tape. -/
private lemma loopFrame_payload (body F : FinTM Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x)
    (q : Option (LoopHostState body F)) (p : Fin (x.length + 2))
    (flag counter payload : ℤ → Option Bool) (ch ph : ℤ) (out : List Bool) :
    (loopFrame body F base q p flag counter payload ch ph out).workTapeSymbols
        (Fin.last (body.k + 1 + (1 + F.k))) = payload ph := by
  have hf : body.k + 1 + (1 + F.k) ≠ body.k := by omega
  simp [loopFrame, Cfg.workTapeSymbols, hf]

/-- The counter track of a frame reads precisely its parameterized tape. -/
private lemma loopFrame_counter (body F : FinTM Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x)
    (q : Option (LoopHostState body F)) (p : Fin (x.length + 2))
    (flag counter payload : ℤ → Option Bool) (ch ph : ℤ) (out : List Bool) :
    (loopFrame body F base q p flag counter payload ch ph out).workTapeSymbols
        ⟨body.k + 1, by omega⟩ = counter ch := by
  simp [loopFrame, Cfg.workTapeSymbols]

/-- Fuel-rewind phase 1 scans to the left blank and returns at the origin.
**Proof sketch.** Induct on the number of stored cells to the left. At zero,
the head is on the left blank; otherwise its cell is nonblank and the left
move reduces that number. All other tracks and the native input are retained. -/
private lemma loopHost_fuel_rewind (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x)
    (p : Fin (x.length + 2)) (flag counter : ℤ → Option Bool)
    (ch : ℤ) (word out : List Bool) : ∀ j, j ≤ word.length →
    (loopHost body F anchor findMode).tm.runFrom
        (loopFrame body F base (some (.inr (.inr 1))) p flag counter
          (bufferTape word) ch ((j : ℤ) - 1) out) (j + 1) =
      loopFrame body F base (some (.inr (.inr 2))) p flag counter
        (bufferTape word) ch 0 out := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    change (match (loopFrame body F base (some (.inr (.inr 1))) p flag counter
        (bufferTape word) ch ((0 : ℤ) - 1) out).workTapeSymbols
          (Fin.last (body.k + 1 + (1 + F.k))) with
      | some _ => loopControlAction body F 0 none (none, 0) (none, .neg) none
          (some (.inr (.inr 1)))
      | none => loopControlAction body F 0 none (none, 0) (none, .pos) none
          (some (.inr (.inr 2)))).apply _ = _
    rw [loopFrame_payload]
    simp only [zero_sub, bufferTape_left]
    rw [loopControl_apply]
    simp [loopWrite]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hs : (loopHost body F anchor findMode).tm.step
        (loopFrame body F base (some (.inr (.inr 1))) p flag counter
          (bufferTape word) ch (((j + 1 : ℕ) : ℤ) - 1) out) =
        loopFrame body F base (some (.inr (.inr 1))) p flag counter
          (bufferTape word) ch ((j : ℤ) - 1) out := by
      change (match (loopFrame body F base (some (.inr (.inr 1))) p flag counter
          (bufferTape word) ch (((j + 1 : ℕ) : ℤ) - 1) out).workTapeSymbols
            (Fin.last (body.k + 1 + (1 + F.k))) with
        | some _ => loopControlAction body F 0 none (none, 0) (none, .neg) none
            (some (.inr (.inr 1)))
        | none => loopControlAction body F 0 none (none, 0) (none, .pos) none
            (some (.inr (.inr 2)))).apply _ = _
      rw [loopFrame_payload]
      rw [show ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) by omega,
        bufferTape_nat, List.getElem?_eq_getElem (by omega : j < word.length)]
      rw [loopControl_apply]
      simp [loopWrite, sub_eq_add_neg]
    rw [hs]
    exact ih (by omega)

/-- During fuel copying, the processed prefix of the capture tape is blank. -/
private def loopCopyTape (pre rest : List Bool) (z : ℤ) : Option Bool :=
  if z < pre.length then none else bufferTape (pre ++ rest) z

/-- The copying frontier reads the first bit of the remaining suffix. -/
private lemma loopCopy_read (pre rest : List Bool) :
    loopCopyTape pre rest pre.length = rest.head? := by
  simp only [loopCopyTape, lt_self_iff_false, ↓reduceIte, loopBuffer_read]

/-- Clearing one fuel cell extends the already-cleared prefix by that bit. -/
private lemma loopCopy_erase (pre rest : List Bool) (b : Bool) :
    Function.update (loopCopyTape pre (b :: rest)) (pre.length : ℤ) none =
      loopCopyTape (pre ++ [b]) rest := by
  funext z
  by_cases hz : z = pre.length
  · subst z; simp [loopCopyTape]
  · rw [Function.update_of_ne hz]
    have hlt : z < (pre.length : ℤ) ↔ z < ((pre ++ [b]).length : ℤ) := by
      simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
      omega
    simp only [loopCopyTape, hlt, List.append_assoc, List.singleton_append]

/-- Before copying begins the capture tape is the original fuel buffer. -/
private lemma loopCopy_initial (word : List Bool) :
    loopCopyTape [] word = bufferTape word := by
  funext z
  by_cases hz : z < 0
  · simp [loopCopyTape, bufferTape, hz, show ¬0 ≤ z by omega]
  · simp [loopCopyTape, hz]

/-- After copying ends the capture tape is completely blank. -/
private lemma loopCopy_final (word : List Bool) :
    loopCopyTape word [] = bufferTape [] := by
  funext z
  by_cases hz : z < word.length
  · simp [loopCopyTape, hz]
  · have hn : 0 ≤ z := by omega
    simp [loopCopyTape, hz, bufferTape, hn]

/-- Phase 2 copies the remaining fuel bits to the counter, clearing each
captured bit, then starts the synchronized rewind.
**Proof sketch.** Induct on the uncopied suffix. A nonempty suffix writes
its head at the counter's right blank, clears the corresponding payload
cell, and advances both heads. The empty suffix detects the right blank
and moves both heads left once, including when the original word is empty. -/
private lemma loopHost_fuel_copy (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x)
    (p : Fin (x.length + 2)) (flag : ℤ → Option Bool) (out : List Bool)
    (rest : List Bool) : ∀ pre,
    (loopHost body F anchor findMode).tm.runFrom
        (loopFrame body F base (some (.inr (.inr 2))) p flag (bufferTape pre)
          (loopCopyTape pre rest) pre.length pre.length out) (rest.length + 1) =
      loopFrame body F base (some (.inr (.inr 3))) p flag (bufferTape (pre ++ rest))
        (bufferTape []) ((pre ++ rest).length - 1) ((pre ++ rest).length - 1) out := by
  induction rest with
  | nil =>
    intro pre
    rw [List.length_nil, MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    change (match (loopFrame body F base (some (.inr (.inr 2))) p flag (bufferTape pre)
        (loopCopyTape pre []) pre.length pre.length out).workTapeSymbols
          (Fin.last (body.k + 1 + (1 + F.k))) with
      | some b => loopControlAction body F 0 none (some (some b), .pos)
          (some none, .pos) none (some (.inr (.inr 2)))
      | none => loopControlAction body F 0 none (none, .neg) (none, .neg) none
          (some (.inr (.inr 3)))).apply _ = _
    rw [loopFrame_payload, loopCopy_read]
    dsimp only [List.head?]
    rw [loopControl_apply]
    simp [loopWrite, loopCopy_final, sub_eq_add_neg]
  | cons b rest ih =>
    intro pre
    rw [List.length_cons, MultiTapeTM.runFrom_succ_eq_step]
    have hs : (loopHost body F anchor findMode).tm.step
        (loopFrame body F base (some (.inr (.inr 2))) p flag (bufferTape pre)
          (loopCopyTape pre (b :: rest)) pre.length pre.length out) =
        loopFrame body F base (some (.inr (.inr 2))) p flag (bufferTape (pre ++ [b]))
          (loopCopyTape (pre ++ [b]) rest) (pre ++ [b]).length (pre ++ [b]).length out := by
      change (match (loopFrame body F base (some (.inr (.inr 2))) p flag (bufferTape pre)
          (loopCopyTape pre (b :: rest)) pre.length pre.length out).workTapeSymbols
            (Fin.last (body.k + 1 + (1 + F.k))) with
        | some bit => loopControlAction body F 0 none (some (some bit), .pos)
            (some none, .pos) none (some (.inr (.inr 2)))
        | none => loopControlAction body F 0 none (none, .neg) (none, .neg) none
            (some (.inr (.inr 3)))).apply _ = _
      rw [loopFrame_payload, loopCopy_read]
      dsimp only [List.head?]
      rw [loopControl_apply]
      simp [loopWrite, loopCopy_erase, bufferTape_append]
    rw [hs]
    simpa [List.append_assoc] using ih (pre ++ [b])

/-- Phase 3 rewinds counter and cleared capture heads together.
**Proof sketch.** Induct on the number of counter cells to the left. Both
heads take the same moves; only the counter is read, so the already-cleared
capture tape stays blank. The final left-blank test moves both heads to zero. -/
private lemma loopHost_fuel_return (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x)
    (p : Fin (x.length + 2)) (flag : ℤ → Option Bool) (word out : List Bool) :
    ∀ j, j ≤ word.length →
    (loopHost body F anchor findMode).tm.runFrom
        (loopFrame body F base (some (.inr (.inr 3))) p flag (bufferTape word)
          (bufferTape []) ((j : ℤ) - 1) ((j : ℤ) - 1) out) (j + 1) =
      loopFrame body F base (some (.inr (.inr 4))) p flag (bufferTape word)
        (bufferTape []) 0 0 out := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    change (match (loopFrame body F base (some (.inr (.inr 3))) p flag (bufferTape word)
        (bufferTape []) ((0 : ℤ) - 1) ((0 : ℤ) - 1) out).workTapeSymbols
          ⟨body.k + 1, by omega⟩ with
      | some _ => loopControlAction body F 0 none (none, .neg) (none, .neg) none
          (some (.inr (.inr 3)))
      | none => loopControlAction body F 0 none (none, .pos) (none, .pos) none
          (some (.inr (.inr 4)))).apply _ = _
    rw [loopFrame_counter]
    simp only [zero_sub, bufferTape_left]
    rw [loopControl_apply]
    simp [loopWrite]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hs : (loopHost body F anchor findMode).tm.step
        (loopFrame body F base (some (.inr (.inr 3))) p flag (bufferTape word)
          (bufferTape []) (((j + 1 : ℕ) : ℤ) - 1) (((j + 1 : ℕ) : ℤ) - 1) out) =
        loopFrame body F base (some (.inr (.inr 3))) p flag (bufferTape word)
          (bufferTape []) ((j : ℤ) - 1) ((j : ℤ) - 1) out := by
      change (match (loopFrame body F base (some (.inr (.inr 3))) p flag (bufferTape word)
          (bufferTape []) (((j + 1 : ℕ) : ℤ) - 1) (((j + 1 : ℕ) : ℤ) - 1) out).workTapeSymbols
            ⟨body.k + 1, by omega⟩ with
        | some _ => loopControlAction body F 0 none (none, .neg) (none, .neg) none
            (some (.inr (.inr 3)))
        | none => loopControlAction body F 0 none (none, .pos) (none, .pos) none
            (some (.inr (.inr 4)))).apply _ = _
      rw [loopFrame_counter]
      rw [show ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) by omega,
        bufferTape_nat, List.getElem?_eq_getElem (by omega : j < word.length)]
      rw [loopControl_apply]
      simp [loopWrite, sub_eq_add_neg]
    rw [hs]
    exact ih (by omega)

/-- Fuel setup phases 0--3 copy the complete fuel word to the counter,
clear the capture track, and return both heads to zero in exactly `3|word|+4`
steps. This includes the empty word, with no counter debit.
**Proof sketch.** Compose the mandatory left move, the fuel rewind, the
copy/clear scan, and the synchronized rewind. Their costs are respectively
one and three copies of the word length plus one. -/
private lemma loopHost_fuel_setup (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x)
    (p : Fin (x.length + 2)) (flag : ℤ → Option Bool) (word out : List Bool) :
    (loopHost body F anchor findMode).tm.runFrom
        (loopFrame body F base (some (.inr (.inr 0))) p flag (bufferTape [])
          (bufferTape word) 0 word.length out) (3 * word.length + 4) =
      loopFrame body F base (some (.inr (.inr 4))) p flag (bufferTape word)
        (bufferTape []) 0 0 out := by
  have hs : (loopHost body F anchor findMode).tm.step
      (loopFrame body F base (some (.inr (.inr 0))) p flag (bufferTape [])
        (bufferTape word) 0 word.length out) =
      loopFrame body F base (some (.inr (.inr 1))) p flag (bufferTape [])
        (bufferTape word) 0 ((word.length : ℤ) - 1) out := by
    change (loopControlAction body F 0 none (none, 0) (none, .neg) none
      (some (.inr (.inr 1)))).apply _ = _
    rw [loopControl_apply]
    simp [loopWrite, sub_eq_add_neg]
  rw [show 3 * word.length + 4 =
      ((word.length + 1) + (word.length + 1) + (word.length + 1)) + 1 by omega,
    MultiTapeTM.runFrom_succ_eq_step, hs]
  rw [MultiTapeTM.runFrom_add,
    MultiTapeTM.runFrom_add (a := word.length + 1) (b := word.length + 1),
    loopHost_fuel_rewind body F anchor findMode base p flag (bufferTape []) 0 word out
      word.length (le_refl _)]
  have hc := loopHost_fuel_copy body F anchor findMode base p flag out word []
  simp only [List.length_nil, Nat.cast_zero, List.nil_append, loopCopy_initial] at hc
  rw [hc, loopHost_fuel_return body F anchor findMode base p flag word out
    word.length (le_refl _)]

/-- The host's captured fuel endpoint, retaining all completed fuel residue. -/
private def loopFuelCaptured (body F : FinTM Bool) {x : List Bool}
    (c : Cfg F.k Bool F.State x) :
    Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x :=
  captureCfg Sum.inl (Sum.inr (Sum.inr (0 : Fin 14))) [] [] (loopFuelCfg body F c)

/-- The prepared startup configuration: fuel copied, capture blank, input
and active heads at their origins, and completed fuel work retained. -/
private def loopReady (body F : FinTM Bool) {x : List Bool}
    (c : Cfg F.k Bool F.State x) :
    Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x :=
  loopFrame body F (loopFuelCaptured body F c)
    (some (.inr (.inl (true, (body.tm.q₀, false))))) 1
    (bufferTape []) (bufferTape c.output) (bufferTape []) 0 0 []

/-- At a genuine fuel halt the capture endpoint has the frame expected by
phase 0, with the flag and counter still blank.
**Proof sketch.** Split the physical tape index into capture, body/flag,
counter, and fuel blocks. The three active controller tracks agree with
their explicit parameters; every inactive track is retained from the base. -/
private lemma loopFuelCaptured_frame (body F : FinTM Bool) {x : List Bool}
    (c : Cfg F.k Bool F.State x) (hc : c.state = none) :
    loopFuelCaptured body F c =
      loopFrame body F (loopFuelCaptured body F c) (some (.inr (.inr 0))) c.inputPos
        (bufferTape []) (bufferTape []) (bufferTape c.output) 0 c.output.length [] := by
  refine Cfg.ext ?_ rfl ?_ ?_ rfl
  · simp [loopFuelCaptured, captureCfg, loopFuelCfg, rightCfg, loopFrame, hc]
  · funext i
    refine Fin.lastCases ?_ ?_ i
    · have hf : body.k + 1 + (1 + F.k) ≠ body.k := by omega
      simp [loopFuelCaptured, captureCfg, loopFuelCfg, rightCfg, loopFrame, hf]
    · intro j
      have hj : (j : ℕ) ≠ body.k + 1 + (1 + F.k) := Nat.ne_of_lt j.isLt
      refine Fin.addCases ?_ ?_ j
      · intro a
        have ha : (a : ℕ) < body.k + 1 + (1 + F.k) := by omega
        have han : (a : ℕ) ≠ body.k + 1 := by omega
        have hap : (a : ℕ) ≠ body.k + 1 + (1 + F.k) := by omega
        simp [loopFuelCaptured, captureCfg, loopFuelCfg, rightCfg, loopFrame, ha, han, hap, Fin.addCases, a.isLt]
      · intro a
        refine Fin.addCases ?_ ?_ a
        · intro b
          have hb : b = 0 := Subsingleton.elim _ _
          subst b
          simp [loopFuelCaptured, captureCfg, loopFuelCfg, rightCfg, loopFrame, Fin.addCases]
        · intro b
          have hbf : body.k + 1 + (1 + (b : ℕ)) ≠ body.k := by omega
          have hbc : body.k + 1 + (1 + (b : ℕ)) ≠ body.k + 1 := by omega
          have hbp : body.k + 1 + (1 + (b : ℕ)) ≠ body.k + 1 + (1 + F.k) := by omega
          simp [loopFrame, hbf, Nat.ne_of_lt b.isLt]
  · funext i
    refine Fin.lastCases ?_ ?_ i
    · have hf : body.k + 1 + (1 + F.k) ≠ body.k := by omega
      simp [loopFuelCaptured, captureCfg, loopFuelCfg, rightCfg, loopFrame, hf]
    · intro j
      refine Fin.addCases ?_ ?_ j
      · intro a
        have ha : (a : ℕ) < body.k + 1 + (1 + F.k) := by omega
        have han : (a : ℕ) ≠ body.k + 1 := by omega
        have hap : (a : ℕ) ≠ body.k + 1 + (1 + F.k) := by omega
        simp [loopFuelCaptured, captureCfg, loopFuelCfg, rightCfg, loopFrame, ha, han, hap, Fin.addCases, a.isLt]
      · intro a
        refine Fin.addCases ?_ ?_ a
        · intro b
          have hb : b = 0 := Subsingleton.elim _ _
          subst b
          simp [loopFuelCaptured, captureCfg, loopFuelCfg, rightCfg, loopFrame, Fin.addCases]
        · intro b
          have hbf : body.k + 1 + (1 + (b : ℕ)) ≠ body.k := by omega
          have hbc : body.k + 1 + (1 + (b : ℕ)) ≠ body.k + 1 := by omega
          have hbp : body.k + 1 + (1 + (b : ℕ)) ≠ body.k + 1 + (1 + F.k) := by omega
          simp [loopFrame, hbf, Nat.ne_of_lt b.isLt]

/-- Fuel execution, setup, and input rewind reach prepared body startup
within `5*T+7` steps, retaining the actual fuel endpoint.
**Proof sketch.** Replace the supplied padded fuel run by its first halt,
relocate it twice, and capture it in the actual host. Setup costs `3L+4`,
where `L ≤ T`; the input rewind costs at most the first run's displacement
plus two, hence at most `T+3`. No bound in the input length is used. -/
private lemma loopHost_prepare (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) (R T : ℕ → ℕ)
    (hF : F.ComputesFunInTime (fun x => Nat.bits (R x.length)) T) (x : List Bool) :
    ∃ (c : Cfg F.k Bool F.State x) (t : ℕ),
      c.state = none ∧ c.output = Nat.bits (R x.length) ∧ t ≤ 5 * T x.length + 7 ∧
      (loopHost body F anchor findMode).tm.runFrom
        ((loopHost body F anchor findMode).tm.initCfg x) t = loopReady body F c := by
  obtain ⟨space, hhalt, hout, hspace⟩ := hF x
  obtain ⟨u, hu, hut, hlive, huh, hue⟩ :=
    loop_first_halt F.tm (F.tm.initCfg x) (T x.length) (by simp [MultiTapeTM.initCfg, Cfg.init]) hhalt
  let c := F.tm.runFrom (F.tm.initCfg x) u
  have hc : c.state = none := huh
  have ho : c.output = Nat.bits (R x.length) := by dsimp only [c]; rw [hue]; exact hout
  have hcap : (loopHost body F anchor findMode).tm.runFrom
      ((loopHost body F anchor findMode).tm.initCfg x) u = loopFuelCaptured body F c := by
    rw [loopHost_init, loopFuel_init]
    rw [loopHost_fuel_capture]
    · rw [loopFuel_run]; rfl
    · intro v hv
      rw [loopFuel_run]
      simpa [Cfg.Halted, loopFuelCfg, rightCfg] using hlive v hv
  let prepared := loopFrame body F (loopFuelCaptured body F c)
    (some (.inr (.inr 4))) c.inputPos (bufferTape []) (bufferTape c.output)
    (bufferTape []) 0 0 []
  have hsetup : (loopHost body F anchor findMode).tm.runFrom
      (loopFuelCaptured body F c) (3 * c.output.length + 4) = prepared := by
    conv_lhs => arg 1; rw [loopFuelCaptured_frame body F c hc]
    exact loopHost_fuel_setup body F anchor findMode _ _ _ _ _
  obtain ⟨v, hv, hrew⟩ := loopHost_input_rewind body F anchor findMode prepared rfl
  have hw : c.output.length ≤ T x.length := by rw [ho]; exact loop_fuel_width F R T hF x
  have hp : c.inputPos.val ≤ 1 + u := loop_input_run_le F.tm (F.tm.initCfg x) u
  refine ⟨c, u + (3 * c.output.length + 4) + v, hc, ho, ?_, ?_⟩
  · change v ≤ c.inputPos.val + 2 at hv
    omega
  · rw [MultiTapeTM.runFrom_add,
      MultiTapeTM.runFrom_add (a := u) (b := 3 * c.output.length + 4), hcap, hsetup, hrew]
    rfl

/-- The stopped body's padded source configuration, preserving the counter
word and the complete fuel residue through every call. -/
private def loopBodyPadded (body F : FinTM Bool) (anchor : body.State) {x : List Bool}
    (c : Cfg body.k Bool body.State x) (release : Bool) (flag : Option Bool)
    (word : List Bool) (fuel : Cfg F.k Bool F.State x) :
    Cfg (body.k + 1 + (1 + F.k)) Bool (body.State × Bool) x :=
  leftCfg id (loopBodyCfg body anchor c release flag)
    (Fin.addCases (fun (_ : Fin 1) => bufferTape word) fuel.workTapes)
    (Fin.addCases (fun (_ : Fin 1) => 0) fuel.workTapePos)

/-- A body call viewed inside the concrete capturing host. A halted stopped
body is represented by the corresponding startup/active return phase. -/
private def loopCall (body F : FinTM Bool) (anchor : body.State) {x : List Bool}
    (startup : Bool) (c : Cfg body.k Bool body.State x) (release : Bool)
    (flag : Option Bool) (word : List Bool) (fuel : Cfg F.k Bool F.State x) :
    Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x :=
  captureCfg (fun s => Sum.inr (Sum.inl (startup, s)))
    (Sum.inr (Sum.inr (if startup then 6 else 7 : Fin 14))) [] []
    (loopBodyPadded body F anchor c release flag word fuel)

/-- The padded body source simulates the stopped body with arbitrary inactive
counter and fuel tracks. -/
private lemma loopBodySource_run (body F : FinTM Bool) (anchor : body.State)
    {x : List Bool}
    (c : Cfg (body.k + 1) Bool (body.State × Bool) x)
    (tapes : Fin (1 + F.k) → ℤ → Option Bool) (heads : Fin (1 + F.k) → ℤ) (t : ℕ) :
    (loopBodySource body F anchor).runFrom (leftCfg id c tapes heads) t =
      leftCfg id ((loopBodyTM body anchor).tm.runFrom c t) tapes heads :=
  leftCfg_run (loopBodyTM body anchor).tm (loopBodySource body F anchor)
    id (fun _ _ _ => rfl) c tapes heads t

/-- A live anchor endpoint is captured after one additional stop step.
The exact endpoint keeps every inactive tape and carries the false stop flag.
**Proof sketch.** The live endpoint rules out earlier halts. Use the source
wrapper simulation up to that endpoint, take its silent anchor-stop step,
and lift the resulting run through the padded source and actual host capture.
The guard at time zero is supplied by the release bit for active calls. -/
private lemma loopHost_anchor_return (body F : FinTM Bool) (anchor : body.State)
    (findMode startup : Bool) {x : List Bool}
    (c : Cfg body.k Bool body.State x) (release : Bool) (t : ℕ)
    (word : List Bool) (fuel : Cfg F.k Bool F.State x)
    (hend : (body.tm.runFrom c t).state = some anchor)
    (hreleased : t = 0 → release = false)
    (hanchor : ∀ u < t, (u = 0 ∧ release = true) ∨
      (body.tm.runFrom c u).state ≠ some anchor) :
    (loopHost body F anchor findMode).tm.runFrom
        (loopCall body F anchor startup c release none word fuel) (t + 1) =
      loopCall body F anchor startup {body.tm.runFrom c t with state := none}
        false (some false) word fuel := by
  have hlive : ∀ u ≤ t, (body.tm.runFrom c u).state ≠ none :=
    loop_live_prefix body.tm c t (by rw [hend]; simp)
  have hc : c.state ≠ none := by simpa using hlive 0 (Nat.zero_le _)
  have hr : (loopBodyTM body anchor).tm.runFrom (loopBodyCfg body anchor c release none) t =
      loopBodyCfg body anchor (body.tm.runFrom c t) false none := by
    rw [loopBody_run body anchor c release hc t
      (fun u hu => hlive u (by omega)) hanchor]
    have hn := hlive t (le_refl _)
    rw [if_neg hn]
    by_cases ht : t = 0
    · rw [if_pos ht, hreleased ht]
    · rw [if_neg ht]
  have hstop : (loopBodyTM body anchor).tm.runFrom (loopBodyCfg body anchor c release none)
      (t + 1) =
      loopBodyCfg body anchor {body.tm.runFrom c t with state := none} false (some false) := by
    rw [MultiTapeTM.runFrom_succ_eq_step', hr, loopBody_stop body anchor _ hend]
  unfold loopCall loopBodyPadded
  rw [loopHost_body_capture]
  · rw [loopBodySource_run, hstop]
  · intro u hu
    rw [loopBodySource_run, loopBody_run body anchor c release hc u
      (fun v hv => hlive v (by omega)) (fun v hv => hanchor v (by omega))]
    simpa [Cfg.Halted, leftCfg, loopBodyCfg] using hlive u (by omega)

/-- Prepared fuel startup is the canonical captured body call on blank body
tapes; the counter and fuel residue are exactly the padded inactive block.
**Proof sketch.** Compare the four physical tape blocks. The input head and
all active heads are at their origins; only the completed fuel bank has
arbitrary contents and head positions. -/
private lemma loopReady_call (body F : FinTM Bool) (anchor : body.State)
    {x : List Bool} (fuel : Cfg F.k Bool F.State x) :
    loopReady body F fuel =
      loopCall body F anchor true (body.tm.initCfg x) false none fuel.output fuel := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  all_goals
    funext i
    refine Fin.lastCases ?_ ?_ i
    · have hf : body.k + 1 + (1 + F.k) ≠ body.k := by omega
      simp [loopReady, loopFrame, loopCall, captureCfg, loopBodyPadded, leftCfg,
        loopBodyCfg, MultiTapeTM.initCfg, Cfg.init, hf]
    · intro j
      refine Fin.addCases ?_ ?_ j
      · intro a
        have ha : (a : ℕ) < body.k + 1 + (1 + F.k) := by omega
        have han : (a : ℕ) ≠ body.k + 1 := by omega
        have hap : (a : ℕ) ≠ body.k + 1 + (1 + F.k) := by omega
        simp [loopReady, loopFrame, loopCall, captureCfg, loopBodyPadded, leftCfg,
          loopBodyCfg, MultiTapeTM.initCfg, Cfg.init, loopFuelCaptured, loopFuelCfg,
          rightCfg, ha, han, hap, Fin.addCases, a.isLt]
      · intro a
        refine Fin.addCases ?_ ?_ a
        · intro b
          have hb : b = 0 := Subsingleton.elim _ _
          subst b
          simp [loopReady, loopFrame, loopCall, captureCfg, loopBodyPadded, leftCfg,
            loopBodyCfg, MultiTapeTM.initCfg, Cfg.init, Fin.addCases]
        · intro b
          have hbf : body.k + 1 + (1 + (b : ℕ)) ≠ body.k := by omega
          have hb : (b : ℕ) < F.k := b.isLt
          simp [loopReady, loopFrame, loopCall, captureCfg, loopBodyPadded, leftCfg,
            loopBodyCfg, MultiTapeTM.initCfg, Cfg.init, loopFuelCaptured, loopFuelCfg,
            rightCfg, hbf, hb, Nat.ne_of_lt hb, Fin.addCases]

/-- Phase 6 clears startup's false flag and releases the first anchor for
free. It changes no body, counter, or fuel data.
**Proof sketch.** The captured stopped body is in phase 6. Its sole write
clears the flag's origin cell. Comparing tape blocks identifies the result
with the active released call on the same body data. -/
private lemma loopHost_release (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool} (c : Cfg body.k Bool body.State x)
    (word : List Bool) (fuel : Cfg F.k Bool F.State x) :
    (loopHost body F anchor findMode).tm.step
        (loopCall body F anchor true {c with state := none} false (some false) word fuel) =
      loopCall body F anchor false {c with state := some anchor} true none word fuel := by
  change (loopControlAction body F 0 (some none) (none, 0) (none, 0) none
    (some (.inr (.inl (false, (anchor, true)))))).apply _ = _
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ ?_
  · funext i z
    by_cases hf : (i : ℕ) = body.k
    · have hi : body.k < body.k + 1 + (1 + F.k) := by omega
      simp [Action.apply, loopControlAction, loopCall, captureCfg, loopBodyPadded,
        leftCfg, loopBodyCfg, hf, hi, Fin.addCases, Function.update]
    · by_cases hb : (i : ℕ) < body.k + 1
      · have hi : (i : ℕ) < body.k := by omega
        simp [Action.apply, loopControlAction, loopCall, captureCfg, loopBodyPadded,
          leftCfg, loopBodyCfg, hf, Fin.addCases, hb, hi]
      · simp [Action.apply, loopControlAction, loopCall, captureCfg, loopBodyPadded,
          leftCfg, loopBodyCfg, hf, Fin.addCases, hb]
  · funext i
    by_cases hf : (i : ℕ) = body.k <;>
      simp [Action.apply, loopControlAction, loopCall, captureCfg, loopBodyPadded,
        leftCfg, loopBodyCfg, hf]
  · simp [Action.apply, loopControlAction, loopCall, captureCfg]

/-- Genuine body startup reaches the released first candidate in at most
its source startup time plus two host steps.
**Proof sketch.** The no-anchor prefix includes time zero, so startup is
captured without a premature stop. Its live endpoint yields the false flag;
one stop step and phase 6's flag-clear step release the initial candidate. -/
private lemma loopHost_start (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool} (s : List Bool) (t : ℕ)
    (fuel : Cfg F.k Bool F.State x)
    (hguard : ∀ u < t, (body.tm.runFrom (body.tm.initCfg x) u).state ≠ some anchor)
    (hend : body.tm.runFrom (body.tm.initCfg x) t = Cfg.ofWords anchor (stateWord body.k s)) :
    (loopHost body F anchor findMode).tm.runFrom (loopReady body F fuel) (t + 2) =
      loopCall body F anchor false (Cfg.ofWords anchor (stateWord body.k s))
        true none fuel.output fuel := by
  rw [loopReady_call body F anchor, show t + 2 = (t + 1) + 1 by omega,
    MultiTapeTM.runFrom_succ_eq_step']
  rw [loopHost_anchor_return body F anchor findMode true (body.tm.initCfg x) false t
    fuel.output fuel (by rw [hend]; rfl) (fun _ => rfl) (fun u hu => Or.inr (hguard u hu))]
  rw [hend, loopHost_release body F anchor findMode _ _ _]
  rfl

/-- A genuine first halt returns to phase 7 with the true stop flag and the
entire source output captured, including its halting emission.
**Proof sketch.** Simulate the released body through its first halting action.
Strict liveness permits actual-host capture throughout; the positive duration
consumes the release bit and the halting action sets the true flag. -/
private lemma loopHost_halt_return (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool} (c : Cfg body.k Bool body.State x)
    (t : ℕ) (word : List Bool) (fuel : Cfg F.k Bool F.State x)
    (ht : 0 < t) (hlive : ∀ u < t, (body.tm.runFrom c u).state ≠ none)
    (hanchor : ∀ u, 0 < u → u < t → (body.tm.runFrom c u).state ≠ some anchor)
    (hend : (body.tm.runFrom c t).state = none) :
    (loopHost body F anchor findMode).tm.runFrom
        (loopCall body F anchor false c true none word fuel) t =
      loopCall body F anchor false (body.tm.runFrom c t) false (some true) word fuel := by
  have hc : c.state ≠ none := by simpa using hlive 0 ht
  have hg : ∀ u < t, (u = 0 ∧ true = true) ∨
      (body.tm.runFrom c u).state ≠ some anchor := by
    intro u hu
    by_cases hz : u = 0
    · exact Or.inl ⟨hz, rfl⟩
    · exact Or.inr (hanchor u (by omega) hu)
  unfold loopCall loopBodyPadded
  rw [loopHost_body_capture]
  · rw [loopBodySource_run, loopBody_run body anchor c true hc t hlive hg]
    simp [hend, Nat.ne_of_gt ht]
  · intro u hu
    rw [loopBodySource_run, loopBody_run body anchor c true hc u
      (fun v hv => hlive v (by omega)) (fun v hv => hg v (by omega))]
    simpa [Cfg.Halted, leftCfg, loopBodyCfg] using hlive u hu

/-- A captured body call has the explicit flag, counter, and payload tracks
used by the controller frame, with arbitrary inactive body and fuel residue. -/
private lemma loopCall_frame (body F : FinTM Bool) (anchor : body.State)
    {x : List Bool} (startup : Bool) (c : Cfg body.k Bool body.State x)
    (release : Bool) (flag : Option Bool) (word : List Bool) (fuel : Cfg F.k Bool F.State x) :
    loopCall body F anchor startup c release flag word fuel =
      loopFrame body F (loopCall body F anchor startup c release flag word fuel)
        (loopCall body F anchor startup c release flag word fuel).state c.inputPos
        (fun z => if z = 0 then flag else none) (bufferTape word) (bufferTape c.output)
        0 c.output.length [] := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  all_goals
    funext i
    by_cases hf : (i : ℕ) = body.k
    · have hlt : body.k < body.k + 1 + (1 + F.k) := by omega
      simp [loopFrame, loopCall, captureCfg, loopBodyPadded, leftCfg, loopBodyCfg,
        hf, hlt, Fin.addCases]
    · by_cases hc : (i : ℕ) = body.k + 1
      · simp [loopFrame, loopCall, captureCfg, loopBodyPadded, leftCfg, loopBodyCfg,
          hc, Fin.addCases]
      · by_cases hp : (i : ℕ) = body.k + 1 + (1 + F.k)
        · have hpf : body.k + 1 + (1 + F.k) ≠ body.k := by omega
          simp [loopFrame, loopCall, captureCfg, loopBodyPadded, leftCfg, loopBodyCfg, hp, hpf]
        · simp [loopFrame, hf, hc, hp]

/-- Reframing a body call changes precisely its control, flag, and counter.
**Proof sketch.** The source configuration changes only in state. Thus all
inactive body and fuel data coincide; compare the three explicitly replaced
tracks and retain every other physical tape and head. -/
private lemma loopCall_reframe (body F : FinTM Bool) (anchor : body.State)
    {x : List Bool} (c : Cfg body.k Bool body.State x)
    (startup startup' release release' : Bool) (flag flag' : Option Bool)
    (word word' : List Bool) (fuel : Cfg F.k Bool F.State x) (q : Option body.State) :
    loopFrame body F (loopCall body F anchor startup c release flag word fuel)
        (loopCall body F anchor startup' {c with state := q} release' flag' word' fuel).state
        c.inputPos (fun z => if z = 0 then flag' else none) (bufferTape word')
        (bufferTape c.output) 0 c.output.length [] =
      loopCall body F anchor startup' {c with state := q} release' flag' word' fuel := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  all_goals
    funext i
    by_cases hf : (i : ℕ) = body.k
    · have hlt : body.k < body.k + 1 + (1 + F.k) := by omega
      simp [loopFrame, loopCall, captureCfg, loopBodyPadded, leftCfg, loopBodyCfg,
        hf, hlt, Fin.addCases]
    · by_cases hc : (i : ℕ) = body.k + 1
      · simp [loopFrame, loopCall, captureCfg, loopBodyPadded, leftCfg, loopBodyCfg,
          hc, Fin.addCases]
      · by_cases hp : (i : ℕ) = body.k + 1 + (1 + F.k)
        · have hpf : body.k + 1 + (1 + F.k) ≠ body.k := by omega
          simp [loopFrame, loopCall, captureCfg, loopBodyPadded, leftCfg, loopBodyCfg, hp, hpf]
        · by_cases hb : (i : ℕ) < body.k + 1
          · have hi : (i : ℕ) < body.k := by omega
            simp [loopFrame, loopCall, captureCfg, loopBodyPadded, leftCfg, loopBodyCfg,
              hf, hc, hp, Fin.addCases, hb, hi]
          · have hn : (i : ℕ) - (body.k + 1) ≠ 0 := by omega
            simp [loopFrame, loopCall, captureCfg, loopBodyPadded, leftCfg, loopBodyCfg,
              hf, hc, hp, Fin.addCases, hb, hn]

/-- One actual-host borrow step changes only the counter, recording success
or underflow in the rewind phase. -/
private lemma loopHost_borrow_step (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x)
    (p : Fin (x.length + 2)) (pre rest : List Bool) :
    (loopHost body F anchor findMode).tm.step
      (loopFrame body F base (some (.inr (.inr 8))) p (bufferTape [])
        (bufferTape (pre ++ rest)) (bufferTape []) pre.length 0 []) =
      match rest with
      | [] => loopFrame body F base (some (.inr (.inr 10))) p (bufferTape [])
          (bufferTape pre) (bufferTape []) (pre.length - 1) 0 []
      | true :: us => loopFrame body F base (some (.inr (.inr 9))) p (bufferTape [])
          (bufferTape (pre ++ false :: us)) (bufferTape []) (pre.length - 1) 0 []
      | false :: us => loopFrame body F base (some (.inr (.inr 8))) p (bufferTape [])
          (bufferTape (pre ++ true :: us)) (bufferTape []) (pre.length + 1) 0 [] := by
  change (match (loopFrame body F base (some (.inr (.inr 8))) p (bufferTape [])
      (bufferTape (pre ++ rest)) (bufferTape []) pre.length 0 []).workTapeSymbols
        ⟨body.k + 1, by omega⟩ with
    | some false => loopControlAction body F 0 none (some (some true), .pos) (none, 0)
        none (some (.inr (.inr 8)))
    | some true => loopControlAction body F 0 none (some (some false), .neg) (none, 0)
        none (some (.inr (.inr 9)))
    | none => loopControlAction body F 0 none (none, .neg) (none, 0) none
        (some (.inr (.inr 10)))).apply _ = _
  rw [loopFrame_counter, loopBuffer_read]
  cases rest with
  | nil =>
    simp only [List.head?]
    rw [loopControl_apply]
    simp [loopWrite, sub_eq_add_neg]
  | cons b rest =>
    cases b <;> simp only [List.head?]
    all_goals rw [loopControl_apply]; simp [loopWrite, loopBuffer_write, sub_eq_add_neg]

/-- The actual host performs the borrow scan in the standalone scan's exact
time, preserving all non-counter tracks.
**Proof sketch.** Induct on the remaining word. Each false bit advances the
processed prefix. A true bit or the right blank starts the appropriate
rewind phase; no cell outside the original counter width is written. -/
private lemma loopHost_borrow_run (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x)
    (p : Fin (x.length + 2)) (word : List Bool) : ∀ pre,
    (loopHost body F anchor findMode).tm.runFrom
        (loopFrame body F base (some (.inr (.inr 8))) p (bufferTape [])
          (bufferTape (pre ++ word)) (bufferTape []) pre.length 0 [])
        (loopBorrowPos word + 1) =
      loopFrame body F base (some (.inr (.inr (if (loopDebit word).2 then 9 else 10)))) p
        (bufferTape []) (bufferTape (pre ++ (loopDebit word).1)) (bufferTape [])
        ((pre.length : ℤ) + loopBorrowPos word - 1) 0 [] := by
  induction word with
  | nil =>
    intro pre
    simpa [loopBorrowPos, loopDebit, MultiTapeTM.runFrom_succ_eq_step] using
      loopHost_borrow_step body F anchor findMode base p pre []
  | cons b word ih =>
    intro pre
    cases b with
    | true =>
      simpa [loopBorrowPos, loopDebit, MultiTapeTM.runFrom_succ_eq_step] using
        loopHost_borrow_step body F anchor findMode base p pre (true :: word)
    | false =>
      simp only [loopBorrowPos]
      rw [MultiTapeTM.runFrom_succ_eq_step, loopHost_borrow_step]
      simpa [loopDebit, List.append_assoc, Nat.cast_add, Nat.cast_one,
        add_assoc, add_comm, add_left_comm] using ih (pre ++ [true])

/-- The host's success/underflow rewind returns the counter head to zero.
Success releases the next anchor; underflow enters phase 11 without yet
emitting. Both paths retain all inactive residue.
**Proof sketch.** Induct on the number of counter cells to the left. The
left-blank test dispatches according to the stored success bit. -/
private lemma loopHost_borrow_rewind (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x)
    (p : Fin (x.length + 2)) (word : List Bool) (success : Bool) :
    ∀ j, j ≤ word.length →
    (loopHost body F anchor findMode).tm.runFrom
        (loopFrame body F base (some (.inr (.inr (if success then 9 else 10)))) p
          (bufferTape []) (bufferTape word) (bufferTape []) ((j : ℤ) - 1) 0 []) (j + 1) =
      loopFrame body F base
        (some (if success then .inr (.inl (false, (anchor, true))) else .inr (.inr 11))) p
        (bufferTape []) (bufferTape word) (bufferTape []) 0 0 [] := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    cases success <;>
      (change (match (loopFrame body F base _ p (bufferTape []) (bufferTape word)
          (bufferTape []) ((0 : ℤ) - 1) 0 []).workTapeSymbols ⟨body.k + 1, by omega⟩ with
        | some _ => loopControlAction body F 0 none (none, .neg) (none, 0) none _
        | none => loopControlAction body F 0 none (none, .pos) (none, 0) none _).apply _ = _)
    all_goals
      rw [loopFrame_counter]
      simp only [zero_sub, bufferTape_left]
      rw [loopControl_apply]
      simp [loopWrite]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hs : (loopHost body F anchor findMode).tm.step
        (loopFrame body F base (some (.inr (.inr (if success then 9 else 10)))) p
          (bufferTape []) (bufferTape word) (bufferTape []) (((j + 1 : ℕ) : ℤ) - 1) 0 []) =
        loopFrame body F base (some (.inr (.inr (if success then 9 else 10)))) p
          (bufferTape []) (bufferTape word) (bufferTape []) ((j : ℤ) - 1) 0 [] := by
      cases success <;>
        (change (match (loopFrame body F base _ p (bufferTape []) (bufferTape word)
            (bufferTape []) (((j + 1 : ℕ) : ℤ) - 1) 0 []).workTapeSymbols
              ⟨body.k + 1, by omega⟩ with
          | some _ => loopControlAction body F 0 none (none, .neg) (none, 0) none _
          | none => loopControlAction body F 0 none (none, .pos) (none, 0) none _).apply _ = _)
      all_goals
        rw [loopFrame_counter, show ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) by omega,
          bufferTape_nat, List.getElem?_eq_getElem (by omega : j < word.length)]
        rw [loopControl_apply]
        simp [loopWrite, sub_eq_add_neg]
    rw [hs]
    exact ih (by omega)

/-- The complete actual-host counter operation has the fixed-width
worst-case bound `2|word|+2`, covering underflow and width zero. -/
private lemma loopHost_borrow (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x)
    (p : Fin (x.length + 2)) (word : List Bool) :
    2 * loopBorrowPos word + 2 ≤ 2 * word.length + 2 ∧
    (loopHost body F anchor findMode).tm.runFrom
        (loopFrame body F base (some (.inr (.inr 8))) p (bufferTape [])
          (bufferTape word) (bufferTape []) 0 0 []) (2 * loopBorrowPos word + 2) =
      loopFrame body F base
        (some (if (loopDebit word).2 then .inr (.inl (false, (anchor, true)))
          else .inr (.inr 11))) p
        (bufferTape []) (bufferTape (loopDebit word).1) (bufferTape []) 0 0 [] := by
  refine ⟨by have := loopBorrowPos_le word; omega, ?_⟩
  have hr := loopHost_borrow_run body F anchor findMode base p word []
  simp only [List.length_nil, Nat.cast_zero, List.nil_append, zero_add] at hr
  rw [show 2 * loopBorrowPos word + 2 =
      (loopBorrowPos word + 1) + (loopBorrowPos word + 1) by omega,
    MultiTapeTM.runFrom_add, hr]
  exact loopHost_borrow_rewind body F anchor findMode base p (loopDebit word).1
    (loopDebit word).2 _ (by rw [loopDebit_length]; exact loopBorrowPos_le word)

/-- The flag read is at its fixed origin, independently of inactive residue. -/
private lemma loopFrame_flag (body F : FinTM Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x)
    (q : Option (LoopHostState body F)) (p : Fin (x.length + 2))
    (flag counter payload : ℤ → Option Bool) (ch ph : ℤ) (out : List Bool) :
    (loopFrame body F base q p flag counter payload ch ph out).workTapeSymbols
        ⟨body.k, by omega⟩ = flag 0 := by
  simp [loopFrame, Cfg.workTapeSymbols]

/-- Clearing the only flag cell leaves a completely blank flag tape. -/
private lemma loopFlag_clear (flag : Option Bool) :
    loopWrite (fun z : ℤ => if z = 0 then flag else none) 0 (some none) = bufferTape [] := by
  funext z
  by_cases hz : z = 0 <;> simp [loopWrite, Function.update, hz]

/-- A rejecting stopped call clears its flag, debits in worst-case width
time, and either releases the next anchor or emits exhaustion and halts.
Underflow and its emission are included in this same segment.
**Proof sketch.** Phase 7 clears the false flag in one step. The proved host
borrow takes `2j+2` steps. Success is the reframed next body seam; underflow
takes one additional phase-11 step, for at most `2|word|+4` steps in total. -/
private lemma loopHost_reject (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool} (c : Cfg body.k Bool body.State x)
    (word : List Bool) (fuel : Cfg F.k Bool F.State x)
    (hc : c.state = none) (ho : c.output = []) :
    ∃ t ≤ 2 * word.length + 4,
      if (loopDebit word).2 then
        (loopHost body F anchor findMode).tm.runFrom
            (loopCall body F anchor false c false (some false) word fuel) t =
          loopCall body F anchor false {c with state := some anchor} true none (loopDebit word).1 fuel
      else
        ((loopHost body F anchor findMode).tm.runFrom
          (loopCall body F anchor false c false (some false) word fuel) t).state = none ∧
        ((loopHost body F anchor findMode).tm.runFrom
          (loopCall body F anchor false c false (some false) word fuel) t).output =
            (if findMode then [] else [false]) := by
  let base := loopCall body F anchor false c false (some false) word fuel
  have hs : base.state = some (.inr (.inr (7 : Fin 14))) := by
    simp [base, loopCall, captureCfg, loopBodyPadded, leftCfg, loopBodyCfg, hc]
  have hf : base = loopFrame body F base (some (.inr (.inr 7))) c.inputPos
      (fun z => if z = 0 then some false else none) (bufferTape word) (bufferTape []) 0 0 [] := by
    have h := loopCall_frame body F anchor false c false (some false) word fuel
    have hstate : (loopCall body F anchor false c false (some false) word fuel).state =
        some (.inr (.inr (7 : Fin 14))) := hs
    simpa only [hstate, ho, List.length_nil, Nat.cast_zero] using h
  have hstep : (loopHost body F anchor findMode).tm.step base =
      loopFrame body F base (some (.inr (.inr 8))) c.inputPos
        (bufferTape []) (bufferTape word) (bufferTape []) 0 0 [] := by
    conv_lhs => arg 1; rw [hf]
    change (if (loopFrame body F base (some (.inr (.inr 7))) c.inputPos
        (fun z => if z = 0 then some false else none) (bufferTape word) (bufferTape []) 0 0 []).workTapeSymbols
          ⟨body.k, by omega⟩ = some true then _
      else loopControlAction body F 0 (some none) (none, 0) (none, 0) none
        (some (.inr (.inr 8)))).apply _ = _
    rw [loopFrame_flag]
    change (loopControlAction body F 0 (some none) (none, 0) (none, 0) none
      (some (.inr (.inr 8)))).apply _ = _
    rw [loopControl_apply, loopFlag_clear]
    simp [loopWrite]
  have hrun : (loopHost body F anchor findMode).tm.runFrom base (2 * loopBorrowPos word + 3) =
      loopFrame body F base
        (some (if (loopDebit word).2 then .inr (.inl (false, (anchor, true)))
          else .inr (.inr 11))) c.inputPos
        (bufferTape []) (bufferTape (loopDebit word).1) (bufferTape []) 0 0 [] := by
    rw [show 2 * loopBorrowPos word + 3 = (2 * loopBorrowPos word + 2) + 1 by omega,
      MultiTapeTM.runFrom_succ_eq_step, hstep]
    exact (loopHost_borrow body F anchor findMode base c.inputPos word).2
  have hw := loopBorrowPos_le word
  by_cases hb : (loopDebit word).2 = true
  · refine ⟨2 * loopBorrowPos word + 3, by omega, ?_⟩
    simp only [hb, if_true] at hrun ⊢
    rw [hrun]
    have h := loopCall_reframe body F anchor c false false false true (some false) none
      word (loopDebit word).1 fuel (some anchor)
    simpa [base, loopCall, captureCfg, loopBodyPadded, leftCfg, loopBodyCfg, ho] using h
  · refine ⟨2 * loopBorrowPos word + 4, by omega, ?_⟩
    simp only [hb] at hrun ⊢
    have hh : (loopHost body F anchor findMode).tm.runFrom base (2 * loopBorrowPos word + 4) =
        loopFrame body F base none c.inputPos (bufferTape []) (bufferTape (loopDebit word).1)
          (bufferTape []) 0 0 (if findMode then [] else [false]) := by
      rw [show 2 * loopBorrowPos word + 4 = (2 * loopBorrowPos word + 3) + 1 by omega,
        MultiTapeTM.runFrom_succ_eq_step', hrun]
      change (loopControlAction body F 0 none (none, 0) (none, 0)
        (if findMode then none else some false) none).apply _ = _
      rw [loopControl_apply]
      cases findMode <;> simp [loopWrite]
    rw [hh]
    exact ⟨rfl, rfl⟩

/-- Accepting-payload phase 12 scans to the left blank and returns at the origin.
**Proof sketch.** Induct on the number of stored cells to the left. At zero,
the head is on the left blank; otherwise its cell is nonblank and the left
move reduces that number. All other tracks and the native input are retained. -/
private lemma loopHost_payload_rewind (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x)
    (p : Fin (x.length + 2)) (flag counter : ℤ → Option Bool)
    (ch : ℤ) (word out : List Bool) : ∀ j, j ≤ word.length →
    (loopHost body F anchor findMode).tm.runFrom
        (loopFrame body F base (some (.inr (.inr 12))) p flag counter
          (bufferTape word) ch ((j : ℤ) - 1) out) (j + 1) =
      loopFrame body F base (some (.inr (.inr 13))) p flag counter
        (bufferTape word) ch 0 out := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    change (match (loopFrame body F base (some (.inr (.inr 12))) p flag counter
        (bufferTape word) ch ((0 : ℤ) - 1) out).workTapeSymbols
          (Fin.last (body.k + 1 + (1 + F.k))) with
      | some _ => loopControlAction body F 0 none (none, 0) (none, .neg) none
          (some (.inr (.inr 12)))
      | none => loopControlAction body F 0 none (none, 0) (none, .pos) none
          (some (.inr (.inr 13)))).apply _ = _
    rw [loopFrame_payload]
    simp only [zero_sub, bufferTape_left]
    rw [loopControl_apply]
    simp [loopWrite]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hs : (loopHost body F anchor findMode).tm.step
        (loopFrame body F base (some (.inr (.inr 12))) p flag counter
          (bufferTape word) ch (((j + 1 : ℕ) : ℤ) - 1) out) =
        loopFrame body F base (some (.inr (.inr 12))) p flag counter
          (bufferTape word) ch ((j : ℤ) - 1) out := by
      change (match (loopFrame body F base (some (.inr (.inr 12))) p flag counter
          (bufferTape word) ch (((j + 1 : ℕ) : ℤ) - 1) out).workTapeSymbols
            (Fin.last (body.k + 1 + (1 + F.k))) with
        | some _ => loopControlAction body F 0 none (none, 0) (none, .neg) none
            (some (.inr (.inr 12)))
        | none => loopControlAction body F 0 none (none, 0) (none, .pos) none
            (some (.inr (.inr 13)))).apply _ = _
      rw [loopFrame_payload]
      rw [show ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) by omega,
        bufferTape_nat, List.getElem?_eq_getElem (by omega : j < word.length)]
      rw [loopControl_apply]
      simp [loopWrite, sub_eq_add_neg]
    rw [hs]
    exact ih (by omega)

/-- Phase 13 replays a framed payload, retaining arbitrary inactive tracks.
**Proof sketch.** Express the frame as the right-block replay configuration
using its own inactive tape and head projections, then apply the already
proved actual-host replay correspondence. -/
private lemma loopHost_frame_replay (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x)
    (p : Fin (x.length + 2)) (flag counter : ℤ → Option Bool) (ch : ℤ) (word : List Bool) :
    let c := loopFrame body F base (some (.inr (.inr 13))) p flag counter (bufferTape word) ch 0 []
    ((loopHost body F anchor findMode).tm.runFrom c (word.length + 1)).state = none ∧
    ((loopHost body F anchor findMode).tm.runFrom c (word.length + 1)).output = word := by
  dsimp only
  let c := loopFrame body F base (some (.inr (.inr 13))) p flag counter (bufferTape word) ch 0 []
  let tapes := fun i : Fin (body.k + 1 + (1 + F.k)) => c.workTapes i.castSucc
  let heads := fun i : Fin (body.k + 1 + (1 + F.k)) => c.workTapePos i.castSucc
  have he : c = rightCfg (fun _ : Unit => Sum.inr (Sum.inr (13 : Fin 14)))
      (loopReplayCfg x p (some ()) 0 word []) tapes heads := by
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
        simp [c, rightCfg, loopReplayCfg, loopFrame, hf]
  change ((loopHost body F anchor findMode).tm.runFrom c _).state = _ ∧
    ((loopHost body F anchor findMode).tm.runFrom c _).output = _
  rw [he, loopHost_replay]
  exact ⟨rfl, rfl⟩

/-- An accepting stopped call emits its fixed verdict or replays its full
captured payload, including the empty payload, within `2|output|+3` steps.
**Proof sketch.** The true stop flag dispatches acceptance independently of
payload length. Decision mode emits immediately. Find mode takes one left
move, the length-plus-one rewind, and the length-plus-one replay. -/
private lemma loopHost_accept (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool} (c : Cfg body.k Bool body.State x)
    (word : List Bool) (fuel : Cfg F.k Bool F.State x) (hc : c.state = none) :
    ∃ t ≤ 2 * c.output.length + 3,
      ((loopHost body F anchor findMode).tm.runFrom
        (loopCall body F anchor false c false (some true) word fuel) t).state = none ∧
      ((loopHost body F anchor findMode).tm.runFrom
        (loopCall body F anchor false c false (some true) word fuel) t).output =
          (if findMode then c.output else [true]) := by
  let base := loopCall body F anchor false c false (some true) word fuel
  let flag := fun z : ℤ => if z = 0 then some true else none
  have hf : base = loopFrame body F base (some (.inr (.inr 7))) c.inputPos flag
      (bufferTape word) (bufferTape c.output) 0 c.output.length [] := by
    have hstate : (loopCall body F anchor false c false (some true) word fuel).state =
        some (.inr (.inr (7 : Fin 14))) := by
      simp [loopCall, captureCfg, loopBodyPadded, leftCfg, loopBodyCfg, hc]
    simpa only [hstate] using loopCall_frame body F anchor false c false (some true) word fuel
  have hstep : (loopHost body F anchor findMode).tm.step base =
      if findMode then
        loopFrame body F base (some (.inr (.inr 12))) c.inputPos flag
          (bufferTape word) (bufferTape c.output) 0 (c.output.length - 1) []
      else loopFrame body F base none c.inputPos flag
        (bufferTape word) (bufferTape c.output) 0 c.output.length [true] := by
    conv_lhs => arg 1; rw [hf]
    change (if (loopFrame body F base (some (.inr (.inr 7))) c.inputPos flag
        (bufferTape word) (bufferTape c.output) 0 c.output.length []).workTapeSymbols
          ⟨body.k, by omega⟩ = some true then _
      else loopControlAction body F 0 (some none) (none, 0) (none, 0) none
        (some (.inr (.inr 8)))).apply _ = _
    rw [loopFrame_flag]
    change (if findMode then
      loopControlAction body F 0 none (none, 0) (none, .neg) none (some (.inr (.inr 12)))
      else loopControlAction body F 0 none (none, 0) (none, 0) (some true) none).apply _ = _
    cases findMode <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      rw [loopControl_apply] <;> simp [loopWrite, sub_eq_add_neg]
  cases findMode with
  | false =>
    refine ⟨1, by omega, ?_⟩
    change ((loopHost body F anchor false).tm.step base).state = none ∧
      ((loopHost body F anchor false).tm.step base).output = [true]
    rw [hstep]
    exact ⟨rfl, rfl⟩
  | true =>
    refine ⟨2 * c.output.length + 3, le_refl _, ?_⟩
    have hrun : (loopHost body F anchor true).tm.runFrom base (2 * c.output.length + 3) =
        (loopHost body F anchor true).tm.runFrom
          (loopFrame body F base (some (.inr (.inr 13))) c.inputPos flag
            (bufferTape word) (bufferTape c.output) 0 0 []) (c.output.length + 1) := by
      rw [show 2 * c.output.length + 3 =
          ((c.output.length + 1) + (c.output.length + 1)) + 1 by omega,
        MultiTapeTM.runFrom_succ_eq_step, hstep]
      simp only [if_true]
      rw [MultiTapeTM.runFrom_add, loopHost_payload_rewind body F anchor true base
        c.inputPos flag (bufferTape word) 0 c.output [] c.output.length (le_refl _)]
    change ((loopHost body F anchor true).tm.runFrom base _).state = _ ∧
      ((loopHost body F anchor true).tm.runFrom base _).output = _
    rw [hrun]
    exact loopHost_frame_replay body F anchor true base c.inputPos flag (bufferTape word) 0 c.output

/-- One body round plus all controller work has a uniform local bound.
Acceptance returns the exact payload/verdict; rejection either reaches the
decremented next seam or finishes underflow within the same segment.
**Proof sketch.** For acceptance, replace a padded endpoint by its first
halt, capture every emission, and use the accepting dispatch bound. At most
one symbol is emitted per source step. For rejection, the live seam supplies
the anchor-stop capture; append the complete width-bounded counter dispatch. -/
private lemma loopHost_round (body F : FinTM Bool) (anchor : body.State)
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
      let start := loopCall body F anchor false (Cfg.ofWords anchor (stateWord body.k s)) true none word fuel
      if accepted then
        ((loopHost body F anchor findMode).tm.runFrom start v).state = none ∧
        ((loopHost body F anchor findMode).tm.runFrom start v).output =
          (if findMode then payload else [true])
      else if (loopDebit word).2 then
        (loopHost body F anchor findMode).tm.runFrom start v =
          loopCall body F anchor false (Cfg.ofWords anchor (stateWord body.k next))
            true none (loopDebit word).1 fuel
      else ((loopHost body F anchor findMode).tm.runFrom start v).state = none ∧
        ((loopHost body F anchor findMode).tm.runFrom start v).output =
          (if findMode then [] else [false]) := by
  dsimp only
  let start := Cfg.ofWords (input := x) anchor (stateWord body.k s)
  by_cases ha : accepted = true
  · simp only [ha, if_true] at hend ⊢
    obtain ⟨u, hu, hut, hlive, hhalt, he⟩ := loop_first_halt body.tm start t (by simp [start, Cfg.ofWords]) hend.1
    have hcap := loopHost_halt_return body F anchor findMode start u word fuel hu hlive
      (fun v hv hvu => hanchor v hv (by omega)) hhalt
    obtain ⟨v, hv, hstop, hout⟩ := loopHost_accept body F anchor findMode (body.tm.runFrom start u) word fuel hhalt
    have hw : (body.tm.runFrom start u).output.length ≤ u := by
      simpa [start, Cfg.ofWords] using loop_output_length_le body.tm start u
    refine ⟨u + v, by omega, ?_⟩
    change ((loopHost body F anchor findMode).tm.runFrom
      (loopCall body F anchor false start true none word fuel) (u + v)).state = _ ∧ _
    rw [MultiTapeTM.runFrom_add, hcap]
    refine ⟨hstop, ?_⟩
    rw [hout, he, hend.2]
  · simp only [ha] at hend ⊢
    have hguard : ∀ u < t, (u = 0 ∧ true = true) ∨ (body.tm.runFrom start u).state ≠ some anchor := by
      intro u hu
      by_cases hz : u = 0
      · exact Or.inl ⟨hz, rfl⟩
      · exact Or.inr (hanchor u (by omega) hu)
    have hcap := loopHost_anchor_return body F anchor findMode false start true t word fuel
      (by rw [hend]; rfl)
      (by intro hz; omega) hguard
    change (loopHost body F anchor findMode).tm.runFrom _ (t + 1) = _ at hcap
    have hr : body.tm.runFrom start t = Cfg.ofWords anchor (stateWord body.k next) := hend
    rw [hr] at hcap
    obtain ⟨v, hv, hfinish⟩ := loopHost_reject body F anchor findMode
      {Cfg.ofWords (input := x) anchor (stateWord body.k next) with state := none} word fuel rfl rfl
    refine ⟨(t + 1) + v, by omega, ?_⟩
    change (if (loopDebit word).2 then
      (loopHost body F anchor findMode).tm.runFrom
        (loopCall body F anchor false start true none word fuel) ((t + 1) + v) = _
      else _)
    rw [MultiTapeTM.runFrom_add, hcap]
    exact hfinish

/-- The audit's single maximum: startup coefficient nine, body coefficient
three, counter coefficient two, and dispatch allowance five. -/
private def loopHost_bound : ℕ := max 1 (max 9 (3 + 2 + 5))

/-- Configuration contracts for the concrete controller in both output modes.
**Continuation frontier: unproved.** The public corollaries below are conditional
on this one machine-construction obligation; this is not a closed batch.

**Proof sketch.** Run the relocated fuel source to its first halt using
`loopHost_fuel_capture`. Phases 0--5 copy and retain its binary fuel, clear
the capture tape, and rewind the two work heads and the input head. Run
startup with `loopHost_body_capture`; phase 6 clears the flag and releases
the initial seam without a debit. Define each candidate seam using the
iterated body word and `loopDebit` word, retaining the fuel work residue.
`loop_orbit_inv` supplies every local body premise. The body simulation and
first-halt lemmas identify the first stop; W1 preserves its full payload.
Phase 7 either emits/replays that payload or starts the width-bounded
borrow. `loopBorrow_correct` is the standalone counter template to be
lifted into phases 8--10. Final zero underflow and phase 11 belong to the
last rejecting segment. If the last candidate accepts, choose any halted
false/empty terminal. Sum the phase constants with the audit's maximum
ledger. The missing proof is precisely the controller-level lifting and
assembly of these phase contracts, including startup and replay bounds. -/
/- Batch L2 closure: the preceding continuation docstring is retained as
historical evidence. Its listed obligations are discharged below by the phase
lemmas and the canonical family; there is no remaining construction admission. -/
private lemma loopHost_contracts (body F : FinTM Bool) (anchor : body.State)
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
      ∃ (cfg : ℕ → Cfg (loopHost body F anchor findMode).k Bool
          (loopHost body F anchor findMode).State x) (startup : ℕ),
        startup ≤ c * (T x.length + 1) ∧
        (loopHost body F anchor findMode).tm.runFrom
          ((loopHost body F anchor findMode).tm.initCfg x) startup = cfg 0 ∧
        (∀ i ≤ R x.length, (cfg i).output = []) ∧
        (cfg (R x.length + 1)).state = none ∧
        (cfg (R x.length + 1)).output = (if findMode then [] else [false]) ∧
        (∀ i ≤ R x.length, ∃ t ≤ c * (T x.length + 1),
          if acceptF x ((stepF x)^[i] (s0 x)) then
            ((loopHost body F anchor findMode).tm.runFrom (cfg i) t).state = none ∧
            ((loopHost body F anchor findMode).tm.runFrom (cfg i) t).output =
              (if findMode then out x ((stepF x)^[i] (s0 x)) else [true])
          else (loopHost body F anchor findMode).tm.runFrom (cfg i) t = cfg (i + 1)) := by
  classical
  refine ⟨loopHost_bound, ?_⟩
  intro x
  obtain ⟨fuel, ftime, hfh, hfo, hft, hprepare⟩ :=
    loopHost_prepare body F anchor findMode R T hF x
  obtain ⟨btime, hbt, hbguard, hbend⟩ := hstart x
  let words (i : ℕ) := (fun w => (loopDebit w).1)^[i] (Nat.bits (R x.length))
  let orbit (i : ℕ) := (stepF x)^[i] (s0 x)
  let candidate (i : ℕ) := loopCall body F anchor false
    (Cfg.ofWords (input := x) anchor (stateWord body.k (orbit i))) true none (words i) fuel
  have hwidth (i : ℕ) : (words i).length ≤ T x.length := by
    dsimp only [words]
    rw [loopDebit_iterate_length]
    exact loop_fuel_width F R T hF x
  have hsuccess (i : ℕ) (hi : i ≤ R x.length) :
      (loopDebit (words i)).2 = true ↔ i < R x.length := by
    rw [loopDebit_success]
    dsimp only [words]
    rw [loopDebit_iterate_value _ _ hi]
    omega
  -- Each specified seam has its own local contract, including unreachable
  -- seams following an earlier accepting candidate.
  have hlocal : ∀ i ≤ R x.length, ∃ t ≤ loopHost_bound * (T x.length + 1),
      if acceptF x (orbit i) then
        ((loopHost body F anchor findMode).tm.runFrom (candidate i) t).state = none ∧
        ((loopHost body F anchor findMode).tm.runFrom (candidate i) t).output =
          (if findMode then out x (orbit i) else [true])
      else if i < R x.length then
        (loopHost body F anchor findMode).tm.runFrom (candidate i) t = candidate (i + 1)
      else
        ((loopHost body F anchor findMode).tm.runFrom (candidate i) t).state = none ∧
        ((loopHost body F anchor findMode).tm.runFrom (candidate i) t).output =
          (if findMode then [] else [false]) := by
    intro i hi
    obtain ⟨t, htpos, ht, hguard, hend⟩ := hround x (orbit i)
      (loop_orbit_inv Inv stepF s0 hInv0 hInvStep x i)
    obtain ⟨v, hv, hsegment⟩ := loopHost_round body F anchor findMode
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
      time i ≤ loopHost_bound * (T x.length + 1) ∧
      if acceptF x (orbit i) then
        ((loopHost body F anchor findMode).tm.runFrom (candidate i) (time i)).state = none ∧
        ((loopHost body F anchor findMode).tm.runFrom (candidate i) (time i)).output =
          (if findMode then out x (orbit i) else [true])
      else if i < R x.length then
        (loopHost body F anchor findMode).tm.runFrom (candidate i) (time i) = candidate (i + 1)
      else
        ((loopHost body F anchor findMode).tm.runFrom (candidate i) (time i)).state = none ∧
        ((loopHost body F anchor findMode).tm.runFrom (candidate i) (time i)).output =
          (if findMode then [] else [false]) := by
    simpa only [time, dif_pos hi] using (hlocal i hi).choose_spec
  have hlast := htime (R x.length) (le_refl _)
  let terminal := if acceptF x (orbit (R x.length)) then
      {candidate (R x.length + 1) with state := none, output := if findMode then [] else [false]}
    else (loopHost body F anchor findMode).tm.runFrom (candidate (R x.length))
      (time (R x.length))
  have hterminal : terminal.state = none ∧ terminal.output = (if findMode then [] else [false]) := by
    dsimp only [terminal]
    split
    · exact ⟨rfl, rfl⟩
    · rename_i ha
      simpa only [ha, Bool.false_eq_true, ↓reduceIte, Nat.lt_irrefl] using hlast.2
  let cfg (i : ℕ) := if i ≤ R x.length then candidate i else terminal
  have hcfg (i : ℕ) (hi : i ≤ R x.length) : cfg i = candidate i := if_pos hi
  refine ⟨cfg, ftime + (btime + 2), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change ftime + (btime + 2) ≤ 10 * (T x.length + 1)
    omega
  · rw [hcfg 0 (Nat.zero_le _), MultiTapeTM.runFrom_add, hprepare,
      loopHost_start body F anchor findMode (s0 x) btime fuel hbguard hbend]
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

/-- **The configuration-level loop combinator** (spec, fill pending;
added per round-2 finding 1 — the final-answer conclusion below cannot
discharge a configuration contract: the round-2 audit exhibits a machine
that answers correctly after a deliberate exponential delay, satisfying
the final-answer form while violating every per-round bound). Same
hypotheses as `exists_loopTM`; the conclusion instead exposes, for every
input, the host's **round-configuration family**: a bounded startup
reaching `cfg 0`, empty output at every round configuration, a per-round
accept-or-advance segment within a uniform constant multiple of
`T |x| + 1` — acceptance halting with `[true]`, advance reaching
`cfg (i + 1)` — and the halted `[false]` exhaustion terminal at index
`R |x| + 1`. This is the generic shape of the frozen Chapter-2
`enumMachine_contracts` (`machine-library-design.md` §9c gives the index
and budget translation). The decision form below is a corollary through
an already-halted-terminal summation lemma; the find form shares the
host construction with the payload surfaced, and is not claimed as a
`Turing.loop_run` corollary (round-3 finding R3-1).

**Proof sketch.** The intended host of `exists_loopTM` already *has* this
family: `cfg i` is the host image of the body's seam at the `i`-th orbit
point together with the counter state after `i` debits (initial entry
free), and `cfg (R |x| + 1)` is the halted configuration after the borrow
underflow and the `[false]` emission. Startup is the fuel phase plus the
body startup; each segment is one captured body round plus counter work
bounded **worst-case** by the counter width: the fuel word has length at
most `T |x|` (`Turing.MultiTapeTM.output_length_le` on the fuel machine)
and never grows, so every debit, rewind, and the final
underflow-plus-`[false]`-emission each cost a constant multiple of
`T |x| + 1` — the per-segment bound needs no amortization (round-3
finding R3-2; the amortized aggregate remains true but is not read off
per segment). -/
theorem exists_loopCfgTM (body F : FinTM Bool) (anchor : body.State)
    (Inv : List Bool → List Bool → Prop)
    (stepF : List Bool → List Bool → List Bool)
    (acceptF : List Bool → List Bool → Bool)
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
              = [true]
        else
          body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t =
              Cfg.ofWords anchor (stateWord body.k (stepF x s))) :
    ∃ (E : FinTM Bool) (c : ℕ), ∀ x : List Bool,
      ∃ (cfg : ℕ → Cfg E.k Bool E.State x) (startup : ℕ),
        startup ≤ c * (T x.length + 1) ∧
        E.tm.runFrom (E.tm.initCfg x) startup = cfg 0 ∧
        (∀ i ≤ R x.length, (cfg i).output = []) ∧
        (cfg (R x.length + 1)).state = none ∧
        (cfg (R x.length + 1)).output = [false] ∧
        (∀ i ≤ R x.length, ∃ t ≤ c * (T x.length + 1),
          if acceptF x ((stepF x)^[i] (s0 x)) then
            (E.tm.runFrom (cfg i) t).state = none ∧
            (E.tm.runFrom (cfg i) t).output = [true]
          else E.tm.runFrom (cfg i) t = cfg (i + 1)) := by
  obtain ⟨c, hc⟩ := loopHost_contracts body F anchor Inv stepF acceptF
    (fun _ _ => [true]) false s0 R T hF hInv0 hInvStep hstart hround
  exact ⟨loopHost body F anchor false, c, by simpa using hc⟩

/-- Summation with an already-halted exhaustion terminal. Unlike `loop_run`,
this lemma requires no empty output at that terminal and charges no final
extra segment.
**Proof sketch.** Induct on the remaining candidates, as in `enumLoop_run`.
An accepting round ends the run; a rejecting round composes with the
shifted induction hypothesis. Zero candidates use the halted terminal at
time zero, with its already-written false verdict. -/
private lemma loop_halted_run {k : ℕ} {S : Type*} {x : List Bool}
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

/-- **The decision loop combinator** (spec, fill pending; repaired per
round-1 findings 1, 2, and 4 — see the module docstring). Hypotheses:

* `hF`: the fuel machine writes `Nat.bits (R |x|)` within `T |x|`.
* `hInv0`, `hInvStep`: the admissibility invariant holds at the initial
  state word and is preserved by the step, so every orbit point the
  conclusion mentions is admissible.
* `hstart`: the body reaches the initial seam within `T |x|` without
  visiting the anchor state earlier.
* `hround`: on every **admissible** state word, the body takes **positive**
  time `t ≤ T |x|`, does not re-enter the anchor strictly before `t`, and
  either halts with the verdict `[true]` (acceptance) or sits at the seam
  carrying the stepped word (advance).

Conclusion: one finite machine answers, within a constant multiple of
`(T |x| + 1) · (R |x| + 2)`, whether some orbit point
`(stepF x)^[i] (s0 x)` with `i ≤ R |x|` is accepted.

At fill time this is a corollary of `exists_loopCfgTM` through an
already-halted-terminal summation lemma — the frozen `Turing.loop_run`
additionally requires an empty-output terminal, which the exported
`[false]` terminal is not (round-3 finding R3-1) — with startup absorbed
by `ComputesInTime.mono`.

**Proof sketch.** The combinator machine runs the fuel machine
relocated-and-captured to lay `Nat.bits (R |x|)` on a counter tape,
rewinds, and embeds the body via the W1 capture discipline of
`TCSlib.Complexity.TuringMachine.Build.Wrappers` (the body's verdict is
captured, never physically emitted until the end). The initial anchor
entry is free; each subsequent entry debits the binary counter in place —
amortized borrow, exhaustion exactly at borrow-overflow, so rounds
`0, …, R |x|` run before the exhaustion rejection `[false]`. Acceptance
surfaces as the captured halt and emits `[true]`. `Turing.loop_run` sums
the seam family; the invariant hypotheses confine every round to
admissible words, and positive round duration makes each anchor entry a
genuine round boundary. Phase overheads are absorbed into `c`. -/
theorem exists_loopTM (body F : FinTM Bool) (anchor : body.State)
    (Inv : List Bool → List Bool → Prop)
    (stepF : List Bool → List Bool → List Bool)
    (acceptF : List Bool → List Bool → Bool)
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
              = [true]
        else
          body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t =
              Cfg.ofWords anchor (stateWord body.k (stepF x s))) :
    ∃ (E : FinTM Bool) (c : ℕ),
      E.ComputesFunInTime
        (fun x => [(List.range (R x.length + 1)).any
          fun i => acceptF x ((stepF x)^[i] (s0 x))])
        (fun n => c * (T n + 1) * (R n + 2)) := by
  obtain ⟨E, c, hc⟩ := exists_loopCfgTM body F anchor Inv stepF acceptF s0 R T
    hF hInv0 hInvStep hstart hround
  refine ⟨E, c, fun x => ?_⟩
  obtain ⟨cfg, startup, hs, hinit, _, hend, hout, hsegments⟩ := hc x
  obtain ⟨t, ht, hhalt, houtput⟩ := loop_halted_run E.tm cfg
    (fun i => acceptF x ((stepF x)^[i] (s0 x))) (c * (T x.length + 1))
    (R x.length + 1) ⟨hend, hout⟩ (fun j hj => hsegments j (by omega))
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
    _ = c * (T x.length + 1) * (R x.length + 2) := by
      rw [Nat.mul_comm (R x.length + 1)]
      simp only [Nat.mul_add, Nat.mul_one, Nat.mul_two]
      omega

/-- The first accepting segment returns its own payload; an already-halted
empty-output terminal supplies exhaustion.
**Proof sketch.** Induct on the ordered candidate range. Acceptance at its
head terminates immediately. Otherwise compose the advance with the shifted
induction hypothesis; `find?_map` shifts the selected index back by one.
Thus the payload is tied to the least accepting candidate, including when
that payload is empty. -/
private lemma loop_find_run {k : ℕ} {S : Type*} {x : List Bool}
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

/-- **The result-bearing loop combinator** (spec, fill pending; added per
round-1 finding 3 — the decision form exposes only a Boolean, which cannot
express the split search's or the reduction emitters' outputs). Identical
skeleton to `exists_loopTM`, except the accepting round halts with the
declared payload `out x s`, and the machine outputs the **first** accepting
orbit point's payload — `[]` on fuel exhaustion, the library's threaded
rejection value. `List.range.find?` returns the least accepting index, which
is exactly the round at which the iterated body first halts.

**Proof sketch.** As `exists_loopTM`, with one change at the surface: on
the captured halt the host replays the entire capture tape (the payload)
as its output instead of the fixed verdict — the W1 core captures the
full output word precisely so that this variant costs nothing extra. A
payload may be `[]`; the conclusion's function is well-defined regardless,
and consumers that need to distinguish success from exhaustion use
nonempty payloads (the split search's `pairEncode` outputs are always
nonempty). -/
theorem exists_loopFindTM (body F : FinTM Bool) (anchor : body.State)
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
        (fun n => c * (T n + 1) * (R n + 2)) := by
  obtain ⟨c, hc⟩ := loopHost_contracts body F anchor Inv stepF acceptF out true s0 R T
    hF hInv0 hInvStep hstart hround
  let E := loopHost body F anchor true
  refine ⟨E, c, fun x => ?_⟩
  obtain ⟨cfg, startup, hs, hinit, _, hend, hout, hsegments⟩ := hc x
  obtain ⟨t, ht, hhalt, houtput⟩ := loop_find_run E.tm cfg
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

end Turing.FinTM


## ===== TCSlib/Complexity/TuringMachine/Build/Primitives.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.List.Induction
import Mathlib.Data.Nat.Bits
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Ring
import TCSlib.Complexity.ClassP.TimeConstructible
import TCSlib.Complexity.TuringMachine.Build.Convention
import TCSlib.Complexity.TuringMachine.Build.Loop
import TCSlib.Complexity.TuringMachine.Build.Wrappers
import TCSlib.Complexity.TuringMachine.Composition
import TCSlib.Complexity.TuringMachine.Encoding

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: the primitive catalog

The instruction set of the machine-construction library
(`machine-library-design.md` §4, P1–P12): the timed string functions every
Chapter-2 fill batch privately rebuilt, stated once as machine contracts.
`Turing.FinTM.computesFunInTime_id` and
`Turing.FinTM.computesFunInTime_const` (in
`TCSlib.Complexity.TuringMachine.Composition`) are catalog entries P1–P2
and already proved; this module states the rest.

**Status: spec phase.** Every theorem below is sorried; roughly half are
harvests — their fills adapt already-proved private constructions from the
Chapter-2 epoch-2 batches (named per entry) — and the rest are new small
machines. Following the house idiom of
`TCSlib.Complexity.TuringMachine.Composition`, the contracts are
existentially packaged; each fill implements a named private machine with
its run invariants and closes the existential. Multi-argument interfaces
go through `Turing.pairEncode`, whose self-delimiting grammar lets a
pipeline stage **thread the original input through its output** — the
`pairLenCheck` and `stripLast` contracts below are deliberately stated in
that threaded form, which is exactly how the Chapter-2 verifier
constructions consume them. New Chapter-1 surface, flagged for the shared
infrastructure audit round.

**Catalog refinements at spec time** (recorded against the frozen design
§4): P6 is realized as the fixed-first-component encoder plus the threaded
extractors/validity test; P7 (replicate) is subsumed by the unary clause of
P5, whose instances are what the emission customers actually consume; P8
is realized in threaded form (`pairLenCheck`); P12 (`clearTM`) has no
standalone string-function contract — clearing is intra-machine and lives
in the loop fill's toolkit. **Round-2 additions** (per round-1 finding 3:
the extractors discard the other component by design, and sequential
composition alone never yields simultaneous access to two results): P13
`pairConcat` (the D-WRAP shape), P14 `pairDup` (the entry stage of
data-retaining pipelines), and the threaded-map combinator `pairMapSnd`;
P10's narrowing is recorded, and result-bearing search is now
`Turing.FinTM.exists_loopFindTM` (`machine-library-design.md` §9b).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2–§1.4: all entries are the
  folklore tape subroutines of the textbook's simulation arguments.)

**Implementation note (batch P, partial).** The first eleven targets in the
batch brief's fill order are now proved. The four continuation targets are
`pairLenCheck`, `stripLast`, `pairMapSnd`, and `splitSolve`; their audited
statements and admissions remain unchanged. The original spec-phase prose
above and on the contracts is retained as the audit record. The length
counter is obtained from the public `Complexity.timeConstructible_id`, whose
proved machine implements precisely the sketched amortized counter. The three
extractors share one private buffered parser, so suffix-only extraction also
buffers and replays silently before copying the suffix; its linear envelope
is unchanged. The fixed-width incrementer adapts the enumerator's carry
semantics to two native-input scans, validating before physical emission.


**Implementation note (batch P2, partial).** The threaded length checker and
marker stripper are now proved; the threaded map and split search remain the
unchanged continuation frontier. The length checker composes the existing
buffered first extractor with the unary generator, captures the result with
`capture_run`, then reparses and counts down on the native payload. Malformed
inputs emit only `[false]`. The marker stripper first guards on a valid
extracted suffix containing a true bit; the successful branch buffers the
whole original encoding, erases its final marker/false-run, and replays the
retained encoding. The guard is complete before any physical output. Both
routes reuse the in-file parser/scan invariant patterns and proved public
wrappers. `catalogPayload_computes` supplies a proved relocated-simulation
component for the next target, with its time evaluated at the actual suffix
length; the retained-prefix/captured-output controller remains to be built.


**Implementation note (batch P3, partial).** The threaded map is now proved.
`pairMapTM` captures `catalogPayload_computes` on the original physical input,
rewinds the capture and input, validates without emission, then replays the
original encoded prefix and captured result. `pairMap_computes` bounds this
controller by `4 * (T n + n + 3)` and the public theorem uses coefficient 40.
All original contract docstrings are retained as the audit record.

The split-search theorem remains the unchanged admitted frontier. Its new
private, admission-free components are the unary orbit/search bridges and
`splitSolve_of_body`, which closes the public result only when supplied the
actual startup and round contracts; a candidate-preserving unary-bank
preparer; a counted source-simulation correspondence; the generator's exact
loop endpoint; and a scratch-restoration controller with a positive first
return and no earlier visit to its return state. These separate component
proofs do not yet constitute a combined body or a proof of its `hround`.
-/

/-! Batch P4 closure note: the split-search body is now constructed and proved.
`splitBodyTM` separates preparation, counted source evaluation, checked rewind,
rejection restoration, and native-bit emission into disjoint finite phases.
`splitBody_round` composes their exact seams and proves positive duration and
strict-interior anchor exclusion, including the arbitrary-bit past-end stall.
`splitEmit_run` supplies the native-slice payload; `splitBody_envelope` accounts
for every phase within the common polynomial bound. Both exponent cases
instantiate this body through the proved `splitSolve_of_body` loop closure.
All fifteen primitive contracts are now proved without admissions. Earlier
spec/checkpoint status notes above are retained as historical documentation. -/

namespace Turing.FinTM

/-! Implementation note (batch P): the private prefix construction below is
adapted in-file from `ClassNP/Reductions.lean`; no private declaration from
that module is used. Completed contracts retain their audited spec docstrings. -/

/-- Emit the fixed prefix, then copy the input verbatim. No work tape is needed;
the last finite state is the copy state. -/
private def catalogPrefixTM (w : List Bool) : FinTM Bool where
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
private def catalogPrefixCfg (w x : List Bool) (q : Option (Fin (w.length + 1)))
    (p : Fin (x.length + 2)) (out : List Bool) : Cfg 0 Bool (Fin (w.length + 1)) x :=
  ⟨q, p, fun i => i.elim0, fun i => i.elim0, out⟩

/-- After `i` prefix steps exactly the first `i` fixed bits have been emitted,
and the input head has not moved. -/
private lemma catalogPrefixTM_emit (w x : List Bool) : ∀ i (hi : i ≤ w.length),
    (catalogPrefixTM w).tm.runFrom ((catalogPrefixTM w).tm.initCfg x) i =
      catalogPrefixCfg w x (some ⟨i, by omega⟩) 1 (w.take i) := by
  intro i
  induction i with
  | zero =>
    intro hi
    apply Cfg.ext_zero_tapes <;> simp [catalogPrefixCfg, catalogPrefixTM]
  | succ i ih =>
    intro hi
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hlt : i < w.length := by omega
    simp only [MultiTapeTM.step, catalogPrefixCfg, catalogPrefixTM, dif_pos hlt, Action.apply]
    apply Cfg.ext_zero_tapes
    · rfl
    · simp
    · rw [List.take_succ, List.getElem?_eq_getElem hlt]

/-- The copy phase emits one input bit per step and preserves the fixed prefix. -/
private lemma catalogPrefixTM_copy (w x : List Bool) : ∀ i (hi : i ≤ x.length),
    (catalogPrefixTM w).tm.runFrom
      (catalogPrefixCfg w x (some ⟨w.length, by omega⟩) 1 w) i =
      catalogPrefixCfg w x (some ⟨w.length, by omega⟩) ⟨i + 1, by omega⟩
        (w ++ x.take i) := by
  intro i
  induction i with
  | zero => intro hi; simp [catalogPrefixCfg]
  | succ i ih =>
    intro hi
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hsym : (catalogPrefixCfg w x (some ⟨w.length, by omega⟩)
        ⟨i + 1, by omega⟩ (w ++ x.take i)).inputSymbol = some (x[i]'(by omega)) :=
      inputSymbolInner i (by simp only [catalogPrefixCfg]; omega) (by omega)
    change ((catalogPrefixTM w).tm.tr ⟨w.length, by omega⟩
      (catalogPrefixCfg w x (some ⟨w.length, by omega⟩) ⟨i + 1, by omega⟩
        (w ++ x.take i)).inputSymbol _).apply _ = _
    rw [hsym]
    simp only [catalogPrefixTM, Nat.lt_irrefl, ↓reduceDIte, Action.apply, catalogPrefixCfg]
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
private lemma catalogPrefixTM_computes (w : List Bool) :
    (catalogPrefixTM w).ComputesFunInTime (fun x => w ++ x) (fun n => w.length + n + 1) := by
  intro x
  apply (FinTM.computesInTime_iff _ _ _ _).mpr
  dsimp only
  rw [show w.length + x.length + 1 = w.length + (x.length + 1) by omega,
    MultiTapeTM.runFrom_add, catalogPrefixTM_emit w x w.length (Nat.le_refl _)]
  simp only [List.take_length]
  rw [MultiTapeTM.runFrom_succ_eq_step', catalogPrefixTM_copy w x x.length (Nat.le_refl _)]
  simp [catalogPrefixTM, catalogPrefixCfg, MultiTapeTM.step, Cfg.inputSymbol, Fin.ext_iff, Action.apply]


/-- A zero-work-tape configuration indexed by the number of input bits passed. -/
private def scanCfg {S : Type} (x : List Bool) (q : Option S)
    (i : ℕ) (hi : i ≤ x.length) (out : List Bool) : Cfg 0 Bool S x :=
  ⟨q, ⟨i + 1, by omega⟩, fun j => j.elim0, fun j => j.elim0, out⟩

/-- Reading at the indexed input position returns the optional list entry. -/
private lemma scanCfg_read {S : Type} (x : List Bool) (q : Option S)
    (i : ℕ) (hi : i ≤ x.length) (out : List Bool) :
    (scanCfg x q i hi out).inputSymbol = x[i]? := by
  by_cases h : i < x.length
  · rw [List.getElem?_eq_getElem h]
    exact inputSymbolInner i (by simp [scanCfg]; omega) h
  · have he : i = x.length := by omega
    subst i
    simp [scanCfg, Cfg.inputSymbol, Fin.ext_iff]

/-- A copy state emits the next `j` input bits after an arbitrary output prefix.
**Proof sketch.** Induct on the number of copied cells; each transition appends
the scanned bit and moves right. The indexed configuration keeps the boundary
case separate from the actual bit-reading steps. -/
private lemma scanCopy_run {S : Type} (tm : MultiTapeTM 0 Bool S) (q : S)
    (htr : ∀ inp work, tm.tr q inp work = match inp with
      | some b => ⟨.pos, fun j => j.elim0, some b, some q⟩
      | none => ⟨0, fun j => j.elim0, none, none⟩)
    (x out : List Bool) : ∀ j (hj : j ≤ x.length),
    tm.runFrom (scanCfg x (some q) 0 (by omega) out) j =
      scanCfg x (some q) j hj (out ++ x.take j) := by
  intro j
  induction j with
  | zero => intro hj; simp [scanCfg]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    unfold MultiTapeTM.step
    change (tm.tr q (scanCfg x (some q) j (by omega) (out ++ x.take j)).inputSymbol
      _).apply _ = _
    rw [htr, scanCfg_read, List.getElem?_eq_getElem (by omega)]
    apply Cfg.ext_zero_tapes
    · rfl
    · exact moveInputPos_pos_of_ne_right _ (by simp [scanCfg]; omega)
    · simp only [Action.apply, scanCfg, Option.toList_some, List.take_succ,
        List.getElem?_eq_getElem (by omega : j < x.length), List.append_assoc]

/-- After copying the entire input, the right-blank transition halts silently. -/
private lemma scanCopy_finish {S : Type} (tm : MultiTapeTM 0 Bool S) (q : S)
    (htr : ∀ inp work, tm.tr q inp work = match inp with
      | some b => ⟨.pos, fun j => j.elim0, some b, some q⟩
      | none => ⟨0, fun j => j.elim0, none, none⟩)
    (x out : List Bool) :
    tm.runFrom (scanCfg x (some q) 0 (by omega) out) (x.length + 1) =
      scanCfg x none x.length (by omega) (out ++ x) := by
  rw [MultiTapeTM.runFrom_succ_eq_step', scanCopy_run tm q htr x out _ (by omega)]
  unfold MultiTapeTM.step
  change (tm.tr q (scanCfg x (some q) x.length (by omega)
    (out ++ x.take x.length)).inputSymbol _).apply _ = _
  rw [htr, scanCfg_read]
  apply Cfg.ext_zero_tapes <;> simp [Action.apply, scanCfg]

/-- Duplicate the input into the self-delimiting pair: double on the first
pass, rewind silently after emitting the separator's first bit, then emit its
second bit and copy. Every input is legal, so no validation buffer is needed. -/
private def pairDupTM : FinTM Bool where
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
private lemma pairDup_double (x : List Bool) : ∀ j (hj : j ≤ x.length),
    pairDupTM.tm.runFrom (pairDupTM.tm.initCfg x) (2 * j) =
      scanCfg x (some (0 : Fin 5)) j hj ((x.take j).flatMap fun b => [b, b]) := by
  intro j
  induction j with
  | zero => intro hj; apply Cfg.ext_zero_tapes <;> simp [scanCfg, pairDupTM]
  | succ j ih =>
    intro hj
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by omega,
      MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hread := scanCfg_read x (some (0 : Fin 5)) j (by omega)
      ((x.take j).flatMap fun b => [b, b])
    rw [List.getElem?_eq_getElem (by omega)] at hread
    have hfirst : pairDupTM.tm.step
        (scanCfg x (some (0 : Fin 5)) j (by omega) ((x.take j).flatMap fun b => [b, b])) =
        scanCfg x (some (1 : Fin 5)) j (by omega)
          (((x.take j).flatMap fun b => [b, b]) ++ [x[j]'(by omega)]) := by
      unfold MultiTapeTM.step
      change (pairDupTM.tm.tr (0 : Fin 5) _ _).apply _ = _
      rw [hread]
      apply Cfg.ext_zero_tapes <;> simp [pairDupTM, Action.apply, scanCfg]
    rw [hfirst]
    unfold MultiTapeTM.step
    change (pairDupTM.tm.tr (1 : Fin 5) _ _).apply _ = _
    rw [scanCfg_read, List.getElem?_eq_getElem (by omega)]
    apply Cfg.ext_zero_tapes
    · rfl
    · exact moveInputPos_pos_of_ne_right _ (by simp [scanCfg]; omega)
    · change (((x.take j).flatMap fun b => [b, b]) ++ [x[j]'(by omega)]) ++
        [x[j]'(by omega)] = (x.take (j + 1)).flatMap fun b => [b, b]
      simp only [List.take_succ, List.getElem?_eq_getElem (by omega : j < x.length),
        Option.toList_some, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.append_assoc, List.cons_append, List.nil_append]

/-- The two passes and rewind take exactly `4|x|+4` transitions.
**Proof sketch.** Doubling costs `2|x|`, emitting the first separator bit
costs one, rewind and dispatch cost `|x|+1`, the second separator bit costs
one, and copying with its final blank test costs `|x|+1`. -/
private lemma pairDup_computes (x : List Bool) :
    pairDupTM.ComputesInTime x (pairEncode x x) (4 * (x.length + 1)) := by
  let pre := x.flatMap fun b => [b, b]
  let c : Cfg 0 Bool (Fin 5) x :=
    ⟨some 2, ⟨x.length, by omega⟩, fun j => j.elim0, fun j => j.elim0, pre ++ [false]⟩
  have hsep : pairDupTM.tm.step (scanCfg x (some (0 : Fin 5)) x.length (by omega) pre) = c := by
    unfold MultiTapeTM.step
    change (pairDupTM.tm.tr (0 : Fin 5) _ _).apply _ = _
    rw [scanCfg_read]
    apply Cfg.ext_zero_tapes
    · simp [pairDupTM, c]
    · simpa [pairDupTM, Action.apply, scanCfg, c] using
        moveInputPos_neg_of_ne_left (⟨x.length + 1, by omega⟩ : Fin (x.length + 2))
          (by simp [Fin.ext_iff])
    · simp [pairDupTM, Action.apply, scanCfg, c]
  have hr := rewind_scan pairDupTM.tm (2 : Fin 5) (some (3 : Fin 5)) (fun _ _ => rfl) c rfl (by simp [c])
  have hemit : pairDupTM.tm.step {c with state := some (3 : Fin 5), inputPos := 1} =
      scanCfg x (some (4 : Fin 5)) 0 (by omega) (pre ++ [false, true]) := by
    apply Cfg.ext_zero_tapes <;>
      simp [MultiTapeTM.step, pairDupTM, c, scanCfg, Action.apply, List.append_assoc]
  have h1 : pairDupTM.tm.runFrom (pairDupTM.tm.initCfg x) (2 * x.length + 1) = c := by
    rw [MultiTapeTM.runFrom_succ_eq_step', pairDup_double x x.length (by omega)]
    simpa only [List.take_length] using hsep
  have h2 : pairDupTM.tm.runFrom (pairDupTM.tm.initCfg x)
      (2 * x.length + 1 + (x.length + 1)) =
      {c with state := some (3 : Fin 5), inputPos := 1} := by
    rw [MultiTapeTM.runFrom_add, h1]
    exact hr
  have h3 : pairDupTM.tm.runFrom (pairDupTM.tm.initCfg x)
      (2 * x.length + 1 + (x.length + 1) + 1) =
      scanCfg x (some (4 : Fin 5)) 0 (by omega) (pre ++ [false, true]) := by
    rw [MultiTapeTM.runFrom_succ_eq_step', h2, hemit]
  apply (computesInTime_iff _ _ _ _).mpr
  rw [show 4 * (x.length + 1) = (2 * x.length + 1 + (x.length + 1) + 1) +
    (x.length + 1) by omega, MultiTapeTM.runFrom_add, h3,
    scanCopy_finish pairDupTM.tm (4 : Fin 5) (fun _ _ => rfl)]
  exact ⟨rfl, rfl⟩

/-- Copy a suffix from an already-positioned input head, preserving prior output.
**Proof sketch.** Induct on the suffix. A nonempty suffix emits its first bit
and shifts the prefix/suffix boundary by one. The empty suffix reads the right
blank and halts without another emission. -/
private lemma scanCopy_suffix {S : Type} (tm : MultiTapeTM 0 Bool S) (q : S)
    (htr : ∀ inp work, tm.tr q inp work = match inp with
      | some b => ⟨.pos, fun j => j.elim0, some b, some q⟩
      | none => ⟨0, fun j => j.elim0, none, none⟩)
    (x rest : List Bool) : ∀ pre out (hx : x = pre ++ rest),
    tm.runFrom (scanCfg x (some q) pre.length (by simp [hx]) out) (rest.length + 1) =
      scanCfg x none x.length (by omega) (out ++ rest) := by
  induction rest with
  | nil =>
    intro pre out hx
    subst x
    simp only [List.length_nil, MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change (tm.tr q _ _).apply _ = _
    rw [htr, scanCfg_read]
    apply Cfg.ext_zero_tapes <;> simp [Action.apply, scanCfg]
  | cons b rest ih =>
    intro pre out hx
    have hlen : pre.length < x.length := by simp [hx]
    have hread : x[pre.length]? = some b := by simp [hx]
    have hs : tm.step (scanCfg x (some q) pre.length (by omega) out) =
        scanCfg x (some q) (pre ++ [b]).length (by simp [hx]) (out ++ [b]) := by
      unfold MultiTapeTM.step
      change (tm.tr q _ _).apply _ = _
      rw [htr, scanCfg_read, hread]
      apply Cfg.ext_zero_tapes
      · rfl
      · simpa [scanCfg] using moveInputPos_pos_of_ne_right
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
private lemma scanTrues_run {S : Type} (tm : MultiTapeTM 0 Bool S) (q : S)
    (emit : Bool)
    (htr : ∀ work, tm.tr q (some true) work =
      ⟨.pos, fun j => j.elim0, if emit then some false else none, some q⟩)
    (x : List Bool) : ∀ j (hj : j ≤ x.length),
    x.take j = List.replicate j true →
    tm.runFrom (scanCfg x (some q) 0 (by omega) []) j =
      scanCfg x (some q) j hj (if emit then List.replicate j false else []) := by
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
    rw [scanCfg_read, hb, htr]
    apply Cfg.ext_zero_tapes
    · rfl
    · exact moveInputPos_pos_of_ne_right _ (by simp [scanCfg]; omega)
    · cases emit <;> simp [Action.apply, scanCfg, List.replicate_succ']

/-- Either every input bit is true (overflow), or its first false splits off
the carry prefix and determines the exact incremented word. -/
private lemma incFixed_cases (x : List Bool) :
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
private def incFixedTM : FinTM Bool where
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
private lemma incFixed_computes (x : List Bool) :
    incFixedTM.ComputesInTime x ((incFixed x).getD []) (3 * (x.length + 1)) := by
  rcases incFixed_cases x with ⟨hx, hinc⟩ | ⟨j, rest, hx, hinc⟩
  · have hr := scanTrues_run incFixedTM.tm (0 : Fin 4) false (fun _ => rfl)
      x x.length (by omega) (by simpa using hx)
    have hh : incFixedTM.ComputesInTime x [] (x.length + 1) := by
      apply (computesInTime_iff _ _ _ _).mpr
      rw [MultiTapeTM.runFrom_succ_eq_step', show incFixedTM.tm.initCfg x =
        scanCfg x (some (0 : Fin 4)) 0 (by omega) [] from
          by apply Cfg.ext_zero_tapes <;> simp [incFixedTM, scanCfg], hr]
      unfold MultiTapeTM.step
      change ((incFixedTM.tm.tr (0 : Fin 4) _ _).apply _).state = none ∧ _
      rw [scanCfg_read]
      simp [incFixedTM, controlAction, Action.apply, scanCfg]
    simpa only [hinc, Option.getD_none] using hh.mono (by omega)
  · have hj : j < x.length := by simp [hx]
    have hpre : x.take j = List.replicate j true := by simp [hx]
    have hread : x[j]? = some false := by simp [hx]
    let c : Cfg 0 Bool (Fin 4) x :=
      ⟨some 1, ⟨j, by omega⟩, fun i => i.elim0, fun i => i.elim0, []⟩
    have hdet : incFixedTM.tm.runFrom (incFixedTM.tm.initCfg x) (j + 1) = c := by
      rw [MultiTapeTM.runFrom_succ_eq_step', show incFixedTM.tm.initCfg x =
        scanCfg x (some (0 : Fin 4)) 0 (by omega) [] from
          by apply Cfg.ext_zero_tapes <;> simp [incFixedTM, scanCfg],
        scanTrues_run incFixedTM.tm (0 : Fin 4) false (fun _ => rfl) x j (by omega) hpre]
      unfold MultiTapeTM.step
      change (incFixedTM.tm.tr (0 : Fin 4) _ _).apply _ = _
      rw [scanCfg_read, hread]
      apply Cfg.ext_zero_tapes
      · rfl
      · simpa [incFixedTM, controlAction, Action.apply, scanCfg, c] using
          moveInputPos_neg_of_ne_left (⟨j + 1, by omega⟩ : Fin (x.length + 2))
            (by simp [Fin.ext_iff])
      · rfl
    have hrew : incFixedTM.tm.runFrom (incFixedTM.tm.initCfg x) (j + 1 + (j + 1)) =
        scanCfg x (some (2 : Fin 4)) 0 (by omega) [] := by
      rw [MultiTapeTM.runFrom_add, hdet]
      exact rewind_scan incFixedTM.tm (1 : Fin 4) (some (2 : Fin 4))
        (fun _ _ => rfl) c rfl (by simp [c]; omega)
    have hemit : incFixedTM.tm.runFrom (scanCfg x (some (2 : Fin 4)) 0 (by omega) [])
        (j + 1) = scanCfg x (some (3 : Fin 4)) (j + 1) (by omega)
          (List.replicate j false ++ [true]) := by
      rw [MultiTapeTM.runFrom_succ_eq_step',
        scanTrues_run incFixedTM.tm (2 : Fin 4) true (fun _ => rfl) x j (by omega) hpre]
      unfold MultiTapeTM.step
      change (incFixedTM.tm.tr (2 : Fin 4) _ _).apply _ = _
      rw [scanCfg_read, hread]
      apply Cfg.ext_zero_tapes
      · rfl
      · exact moveInputPos_pos_of_ne_right _ (by simp [scanCfg]; omega)
      · rfl
    have hcopy := scanCopy_suffix incFixedTM.tm (3 : Fin 4) (fun _ _ => rfl)
      x rest (List.replicate j true ++ [false]) (List.replicate j false ++ [true])
      (by simpa [List.append_assoc] using hx)
    have hh : incFixedTM.ComputesInTime x (List.replicate j false ++ true :: rest)
        ((j + 1 + (j + 1)) + ((j + 1) + (rest.length + 1))) := by
      apply (computesInTime_iff _ _ _ _).mpr
      rw [MultiTapeTM.runFrom_add, hrew, MultiTapeTM.runFrom_add, hemit]
      simp only [List.length_append, List.length_replicate, List.length_singleton] at hcopy
      rw [hcopy]
      exact ⟨rfl, by simp [scanCfg, List.append_assoc]⟩
    have hlen : x.length = j + 1 + rest.length := by simp [hx]; omega
    simpa only [hinc, Option.getD_some] using hh.mono (by omega)

/-- A right-moving zero-tape transition advances the indexed configuration
and appends exactly its optional emission. -/
private lemma scanStep_right {S : Type} (tm : MultiTapeTM 0 Bool S)
    (x : List Bool) (q : S) (q' : Option S) (i : ℕ) (hi : i < x.length)
    (out : List Bool) (emit : Option Bool)
    (htr : ∀ work, tm.tr q x[i]? work = ⟨.pos, fun j => j.elim0, emit, q'⟩) :
    tm.step (scanCfg x (some q) i (by omega) out) =
      scanCfg x q' (i + 1) (by omega) (out ++ emit.toList) := by
  unfold MultiTapeTM.step
  change (tm.tr q _ _).apply _ = _
  rw [scanCfg_read, htr]
  apply Cfg.ext_zero_tapes
  · rfl
  · exact moveInputPos_pos_of_ne_right _ (by simp [scanCfg]; omega)
  · rfl

/-- Scan aligned pairs of bits, retaining just the first bit of the current
block. Only a terminal verdict transition emits output. -/
private def pairValidTM : FinTM Bool where
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
private lemma pairValid_block (x pre rest : List Bool) (b c : Bool)
    (hx : x = pre ++ b :: c :: rest) :
    pairValidTM.tm.runFrom (scanCfg x (some none) pre.length (by simp [hx]) []) 2 =
      if b = c then scanCfg x (some none) (pre.length + 2) (by simp [hx]) []
      else scanCfg x none (pre.length + 2) (by simp [hx]) [!b && c] := by
  have h1 := scanStep_right pairValidTM.tm x none (some (some b)) pre.length
    (by simp [hx]) [] none (by intro work; simp [hx, pairValidTM])
  have h2 := scanStep_right pairValidTM.tm x (some b)
    (if b = c then some none else none) (pre.length + 1) (by simp [hx])
    [] (if b = c then none else some (!b && c)) (by
      intro work
      have hr : x[pre.length + 1]? = some c := by simp [hx]
      rw [hr]
      by_cases h : b = c <;> simp [pairValidTM, h])
  change pairValidTM.tm.step (pairValidTM.tm.step _) = _
  rw [h1]
  simp only [Option.toList_none, List.append_nil]
  rw [h2]
  by_cases h : b = c <;> simp [h]

/-- The validity scanner halts within one more than the unprocessed length.
**Proof sketch.** Induct in aligned two-bit blocks. The empty and singleton
cases fail on a boundary blank. Equal-bit blocks invoke the induction
hypothesis silently; `01` succeeds and `10` fails immediately, independently
of the suffix. Thus no verdict is emitted before validity is decided. -/
private lemma pairValid_run (x rest : List Bool) : ∀ pre (hx : x = pre ++ rest),
    ∃ t ≤ rest.length + 1,
      (pairValidTM.tm.runFrom
        (scanCfg x (some none) pre.length (by simp [hx]) []) t).state = none ∧
      (pairValidTM.tm.runFrom
        (scanCfg x (some none) pre.length (by simp [hx]) []) t).output =
          [(pairDecode rest).isSome] := by
  induction rest using List.twoStepInduction with
  | nil =>
    intro pre hx
    refine ⟨1, by simp, ?_⟩
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change ((pairValidTM.tm.tr none _ _).apply _).state = none ∧ _
    rw [scanCfg_read]
    simp [hx, pairValidTM, Action.apply, scanCfg, pairDecode]
  | singleton b =>
    intro pre hx
    have h1 := scanStep_right pairValidTM.tm x none (some (some b)) pre.length
      (by simp [hx]) [] none (by intro work; simp [hx, pairValidTM])
    refine ⟨2, by simp, ?_⟩
    change (pairValidTM.tm.step (pairValidTM.tm.step _)).state = none ∧
      (pairValidTM.tm.step (pairValidTM.tm.step _)).output = _
    rw [h1]
    unfold MultiTapeTM.step
    change ((pairValidTM.tm.tr (some b) _ _).apply _).state = none ∧ _
    rw [scanCfg_read]
    cases b <;> simp [hx, pairValidTM, Action.apply, scanCfg, pairDecode]
  | cons_cons b c rest ih _ =>
    intro pre hx
    by_cases h : b = c
    · subst c
      obtain ⟨t, ht, hs, ho⟩ := ih (pre ++ [b, b]) (by simpa [List.append_assoc] using hx)
      refine ⟨2 + t, by simp only [List.length_cons] at *; omega, ?_⟩
      rw [MultiTapeTM.runFrom_add, pairValid_block x pre rest b b hx, if_pos rfl]
      simp only [List.length_append, List.length_cons, List.length_nil] at hs ho
      refine ⟨hs, ?_⟩
      cases b <;> simpa [pairDecode] using ho
    · refine ⟨2, by simp, ?_⟩
      rw [pairValid_block x pre rest b c hx, if_neg h]
      cases b <;> cases c <;> simp_all [scanCfg, pairDecode]

/-- The validity test starts with an empty aligned prefix and uses the
linear envelope `|x|+1`. -/
private lemma pairValid_computes (x : List Bool) :
    pairValidTM.ComputesInTime x [(pairDecode x).isSome] (x.length + 1) := by
  obtain ⟨t, ht, hs, ho⟩ := pairValid_run x x [] rfl
  have hinit : pairValidTM.tm.initCfg x = scanCfg x (some none) 0 (by omega) [] := by
    apply Cfg.ext_zero_tapes <;> simp [pairValidTM, scanCfg]
  have h : pairValidTM.ComputesInTime x [(pairDecode x).isSome] t := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [hinit]
    exact ⟨hs, ho⟩
  exact h.mono ht

/-- A shared extractor buffers the decoded prefix, validates the separator,
rewinds and replays the buffer, then optionally copies the suffix. The two
flags select the first component, the second, or their concatenation. -/
private def pairExtractTM (first second : Bool) : FinTM Bool where
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
private def extractCfg (x : List Bool) (q : Option (Option Bool ⊕ Fin 3))
    (i : ℕ) (hi : i ≤ x.length) (a : List Bool) (z : ℤ) (out : List Bool) :
    Cfg 1 Bool (Option Bool ⊕ Fin 3) x :=
  ⟨q, ⟨i + 1, by omega⟩, fun _ => bufferTape a, fun _ => z, out⟩

/-- The extractor reads the indexed input entry independently of its buffer. -/
private lemma extractCfg_read (x : List Bool) (q : Option (Option Bool ⊕ Fin 3))
    (i : ℕ) (hi : i ≤ x.length) (a : List Bool) (z : ℤ) (out : List Bool) :
    (extractCfg x q i hi a z out).inputSymbol = x[i]? :=
  scanCfg_read x q i hi out

/-- Reading the first half of an aligned block preserves the buffer silently. -/
private lemma extract_first (first second : Bool) (x pre rest a : List Bool) (b : Bool)
    (hx : x = pre ++ b :: rest) :
    (pairExtractTM first second).tm.step
      (extractCfg x (some (.inl none)) pre.length (by simp [hx]) a a.length []) =
      extractCfg x (some (.inl (some b))) (pre.length + 1) (by simp [hx]) a a.length [] := by
  unfold MultiTapeTM.step
  change ((pairExtractTM first second).tm.tr (.inl none) _ _).apply _ = _
  rw [extractCfg_read]
  have hr : x[pre.length]? = some b := by simp [hx]
  rw [hr]
  refine Cfg.ext rfl ?_ rfl ?_ rfl
  · exact moveInputPos_pos_of_ne_right _ (by simp [extractCfg, hx])
  · funext i; simp [pairExtractTM, Action.apply, extractCfg]

/-- Equal-bit blocks append one decoded bit; `01` begins replay and `10`
halts silently. In particular, neither transition emits physical output. -/
private lemma extract_block (first second : Bool) (x pre rest a : List Bool) (b c : Bool)
    (hx : x = pre ++ b :: c :: rest) :
    (pairExtractTM first second).tm.runFrom
      (extractCfg x (some (.inl none)) pre.length (by simp [hx]) a a.length []) 2 =
      if b = c then extractCfg x (some (.inl none)) (pre.length + 2) (by simp [hx])
          (a ++ [b]) (a ++ [b]).length []
      else if b then extractCfg x none (pre.length + 2) (by simp [hx]) a a.length []
      else extractCfg x (some (.inr 0)) (pre.length + 2) (by simp [hx]) a (a.length - 1) [] := by
  change (pairExtractTM first second).tm.step ((pairExtractTM first second).tm.step _) = _
  rw [extract_first first second x pre (c :: rest) a b hx]
  unfold MultiTapeTM.step
  change ((pairExtractTM first second).tm.tr (.inl (some b)) _ _).apply _ = _
  rw [extractCfg_read]
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
    | (funext i; simp [pairExtractTM, Action.apply, extractCfg])

/-- Rewinding the validated buffer from cell `j-1` takes `j+1` transitions.
**Proof sketch.** At the left blank, move right and enter replay. Otherwise
read a buffer cell, move left, and invoke the induction hypothesis. -/
private lemma extract_rewind (first second : Bool) (x a : List Bool)
    (i : ℕ) (hi : i ≤ x.length) : ∀ j, j ≤ a.length →
    (pairExtractTM first second).tm.runFrom
      (extractCfg x (some (.inr 0)) i hi a ((j : ℤ) - 1) []) (j + 1) =
      extractCfg x (some (.inr 1)) i hi a 0 [] := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    simp only [pairExtractTM, extractCfg, Cfg.workTapeSymbols, Nat.cast_zero,
      zero_sub, bufferTape_left]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext k; simp [Action.apply]
  | succ j ih =>
    intro hj
    have hs : (pairExtractTM first second).tm.step
        (extractCfg x (some (.inr 0)) i hi a (((j + 1 : ℕ) : ℤ) - 1) []) =
        extractCfg x (some (.inr 0)) i hi a ((j : ℤ) - 1) [] := by
      have hz : (((j + 1 : ℕ) : ℤ) - 1) = j := by omega
      rw [hz]
      unfold MultiTapeTM.step
      simp only [pairExtractTM, extractCfg, Cfg.workTapeSymbols, bufferTape_nat,
        List.getElem?_eq_getElem (by omega : j < a.length)]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext k; simp [Action.apply, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Replay reads the buffered word once; the first-component flag decides
whether those reads emit. At the right blank the controller starts the suffix.
**Proof sketch.** Induct on the number of replayed cells. Each live step
preserves the tape and appends either its bit or nothing. -/
private lemma extract_replay (first second : Bool) (x a : List Bool)
    (i : ℕ) (hi : i ≤ x.length) : ∀ j (_hj : j ≤ a.length),
    (pairExtractTM first second).tm.runFrom
      (extractCfg x (some (.inr 1)) i hi a 0 []) j =
      extractCfg x (some (.inr 1)) i hi a j (if first then a.take j else []) := by
  intro j
  induction j with
  | zero => intro hj; cases first <;> rfl
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    unfold MultiTapeTM.step
    simp only [pairExtractTM, extractCfg, Cfg.workTapeSymbols, bufferTape_nat,
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
private lemma extract_replay_finish (first second : Bool) (x a : List Bool)
    (i : ℕ) (hi : i ≤ x.length) :
    (pairExtractTM first second).tm.runFrom
      (extractCfg x (some (.inr 1)) i hi a 0 []) (a.length + 1) =
      extractCfg x (some (.inr 2)) i hi a a.length (if first then a else []) := by
  rw [MultiTapeTM.runFrom_succ_eq_step', extract_replay first second x a i hi _ (by omega)]
  unfold MultiTapeTM.step
  simp only [pairExtractTM, extractCfg, Cfg.workTapeSymbols, bufferTape_nat,
    List.getElem?_length, List.take_length]
  refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ ?_
  · funext k; simp [Action.apply]
  · simp [Action.apply]

/-- With suffix copying enabled, the final phase emits the remaining input.
**Proof sketch.** The input prefix grows by one at each emitting transition;
the buffer and its head remain fixed. A right-blank test supplies the final
halting step. This is the one-buffer version of the private suffix-copy lemma. -/
private lemma extract_suffix (first : Bool) (x rest a : List Bool) :
    ∀ pre out (hx : x = pre ++ rest),
    (pairExtractTM first true).tm.runFrom
      (extractCfg x (some (.inr 2)) pre.length (by simp [hx]) a a.length out)
        (rest.length + 1) =
      extractCfg x none x.length (by omega) a a.length (out ++ rest) := by
  induction rest with
  | nil =>
    intro pre out hx
    simp only [List.length_nil, MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change ((pairExtractTM first true).tm.tr (.inr 2) _ _).apply _ = _
    rw [extractCfg_read]
    have hr : x[pre.length]? = none := by simp [hx]
    rw [hr]
    refine Cfg.ext rfl ?_ rfl ?_ ?_
    · simp [pairExtractTM, Action.apply, extractCfg, hx]
    · funext k; simp [pairExtractTM, Action.apply, extractCfg]
    · simp [pairExtractTM, Action.apply, extractCfg]
  | cons b rest ih =>
    intro pre out hx
    have hs : (pairExtractTM first true).tm.step
        (extractCfg x (some (.inr 2)) pre.length (by simp [hx]) a a.length out) =
        extractCfg x (some (.inr 2)) (pre ++ [b]).length (by simp [hx])
          a a.length (out ++ [b]) := by
      unfold MultiTapeTM.step
      change ((pairExtractTM first true).tm.tr (.inr 2) _ _).apply _ = _
      rw [extractCfg_read]
      have hr : x[pre.length]? = some b := by simp [hx]
      rw [hr]
      refine Cfg.ext rfl ?_ rfl ?_ rfl
      · simpa [extractCfg] using moveInputPos_pos_of_ne_right
          (⟨pre.length + 1, by simp [hx]; omega⟩ : Fin (x.length + 2)) (by simp [hx])
      · funext k; simp [pairExtractTM, Action.apply, extractCfg]
    simp only [List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    simpa only [List.append_assoc, List.singleton_append] using
      ih (pre ++ [b]) (out ++ [b]) (by simpa [List.append_assoc] using hx)

/-- Once validation succeeds, rewind, replay, and optional suffix copying
cost at most `2|a|+|rest|+3` steps.
**Proof sketch.** The rewind costs `|a|+1`, and replay plus dispatch costs
`|a|+1`. Disabled suffix copying halts in one step; enabled copying uses
`|rest|+1`. Only these postvalidation phases emit output. -/
private lemma extract_finish (first second : Bool) (x pre rest a : List Bool)
    (hx : x = pre ++ rest) :
    ∃ t ≤ 2 * a.length + rest.length + 3,
      ((pairExtractTM first second).tm.runFrom
        (extractCfg x (some (.inr 0)) pre.length (by simp [hx]) a (a.length - 1) []) t).state = none ∧
      ((pairExtractTM first second).tm.runFrom
        (extractCfg x (some (.inr 0)) pre.length (by simp [hx]) a (a.length - 1) []) t).output =
          (if first then a else []) ++ (if second then rest else []) := by
  have hp : (pairExtractTM first second).tm.runFrom
      (extractCfg x (some (.inr 0)) pre.length (by simp [hx]) a (a.length - 1) [])
        ((a.length + 1) + (a.length + 1)) =
      extractCfg x (some (.inr 2)) pre.length (by simp [hx]) a a.length (if first then a else []) := by
    rw [MultiTapeTM.runFrom_add, extract_rewind first second x a _ _ _ (by omega),
      extract_replay_finish]
  cases second with
  | false =>
    refine ⟨(a.length + 1) + (a.length + 1) + 1, by omega, ?_⟩
    rw [MultiTapeTM.runFrom_succ_eq_step', hp]
    simp [MultiTapeTM.step, pairExtractTM, extractCfg, Action.apply]
  | true =>
    refine ⟨((a.length + 1) + (a.length + 1)) + (rest.length + 1), by omega, ?_⟩
    rw [MultiTapeTM.runFrom_add, hp, extract_suffix first x rest a pre _ hx]
    exact ⟨rfl, rfl⟩

/-- The silent aligned parser either rejects or validates and invokes replay.
**Proof sketch.** Induct over aligned two-bit blocks while carrying the
already-decoded buffer. A doubled bit costs two steps and enlarges the buffer
by one; the linear potential `3|rest|+2|a|+5` pays for both effects. Missing
and forbidden separators halt silently. At `01`, apply the validated finish
ledger. The result includes the previously buffered prefix only on success. -/
private lemma extract_run (first second : Bool) (x rest : List Bool) :
    ∀ pre a (hx : x = pre ++ rest),
    ∃ t ≤ 3 * rest.length + 2 * a.length + 5,
      ((pairExtractTM first second).tm.runFrom
        (extractCfg x (some (.inl none)) pre.length (by simp [hx]) a a.length []) t).state = none ∧
      ((pairExtractTM first second).tm.runFrom
        (extractCfg x (some (.inl none)) pre.length (by simp [hx]) a a.length []) t).output =
          match pairDecode rest with
          | some (b, c) => (if first then a ++ b else []) ++ (if second then c else [])
          | none => [] := by
  induction rest using List.twoStepInduction with
  | nil =>
    intro pre a hx
    refine ⟨1, by omega, ?_⟩
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change (((pairExtractTM first second).tm.tr (.inl none) _ _).apply _).state = none ∧ _
    rw [extractCfg_read]
    simp [hx, pairExtractTM, Action.apply, extractCfg, pairDecode]
  | singleton b =>
    intro pre a hx
    refine ⟨2, by simp, ?_⟩
    change ((pairExtractTM first second).tm.step ((pairExtractTM first second).tm.step _)).state = none ∧
      ((pairExtractTM first second).tm.step ((pairExtractTM first second).tm.step _)).output = _
    rw [extract_first first second x pre [] a b hx]
    unfold MultiTapeTM.step
    change (((pairExtractTM first second).tm.tr (.inl (some b)) _ _).apply _).state = none ∧ _
    rw [extractCfg_read]
    cases b <;> simp [hx, pairExtractTM, Action.apply, extractCfg, pairDecode]
  | cons_cons b c rest ih _ =>
    intro pre a hx
    by_cases h : b = c
    · subst c
      obtain ⟨t, ht, hs, ho⟩ := ih (pre ++ [b, b]) (a ++ [b]) (by simpa [List.append_assoc] using hx)
      refine ⟨2 + t, by simp only [List.length_append, List.length_cons, List.length_nil] at *; omega, ?_⟩
      rw [MultiTapeTM.runFrom_add, extract_block first second x pre rest a b b hx, if_pos rfl]
      simp only [List.length_append, List.length_cons, List.length_nil] at hs ho
      refine ⟨?_, ?_⟩
      · simpa only [List.length_append, List.length_cons, List.length_nil] using hs
      · cases b <;> cases hd : pairDecode rest with
        | none => simpa [pairDecode, hd] using ho
        | some p => cases p; simpa [pairDecode, hd, List.append_assoc] using ho
    · cases b <;> cases c
      · exact False.elim (h rfl)
      · obtain ⟨t, ht, hs, ho⟩ := extract_finish first second x (pre ++ [false, true]) rest a
          (by simpa [List.append_assoc] using hx)
        refine ⟨2 + t, by simp only [List.length_cons]; omega, ?_⟩
        rw [MultiTapeTM.runFrom_add, extract_block first second x pre rest a false true hx]
        simp only [Bool.false_eq_true, ↓reduceIte]
        simp only [List.length_append, List.length_cons, List.length_nil] at hs ho
        exact ⟨hs, by simpa [pairDecode] using ho⟩
      · refine ⟨2, by simp, ?_⟩
        rw [extract_block first second x pre rest a true false hx]
        simp [extractCfg, pairDecode]
      · exact False.elim (h rfl)

/-- The three extractor modes share the uniform linear envelope `5(|x|+1)`.
The initial buffer and decoded prefix are empty. -/
private lemma pairExtract_computes (first second : Bool) (x : List Bool) :
    (pairExtractTM first second).ComputesInTime x
      (match pairDecode x with
        | some (a, b) => (if first then a else []) ++ (if second then b else [])
        | none => []) (5 * (x.length + 1)) := by
  obtain ⟨t, ht, hs, ho⟩ := extract_run first second x x [] [] rfl
  have hinit : (pairExtractTM first second).tm.initCfg x =
      extractCfg x (some (.inl none)) 0 (by omega) [] 0 [] := by
    apply Cfg.ext <;> simp [pairExtractTM, extractCfg, MultiTapeTM.initCfg, Cfg.init]
  have hh : (pairExtractTM first second).ComputesInTime x
      (match pairDecode x with
        | some (a, b) => (if first then a else []) ++ (if second then b else [])
        | none => []) t := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [hinit]
    exact ⟨hs, by simpa using ho⟩
  exact hh.mono (by simp only [List.length_nil] at ht; omega)

/-! The unary polynomial generator below is adapted privately from
`ClassNP/TMSAT.lean`, including its exact loop-depth ledger. -/

/-- Control for copying the side length, nested unary loops, and constant emission. -/
private inductive CatalogPolyControl (c C : ℕ) where
  | copy | setup
  | loop (i : Fin (c + 1))
  | rewind (i : Fin (c + 1))
  | advance (i : Fin (c + 2))
  | emit (j : Fin (C + 1))

/-- Enumerate the control through a finite sum representation, privately. -/
private instance catalogPolyControlFintype (c C : ℕ) : Fintype (CatalogPolyControl c C) :=
  derive_fintype% _

/-- Compare control states through the same finite sum representation, privately. -/
private instance catalogPolyControlDecidableEq (c C : ℕ) : DecidableEq (CatalogPolyControl c C) :=
  (proxy_equiv% (CatalogPolyControl c C)).symm.decidableEq

/-- A unary word of length `q`, surrounded by blanks. -/
private def catalogPolyTape (q : ℕ) (z : ℤ) : Option Bool :=
  if 0 ≤ z ∧ z < q then some true else none

/-- Move just the selected work head, preserving every tape. -/
private def catalogPolyMove {c C : ℕ} (i : Fin (c + 1)) (d : SignType)
    (s : CatalogPolyControl c C) : Action (c + 1) Bool (CatalogPolyControl c C) :=
  ⟨0, fun j => (none, if j = i then d else 0), none, some s⟩

/-- Finite machine emitting `C` symbols at each point of a `(c+1)`-dimensional
box. The unary loop tapes are copied in parallel; rewinding a completed inner
loop costs its side length, charged to the iterations that just completed. -/
private def catalogPolyUnaryTM (c C : ℕ) : FinTM Bool where
  k := c + 1
  State := CatalogPolyControl c C
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
        if w i = none then catalogPolyMove i .neg (.rewind i)
        else ⟨0, fun _ => (none, 0), none,
          some (if h : i.val = 0 then .emit ⟨C, Nat.lt_succ_self C⟩
            else .loop ⟨i.val - 1, by omega⟩)⟩
      | .rewind i =>
        if w i = none then catalogPolyMove i .pos (.advance ⟨i.val + 1, by omega⟩)
        else catalogPolyMove i .neg (.rewind i)
      | .advance i =>
        if h : i.val < c + 1 then catalogPolyMove ⟨i.val, h⟩ .pos (.loop ⟨i.val, h⟩)
        else ⟨0, fun _ => (none, 0), none, none⟩
      | .emit j =>
        if h : j.val = 0 then ⟨0, fun _ => (none, 0), none, some (.advance 0)⟩
        else ⟨0, fun _ => (none, 0), some true,
          some (.emit ⟨j.val - 1, by omega⟩)⟩ }

/-- A loop configuration, with all unary tapes installed and arbitrary head positions. -/
private def catalogPolyCfg {c C : ℕ} (x : List Bool) (q : ℕ)
    (s : CatalogPolyControl c C) (h : Fin (c + 1) → ℤ) (o : List Bool) :
    Cfg (c + 1) Bool (CatalogPolyControl c C) x :=
  ⟨some s, ⟨x.length + 1, by omega⟩, fun _ => catalogPolyTape q, h, o⟩

/-- Applying a head-only action updates exactly the selected head. -/
private lemma catalogPolyMove_apply {c C : ℕ} (x : List Bool) (q : ℕ)
    (s s' : CatalogPolyControl c C) (h : Fin (c + 1) → ℤ) (o : List Bool)
    (i : Fin (c + 1)) (d : SignType) :
    (catalogPolyMove i d s').apply (catalogPolyCfg x q s h o) =
      catalogPolyCfg x q s' (Function.update h i (h i + d.cast)) o := by
  apply Cfg.ext
  · rfl
  · exact moveInputPos_zero _
  · rfl
  · funext j
    by_cases hj : j = i <;> simp [catalogPolyMove, catalogPolyCfg, Action.apply, hj]
  · simp [catalogPolyMove, catalogPolyCfg, Action.apply]

/-- The finite emission chain appends exactly its remaining number of true bits. -/
private lemma catalogPoly_emit {c C : ℕ} (x : List Bool) (q : ℕ)
    (h : Fin (c + 1) → ℤ) : ∀ j (hj : j ≤ C) (o : List Bool),
    (catalogPolyUnaryTM c C).tm.runFrom
      (catalogPolyCfg x q (.emit ⟨j, by omega⟩) h o) (j + 1) =
      catalogPolyCfg x q (.advance 0) h (o ++ List.replicate j true) := by
  intro j
  induction j with
  | zero =>
    intro hj o
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    apply Cfg.ext <;> simp [MultiTapeTM.step, catalogPolyUnaryTM, catalogPolyCfg, Action.apply]
  | succ j ih =>
    intro hj o
    have hs : (catalogPolyUnaryTM c C).tm.step
        (catalogPolyCfg x q (.emit ⟨j + 1, by omega⟩) h o) =
        catalogPolyCfg x q (.emit ⟨j, by omega⟩) h (o ++ [true]) := by
      apply Cfg.ext <;> simp [MultiTapeTM.step, catalogPolyUnaryTM, catalogPolyCfg, Action.apply]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs, ih (by omega)]
    simp [List.replicate_succ, List.append_assoc]

/-- Rewinding crosses a unary prefix and its left boundary, restoring head zero.
The other loop heads and the accumulated output remain unchanged. -/
private lemma catalogPoly_rewind {c C : ℕ} (x : List Bool) (q : ℕ)
    (h : Fin (c + 1) → ℤ) (o : List Bool) (i : Fin (c + 1)) :
    ∀ j (_hj : j ≤ q),
    (catalogPolyUnaryTM c C).tm.runFrom
      (catalogPolyCfg x q (.rewind i) (Function.update h i ((j : ℤ) - 1)) o) (j + 1) =
      catalogPolyCfg x q (.advance ⟨i.val + 1, by omega⟩) (Function.update h i 0) o := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    change ((if _ then _ else _) : Action (c + 1) Bool (CatalogPolyControl c C)).apply _ = _
    simp only [Cfg.workTapeSymbols, catalogPolyCfg, Function.update_self,
      Nat.cast_zero, zero_sub, catalogPolyTape, show ¬(0 ≤ (-1 : ℤ) ∧ (-1 : ℤ) < q) by omega,
      ↓reduceIte]
    simpa [catalogPolyCfg] using catalogPolyMove_apply x q (.rewind i)
      (.advance ⟨i.val + 1, by omega⟩) (Function.update h i (-1)) o i .pos
  | succ j ih =>
    intro hj
    have hs : (catalogPolyUnaryTM c C).tm.step
        (catalogPolyCfg x q (.rewind i) (Function.update h i ((j + 1 : ℕ) - 1 : ℤ)) o) =
        catalogPolyCfg x q (.rewind i) (Function.update h i ((j : ℤ) - 1)) o := by
      change ((if _ then _ else _) : Action (c + 1) Bool (CatalogPolyControl c C)).apply _ = _
      simp only [Cfg.workTapeSymbols, catalogPolyCfg, Function.update_self,
        Nat.cast_add, Nat.cast_one, add_sub_cancel_right, catalogPolyTape,
        if_pos (show 0 ≤ (j : ℤ) ∧ (j : ℤ) < q by omega),
        reduceCtorEq, ↓reduceIte]
      simpa [catalogPolyCfg, sub_eq_add_neg] using catalogPolyMove_apply x q (.rewind i)
        (.rewind i) (Function.update h i (j : ℤ)) o i .neg
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Returning from an inner loop advances the next outer loop by one cell. -/
private lemma catalogPoly_advance {c C : ℕ} (x : List Bool) (q : ℕ)
    (h : Fin (c + 1) → ℤ) (o : List Bool) (i : Fin (c + 1)) :
    (catalogPolyUnaryTM c C).tm.step
      (catalogPolyCfg x q (.advance ⟨i.val, by omega⟩) h o) =
      catalogPolyCfg x q (.loop i) (Function.update h i (h i + 1)) o := by
  simp only [MultiTapeTM.step, catalogPolyUnaryTM, catalogPolyCfg, i.isLt, ↓reduceDIte]
  simpa [catalogPolyCfg] using catalogPolyMove_apply x q
    (.advance ⟨i.val, by omega⟩) (.loop i) h o i .pos

/-- Exact time for a full nest of unary loops, with `r` loop levels. -/
private def catalogPolyCost (q C : ℕ) : ℕ → ℕ
  | 0 => C + 1
  | r + 1 => q * (catalogPolyCost q C r + 2) + q + 2

/-- A loop at level `i` executes its remaining iterations, resets its head,
and returns to its parent with exactly `C*q^i` new symbols per iteration.

**Proof sketch.** Induct on the nesting level, then on the number of remaining
iterations. At level zero the body is the finite emission chain. At higher
levels it is a complete inner loop. Each body has one dispatch and one parent
advance; after the final iteration the unary rewind restores the head to zero.
The invariant leaves all outer heads arbitrary, making recursive calls composable. -/
private lemma catalogPoly_loop {c C : ℕ} (x : List Bool) (q : ℕ) (_hq : 0 < q) :
    ∀ i (hi : i < c + 1) (h : Fin (c + 1) → ℤ)
      (_hh : ∀ k, k.val ≤ i → h k = 0) (o : List Bool) (r j : ℕ), j + r = q →
    (catalogPolyUnaryTM c C).tm.runFrom
      (catalogPolyCfg x q (.loop ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ (j : ℤ)) o)
      (r * (catalogPolyCost q C i + 2) + q + 2) =
      catalogPolyCfg x q (.advance ⟨i + 1, by omega⟩) h
        (o ++ List.replicate (r * (C * q ^ i)) true) := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi h hh o r
    have hbody (j : ℕ) (hj : j < q) (o : List Bool) :
        (catalogPolyUnaryTM c C).tm.runFrom
          (catalogPolyCfg x q (.loop ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ (j : ℤ)) o)
          (catalogPolyCost q C i + 2) =
        catalogPolyCfg x q (.loop ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ ((j : ℤ) + 1))
          (o ++ List.replicate (C * q ^ i) true) := by
      let h' := Function.update h ⟨i, hi⟩ (j : ℤ)
      have hread : (catalogPolyCfg (C := C) x q (.loop ⟨i, hi⟩) h' o).workTapeSymbols ⟨i, hi⟩ =
          some true := by simp [h', catalogPolyCfg, Cfg.workTapeSymbols, catalogPolyTape, hj]
      have hs : (catalogPolyUnaryTM c C).tm.step (catalogPolyCfg x q (.loop ⟨i, hi⟩) h' o) =
          catalogPolyCfg x q (if hz : i = 0 then .emit ⟨C, by omega⟩
            else .loop ⟨i - 1, by omega⟩) h' o := by
        unfold MultiTapeTM.step
        change ((catalogPolyUnaryTM c C).tm.tr (.loop ⟨i, hi⟩) _ _).apply _ = _
        simp only [catalogPolyUnaryTM, hread, reduceCtorEq, ↓reduceIte]
        apply Cfg.ext <;> simp [catalogPolyCfg, Action.apply]
      by_cases hz : i = 0
      · subst i
        simp only [↓reduceDIte] at hs
        change (catalogPolyUnaryTM c C).tm.runFrom (catalogPolyCfg x q (.loop 0) h' o) _ = _
        rw [show catalogPolyCost q C 0 + 2 = 1 + (C + 1) + 1 by simp [catalogPolyCost]; omega,
          MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add,
          show (catalogPolyUnaryTM c C).tm.runFrom (catalogPolyCfg x q (.loop 0) h' o) 1 =
            catalogPolyCfg x q (.emit ⟨C, by omega⟩) h' o by simpa using hs,
          catalogPoly_emit x q h' C (le_refl C),
          MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
        simpa [h'] using catalogPoly_advance (C := C) x q h'
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
        have hinner' : (catalogPolyUnaryTM c C).tm.runFrom
            (catalogPolyCfg x q (.loop ⟨i - 1, by omega⟩) h' o) (catalogPolyCost q C i) =
            catalogPolyCfg x q (.advance ⟨i, by omega⟩) h'
              (o ++ List.replicate (C * q ^ i) true) := by
          have hcost : q * (catalogPolyCost q C (i - 1) + 2) + q + 2 =
              catalogPolyCost q C i := by
            calc
              _ = catalogPolyCost q C (i - 1 + 1) := rfl
              _ = catalogPolyCost q C i := by rw [hi']
          simpa only [hcost, hi', hout] using hinner
        change (catalogPolyUnaryTM c C).tm.runFrom (catalogPolyCfg x q (.loop ⟨i, hi⟩) h' o) _ = _
        rw [show catalogPolyCost q C i + 2 = 1 + catalogPolyCost q C i + 1 by omega,
          MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add,
          show (catalogPolyUnaryTM c C).tm.runFrom (catalogPolyCfg x q (.loop ⟨i, hi⟩) h' o) 1 =
            catalogPolyCfg x q (.loop ⟨i - 1, by omega⟩) h' o by simpa using hs,
          hinner', MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
        simpa [h'] using catalogPoly_advance (C := C) x q h'
          (o ++ List.replicate (C * q ^ i) true) (⟨i, hi⟩ : Fin (c + 1))
    induction r generalizing o with
    | zero =>
      intro j hj
      have hj' : j = q := by omega
      subst j
      have hs : (catalogPolyUnaryTM c C).tm.step
          (catalogPolyCfg x q (.loop ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ (q : ℤ)) o) =
          catalogPolyCfg x q (.rewind ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ ((q : ℤ) - 1)) o := by
        unfold MultiTapeTM.step
        change ((catalogPolyUnaryTM c C).tm.tr (.loop ⟨i, hi⟩) _ _).apply _ = _
        simp only [catalogPolyUnaryTM, Cfg.workTapeSymbols, catalogPolyCfg, Function.update_self,
          catalogPolyTape, lt_self_iff_false, and_false, ↓reduceIte]
        simpa [catalogPolyCfg, sub_eq_add_neg] using catalogPolyMove_apply x q (.loop ⟨i, hi⟩)
          (.rewind ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ (q : ℤ)) o ⟨i, hi⟩ .neg
      simp only [Nat.zero_mul, Nat.zero_add, List.replicate_zero, List.append_nil]
      rw [MultiTapeTM.runFrom_succ_eq_step, hs, catalogPoly_rewind x q h o ⟨i, hi⟩ q (le_refl q)]
      rw [← hh ⟨i, hi⟩ (le_refl _), Function.update_eq_self]
    | succ r ihr =>
      intro j hj
      have hjq : j < q := by omega
      rw [show (r + 1) * (catalogPolyCost q C i + 2) + q + 2 =
          (catalogPolyCost q C i + 2) + (r * (catalogPolyCost q C i + 2) + q + 2) by ring,
        MultiTapeTM.runFrom_add, hbody j hjq]
      have hr := ihr (o ++ List.replicate (C * q ^ i) true) (j + 1) (by omega)
      simp only [Nat.cast_add, Nat.cast_one] at hr
      rw [hr, List.append_assoc, ← List.replicate_add]
      congr 3
      ring

/-- Writing at the first blank extends a unary tape by exactly one cell. -/
private lemma catalogPolyTape_write (q : ℕ) :
    Function.update (catalogPolyTape q) (q : ℤ) (some true) = catalogPolyTape (q + 1) := by
  funext z
  by_cases hz : z = (q : ℤ)
  · subst z
    simp [catalogPolyTape]
  · rw [Function.update_of_ne hz]
    unfold catalogPolyTape
    have he : (0 ≤ z ∧ z < (q : ℤ)) ↔ (0 ≤ z ∧ z < ((q + 1 : ℕ) : ℤ)) := by omega
    simp only [he]

/-- The full loop costs at most a constant times the number of box points.
Each level's rewinds are charged to its `q` completed body iterations. -/
private lemma catalogPolyCost_le (q C : ℕ) (hq : 0 < q) : ∀ r,
    catalogPolyCost q C r ≤ (C + 1 + 5 * r) * q ^ r := by
  intro r
  induction r with
  | zero => simp [catalogPolyCost]
  | succ r ih =>
    have hqpow : q ≤ q ^ (r + 1) := by
      simpa only [Nat.pow_one] using Nat.pow_le_pow_right hq (show 1 ≤ r + 1 by omega)
    have hpos : 1 ≤ q ^ (r + 1) := Nat.one_le_pow _ _ hq
    calc
      catalogPolyCost q C (r + 1) = q * (catalogPolyCost q C r + 2) + q + 2 := rfl
      _ ≤ q * ((C + 1 + 5 * r) * q ^ r + 2) + q + 2 :=
        Nat.add_le_add_right (Nat.add_le_add_right
          (Nat.mul_le_mul_left q (Nat.add_le_add_right ih 2)) q) 2
      _ = (C + 1 + 5 * r) * q ^ (r + 1) + 3 * q + 2 := by rw [Nat.pow_succ]; ring
      _ ≤ (C + 1 + 5 * r) * q ^ (r + 1) + 5 * q ^ (r + 1) := by omega
      _ = (C + 1 + 5 * (r + 1)) * q ^ (r + 1) := by ring

/-- Configurations while copying the input length to every unary loop tape. -/
private def catalogPolyCopyCfg (c C : ℕ) (x : List Bool) (i : ℕ) (hi : i ≤ x.length) :
    Cfg (c + 1) Bool (CatalogPolyControl c C) x :=
  ⟨some .copy, ⟨i + 1, by omega⟩, fun _ => catalogPolyTape i, fun _ => i, []⟩

/-- One input scan copies its length, in unary, onto every loop tape at once. -/
private lemma catalogPoly_copy (c C : ℕ) (x : List Bool) : ∀ i (hi : i ≤ x.length),
    (catalogPolyUnaryTM c C).tm.runFrom ((catalogPolyUnaryTM c C).tm.initCfg x) i =
      catalogPolyCopyCfg c C x i hi := by
  intro i
  induction i with
  | zero =>
    intro hi
    apply Cfg.ext
    · rfl
    · rfl
    · funext k z
      simp [MultiTapeTM.initCfg, Cfg.init, catalogPolyCopyCfg, catalogPolyTape,
        show ¬(0 ≤ z ∧ z < (0 : ℤ)) by omega]
    · rfl
    · rfl
  | succ i ih =>
    intro hi
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hin : (catalogPolyCopyCfg c C x i (by omega)).inputSymbol = some x[i] :=
      inputSymbolInner i (by simp [catalogPolyCopyCfg, Nat.add_comm]) (by omega)
    unfold MultiTapeTM.step
    change ((catalogPolyUnaryTM c C).tm.tr .copy _ _).apply _ = _
    rw [hin]
    apply Cfg.ext
    · rfl
    · apply Fin.ext
      change (moveInputPos (⟨i + 1, by omega⟩ : Fin (x.length + 2)) .pos).val = i + 1 + 1
      rw [moveInputPos_pos_of_ne_right _ (by simp; omega)]
    · funext k
      exact catalogPolyTape_write i
    · funext k
      simp [catalogPolyUnaryTM, catalogPolyCopyCfg, Action.apply, Nat.add_comm]
    · rfl

/-- The startup rewind moves all synchronized heads left, then enters the outermost loop. -/
private lemma catalogPoly_setup (c C : ℕ) (x : List Bool) (q : ℕ) : ∀ j (_hj : j ≤ q),
    (catalogPolyUnaryTM c C).tm.runFrom
      (catalogPolyCfg x q .setup (fun _ => (j : ℤ) - 1) []) (j + 1) =
      catalogPolyCfg x q (.loop (Fin.last c)) (fun _ => 0) [] := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    apply Cfg.ext <;>
      simp [MultiTapeTM.step, catalogPolyUnaryTM, catalogPolyCfg, Cfg.workTapeSymbols, catalogPolyTape, Action.apply]
  | succ j ih =>
    intro hj
    have hs : (catalogPolyUnaryTM c C).tm.step
        (catalogPolyCfg x q .setup (fun _ => ((j + 1 : ℕ) : ℤ) - 1) []) =
        catalogPolyCfg x q .setup (fun _ => (j : ℤ) - 1) [] := by
      apply Cfg.ext <;>
        simp [MultiTapeTM.step, catalogPolyUnaryTM, catalogPolyCfg, Cfg.workTapeSymbols, catalogPolyTape,
          show (j : ℤ) < q by omega, Action.apply, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Startup installs side length `|x|+1` and puts every loop head at zero.
The final extra unary cell handles empty input without a special case. -/
private lemma catalogPoly_start (c C : ℕ) (x : List Bool) :
    (catalogPolyUnaryTM c C).tm.runFrom ((catalogPolyUnaryTM c C).tm.initCfg x)
      (2 * (x.length + 1)) =
      catalogPolyCfg x (x.length + 1) (.loop (Fin.last c)) (fun _ => 0) [] := by
  have hs : (catalogPolyUnaryTM c C).tm.step
      (catalogPolyCopyCfg c C x x.length (le_refl _)) =
      catalogPolyCfg x (x.length + 1) .setup (fun _ => (x.length : ℤ) - 1) [] := by
    have hin : (catalogPolyCopyCfg c C x x.length (le_refl _)).inputSymbol = none := by
      simp [catalogPolyCopyCfg, Cfg.inputSymbol]
    unfold MultiTapeTM.step
    change ((catalogPolyUnaryTM c C).tm.tr .copy _ _).apply _ = _
    rw [hin]
    apply Cfg.ext
    · rfl
    · exact moveInputPos_zero _
    · funext k
      exact catalogPolyTape_write x.length
    · funext k
      simp [catalogPolyUnaryTM, catalogPolyCopyCfg, catalogPolyCfg, Action.apply, sub_eq_add_neg]
    · rfl
  have hpre : (catalogPolyUnaryTM c C).tm.runFrom ((catalogPolyUnaryTM c C).tm.initCfg x)
      (x.length + 1) =
      catalogPolyCfg x (x.length + 1) .setup (fun _ => (x.length : ℤ) - 1) [] := by
    rw [MultiTapeTM.runFrom_succ_eq_step', catalogPoly_copy c C x x.length (le_refl _), hs]
  rw [show 2 * (x.length + 1) = (x.length + 1) + (x.length + 1) by omega,
    MultiTapeTM.runFrom_add, hpre]
  exact catalogPoly_setup c C x (x.length + 1) x.length (by omega)

/-- The explicit generator computes the exact unary catalogPolynomial in linear time
in its number of box points. This includes coefficient zero and empty input.

**Proof sketch.** Startup costs `2(n+1)`. The full outer loop emits
`C(n+1)^(c+1)` symbols and costs at most `(C+1+5(c+1))(n+1)^(c+1)`.
One final transition halts; `n+1 ≤ (n+1)^(c+1)` absorbs startup. -/
private lemma catalogPoly_unary_computes (c C : ℕ) :
    (catalogPolyUnaryTM c C).ComputesFunInTime
      (fun x => List.replicate (C * (x.length + 1) ^ (c + 1)) true)
      (fun n => (C + 5 * (c + 1) + 4) * (n + 1) ^ (c + 1)) := by
  intro x
  have hl := catalogPoly_loop (c := c) (C := C) x (x.length + 1) (Nat.succ_pos _) c (by omega)
    (fun _ => 0) (by simp) [] (x.length + 1) 0 (by omega)
  have hout : (x.length + 1) * (C * (x.length + 1) ^ c) =
      C * (x.length + 1) ^ (c + 1) := by rw [Nat.pow_succ]; ring
  have hloop : (catalogPolyUnaryTM c C).tm.runFrom
      (catalogPolyCfg x (x.length + 1) (.loop (Fin.last c)) (fun _ => 0) [])
      (catalogPolyCost (x.length + 1) C (c + 1)) =
      catalogPolyCfg x (x.length + 1) (.advance (Fin.last (c + 1))) (fun _ => 0)
        (List.replicate (C * (x.length + 1) ^ (c + 1)) true) := by
    simpa [catalogPolyCost, hout] using hl
  have hbase : (catalogPolyUnaryTM c C).ComputesInTime x
      (List.replicate (C * (x.length + 1) ^ (c + 1)) true)
      (2 * (x.length + 1) + catalogPolyCost (x.length + 1) C (c + 1) + 1) := by
    apply (FinTM.computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_add, catalogPoly_start, hloop]
    simp [MultiTapeTM.step, catalogPolyUnaryTM, catalogPolyCfg, Action.apply]
  apply hbase.mono
  have hp : x.length + 1 ≤ (x.length + 1) ^ (c + 1) := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right (Nat.succ_pos x.length)
      (show 1 ≤ c + 1 by omega)
  have hpos : 1 ≤ (x.length + 1) ^ (c + 1) := Nat.one_le_pow _ _ (Nat.succ_pos _)
  calc
    _ ≤ 2 * (x.length + 1) +
        (C + 1 + 5 * (c + 1)) * (x.length + 1) ^ (c + 1) + 1 :=
      Nat.add_le_add_right (Nat.add_le_add_left
        (catalogPolyCost_le (x.length + 1) C (Nat.succ_pos _) (c + 1)) _) 1
    _ ≤ (C + 1 + 5 * (c + 1)) * (x.length + 1) ^ (c + 1) +
        3 * (x.length + 1) ^ (c + 1) := by omega
    _ = _ := by ring


/-- Administrative actions for the captured length checker move only the
input and final (countdown) head. No tape is written. -/
private def lenAction (M : FinTM Bool) (m d : SignType) (b : Option Bool)
    (q : Option (M.State ⊕ (Fin 4 ⊕ Option Bool))) :
    Action (M.k + 1) Bool (M.State ⊕ (Fin 4 ⊕ Option Bool)) :=
  ⟨m, fun i => (none, if i.val < M.k then 0 else d), b, q⟩

/-- Capture a total generator, rewind the physical input, validate its pair
syntax, then compare the suffix length with the captured word's length.
Only the final comparison or rejection transition emits a verdict. -/
private def pairCountTM (M : FinTM Bool) : FinTM Bool where
  k := M.k + 1
  State := M.State ⊕ (Fin 4 ⊕ Option Bool)
  tm := {
    q₀ := .inl M.tm.q₀
    tr := fun q inp work => match q with
      | .inl s => captureAction Sum.inl (.inr (.inl 0))
          (M.tm.tr s inp fun i => work i.castSucc)
      | .inr (.inl q) => match q.val with
        | 0 => lenAction M 0 .neg none (some (.inr (.inl 1)))
        | 1 => controlAction .neg (some (.inr (.inl 2)))
        | 2 => match inp with
          | some _ => controlAction .neg (some (.inr (.inl 2)))
          | none => controlAction .pos (some (.inr (.inr none)))
        | _ => match inp with
          | none => lenAction M 0 0 (some true) none
          | some _ => match work (Fin.last M.k) with
            | none => lenAction M 0 0 (some false) none
            | some _ => lenAction M .pos .neg none (some (.inr (.inl 3)))
      | .inr (.inr none) => match inp with
        | none => lenAction M 0 0 (some false) none
        | some b => lenAction M .pos 0 none (some (.inr (.inr (some b))))
      | .inr (.inr (some b)) => match inp with
        | none => lenAction M 0 0 (some false) none
        | some d => if b = d then lenAction M .pos 0 none (some (.inr (.inr none)))
          else if b then lenAction M 0 0 (some false) none
          else lenAction M .pos 0 none (some (.inr (.inl 3))) }

/-- Checker configurations retain the completed generator bank and its
captured output; `r` is the number of still available countdown cells. -/
private def lenCfg (M : FinTM Bool) {x : List Bool} (c : Cfg M.k Bool M.State x)
    (q : Option (pairCountTM M).State) (i : ℕ) (hi : i ≤ x.length) (r : ℕ) :
    Cfg (M.k + 1) Bool (pairCountTM M).State x :=
  { captureCfg (fun s : M.State => (Sum.inl s : (pairCountTM M).State))
      (.inr (.inl 0)) [] [] c with
    state := q
    inputPos := ⟨i + 1, by omega⟩
    workTapePos := fun j => if h : j.val < M.k then c.workTapePos ⟨j, h⟩
      else (r : ℤ) - 1 }

/-- The checker's input read is independent of the saved generator bank. -/
private lemma lenCfg_read (M : FinTM Bool) {x : List Bool} (c : Cfg M.k Bool M.State x)
    (q : Option (pairCountTM M).State) (i : ℕ) (hi : i ≤ x.length) (r : ℕ) :
    (lenCfg M c q i hi r).inputSymbol = x[i]? :=
  inputSymbol_at _ i hi rfl

/-- A stationary or forward administrative action preserves all work tapes;
its last-head movement subtracts one precisely when consuming a cell. -/
private lemma lenAction_apply (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (q q' : Option (pairCountTM M).State)
    (i j r s : ℕ) (hi : i ≤ x.length) (hj : j ≤ x.length)
    (m d : SignType) (b : Option Bool)
    (hm : moveInputPos (⟨i + 1, by omega⟩ : Fin (x.length + 2)) m = ⟨j + 1, by omega⟩)
    (hd : (r : ℤ) - 1 + d.cast = (s : ℤ) - 1) :
    (lenAction M m d b q').apply (lenCfg M c q i hi r) =
      {lenCfg M c q' j hj s with output := b.toList} := by
  refine Cfg.ext rfl hm ?_ ?_ rfl
  · rfl
  · funext k
    by_cases hk : k.val < M.k
    · simp [lenAction, lenCfg, Action.apply, hk]
    · simpa [lenAction, lenCfg, Action.apply, hk] using hd

/-- Suffix comparison consumes one captured cell per input bit and emits one
verdict at termination. Empty suffixes succeed even with an empty counter.
**Proof sketch.** Induct on the suffix. A zero counter rejects a nonempty
suffix immediately; otherwise one silent step decrements both lengths. -/
private lemma lenSuffix_run (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (rest : List Bool) :
    ∀ pre (hx : x = pre ++ rest) r, r ≤ c.output.length →
    ∃ t ≤ rest.length + 1,
      ((pairCountTM M).tm.runFrom
        (lenCfg M c (some (.inr (.inl 3))) pre.length (by simp [hx]) r) t).state = none ∧
      ((pairCountTM M).tm.runFrom
        (lenCfg M c (some (.inr (.inl 3))) pre.length (by simp [hx]) r) t).output =
          [decide (rest.length ≤ r)] := by
  induction rest with
  | nil =>
    intro pre hx r hr
    refine ⟨1, by simp, ?_⟩
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change (((pairCountTM M).tm.tr (.inr (.inl 3)) _ _).apply _).state = none ∧ _
    rw [lenCfg_read]
    simp [hx, pairCountTM, lenAction, lenCfg, captureCfg, Action.apply]
  | cons b rest ih =>
    intro pre hx r hr
    cases r with
    | zero =>
      refine ⟨1, by simp, ?_⟩
      simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
      unfold MultiTapeTM.step
      change (((pairCountTM M).tm.tr (.inr (.inl 3)) _ _).apply _).state = none ∧ _
      rw [lenCfg_read]
      simp [hx, pairCountTM, lenAction, lenCfg, captureCfg, Cfg.workTapeSymbols,
        bufferTape_left, Action.apply]
    | succ r =>
      have hs : (pairCountTM M).tm.step
          (lenCfg M c (some (.inr (.inl 3))) pre.length (by simp [hx]) (r + 1)) =
          lenCfg M c (some (.inr (.inl 3))) (pre.length + 1) (by simp [hx]) r := by
        unfold MultiTapeTM.step
        change ((pairCountTM M).tm.tr (.inr (.inl 3)) _ _).apply _ = _
        rw [lenCfg_read]
        have hin : x[pre.length]? = some b := by simp [hx]
        have hw : (lenCfg M c (some (.inr (.inl 3))) pre.length
            (by simp [hx]) (r + 1)).workTapeSymbols (Fin.last M.k) =
              some (c.output[r]'(by omega)) := by
          simp [lenCfg, captureCfg, Cfg.workTapeSymbols, bufferTape,
            List.getElem?_eq_getElem (by omega : r < c.output.length)]
        simp only [pairCountTM, hin, hw]
        exact lenAction_apply M c _ _ pre.length (pre.length + 1) (r + 1) r
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
private lemma lenParse_first (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (pre rest : List Bool) (b : Bool) (r : ℕ)
    (hx : x = pre ++ b :: rest) :
    (pairCountTM M).tm.step
      (lenCfg M c (some (.inr (.inr none))) pre.length (by simp [hx]) r) =
      lenCfg M c (some (.inr (.inr (some b)))) (pre.length + 1) (by simp [hx]) r := by
  unfold MultiTapeTM.step
  change ((pairCountTM M).tm.tr (.inr (.inr none)) _ _).apply _ = _
  rw [lenCfg_read]
  have hin : x[pre.length]? = some b := by simp [hx]
  simp only [pairCountTM, hin]
  exact lenAction_apply M c _ _ pre.length (pre.length + 1) r r
    (by simp [hx]) (by simp [hx]) .pos 0 none
    (moveInputPos_pos_of_ne_right _ (by simp [hx])) (by simp [SignType.cast])

/-- Two parser steps either advance over a doubled bit, enter the suffix
comparison at `01`, or reject `10`. Nothing is emitted on a valid block. -/
private lemma lenParse_block (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (pre rest : List Bool) (b d : Bool) (r : ℕ)
    (hx : x = pre ++ b :: d :: rest) :
    (pairCountTM M).tm.runFrom
      (lenCfg M c (some (.inr (.inr none))) pre.length (by simp [hx]) r) 2 =
      if b = d then lenCfg M c (some (.inr (.inr none)))
          (pre.length + 2) (by simp [hx]) r
      else if b then {lenCfg M c none (pre.length + 1) (by simp [hx]) r with output := [false]}
      else lenCfg M c (some (.inr (.inl 3))) (pre.length + 2) (by simp [hx]) r := by
  change (pairCountTM M).tm.step ((pairCountTM M).tm.step _) = _
  rw [lenParse_first M c pre (d :: rest) b r hx]
  unfold MultiTapeTM.step
  change ((pairCountTM M).tm.tr (.inr (.inr (some b))) _ _).apply _ = _
  rw [lenCfg_read]
  have hin : x[pre.length + 1]? = some d := by simp [hx]
  rw [hin]
  have hm : moveInputPos (⟨pre.length + 1 + 1, by simp [hx]⟩ : Fin (x.length + 2)) .pos =
      ⟨pre.length + 2 + 1, by simp [hx]; omega⟩ :=
    moveInputPos_pos_of_ne_right _ (by simp [hx])
  cases b <;> cases d <;>
    simp only [pairCountTM, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
  all_goals first
    | exact lenAction_apply M c _ _ (pre.length + 1) (pre.length + 2) r r
        (by simp [hx]) (by simp [hx]) .pos 0 none hm (by simp [SignType.cast])
    | exact lenAction_apply M c _ _ (pre.length + 1) (pre.length + 1) r r
        (by simp [hx]) (by simp [hx]) 0 0 (some false)
        (moveInputPos_zero _) (by simp [SignType.cast])

/-- Aligned validation followed by countdown comparison decides the payload
bound in at most one more than the unread input length.
**Proof sketch.** Induct over two-bit blocks, using the existing parser's
same grammar and induction pattern. Equal-bit blocks preserve the counter;
`01` invokes suffix comparison; malformed endings and `10` reject. -/
private lemma lenParse_run (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (rest : List Bool) :
    ∀ pre (hx : x = pre ++ rest) r, r ≤ c.output.length →
    ∃ t ≤ rest.length + 1,
      ((pairCountTM M).tm.runFrom
        (lenCfg M c (some (.inr (.inr none))) pre.length (by simp [hx]) r) t).state = none ∧
      ((pairCountTM M).tm.runFrom
        (lenCfg M c (some (.inr (.inr none))) pre.length (by simp [hx]) r) t).output =
          [match pairDecode rest with
            | some (_, b) => decide (b.length ≤ r)
            | none => false] := by
  induction rest using List.twoStepInduction with
  | nil =>
    intro pre hx r hr
    refine ⟨1, by simp, ?_⟩
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change (((pairCountTM M).tm.tr (.inr (.inr none)) _ _).apply _).state = none ∧ _
    rw [lenCfg_read]
    simp [hx, pairCountTM, lenAction, lenCfg, captureCfg, Action.apply, pairDecode]
  | singleton b =>
    intro pre hx r hr
    refine ⟨2, by simp, ?_⟩
    change ((pairCountTM M).tm.step ((pairCountTM M).tm.step _)).state = none ∧
      ((pairCountTM M).tm.step ((pairCountTM M).tm.step _)).output = _
    rw [lenParse_first M c pre [] b r hx]
    unfold MultiTapeTM.step
    change (((pairCountTM M).tm.tr (.inr (.inr (some b))) _ _).apply _).state = none ∧ _
    rw [lenCfg_read]
    cases b <;> simp [hx, pairCountTM, lenAction, lenCfg, captureCfg, Action.apply, pairDecode]
  | cons_cons b d rest ih _ =>
    intro pre hx r hr
    by_cases h : b = d
    · subst d
      obtain ⟨t, ht, hs, ho⟩ := ih (pre ++ [b, b])
        (by simpa [List.append_assoc] using hx) r hr
      refine ⟨2 + t, by simp only [List.length_cons] at *; omega, ?_⟩
      rw [MultiTapeTM.runFrom_add, lenParse_block M c pre rest b b r hx, if_pos rfl]
      simp only [List.length_append, List.length_cons, List.length_nil] at hs ho
      refine ⟨hs, ?_⟩
      cases b <;> cases hd : pairDecode rest with
        | none => simpa [pairDecode, hd] using ho
        | some p => cases p; simpa [pairDecode, hd] using ho
    · cases b <;> cases d
      · exact False.elim (h rfl)
      · obtain ⟨t, ht, hs, ho⟩ := lenSuffix_run M c rest (pre ++ [false, true])
          (by simpa [List.append_assoc] using hx) r hr
        refine ⟨2 + t, by simp only [List.length_cons]; omega, ?_⟩
        rw [MultiTapeTM.runFrom_add, lenParse_block M c pre rest false true r hx]
        simp only [Bool.false_eq_true, ↓reduceIte]
        simp only [List.length_append, List.length_cons, List.length_nil] at hs ho
        exact ⟨hs, by simpa [pairDecode] using ho⟩
      · refine ⟨2, by simp, ?_⟩
        rw [lenParse_block M c pre rest true false r hx]
        simp [lenCfg, pairDecode]
      · exact False.elim (h rfl)

/-- Quantitative input rewind, adapted from the wrapper controller's proved
`timed_rewind` pattern using the public `rewind_scan` interface.
**Proof sketch.** One mandatory left move is followed by exactly the new
position plus one scan steps. Work tapes and output are preserved. -/
private lemma catalogRewind {k : ℕ} {S : Type} {x : List Bool}
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
private lemma lenStart (M : FinTM Bool) (x w : List Bool) (T : ℕ)
    (hM : M.ComputesInTime x w T) :
    ∃ t ≤ T + x.length + 4, ∃ c : Cfg M.k Bool M.State x,
      c.output = w ∧
      (pairCountTM M).tm.runFrom ((pairCountTM M).tm.initCfg x) t =
        lenCfg M c (some (.inr (.inr none))) 0 (by omega) c.output.length := by
  classical
  have hh : ∃ t, (M.tm.runFrom (M.tm.initCfg x) t).state = none :=
    ⟨T, ((computesInTime_iff _ _ _ _).mp hM).1⟩
  let t := Nat.find hh
  let c := M.tm.runFrom (M.tm.initCfg x) t
  have ht : t ≤ T := Nat.find_min' hh ((computesInTime_iff _ _ _ _).mp hM).1
  have hs : c.state = none := Nat.find_spec hh
  have hc : M.ComputesInTime x c.output t := (computesInTime_iff _ _ _ _).mpr ⟨hs, rfl⟩
  have ho : c.output = w := hc.output_unique hM
  let emb : M.State → (pairCountTM M).State := Sum.inl
  let ret : (pairCountTM M).State := .inr (.inl 0)
  have hinit : (pairCountTM M).tm.initCfg x = captureCfg emb ret [] [] (M.tm.initCfg x) := by
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    · funext i; simp [captureCfg, MultiTapeTM.initCfg, Cfg.init]
    · funext i; simp [captureCfg, MultiTapeTM.initCfg, Cfg.init]
  have hcap : (pairCountTM M).tm.runFrom ((pairCountTM M).tm.initCfg x) t =
      captureCfg emb ret [] [] c := by
    rw [hinit]
    exact capture_run M.tm (pairCountTM M).tm emb ret (fun _ _ _ => rfl)
      [] [] _ t (fun s hst => Nat.find_min hh hst)
  let ready : Cfg (M.k + 1) Bool (pairCountTM M).State x :=
    {lenCfg M c (some (.inr (.inl 1))) 0 (by omega) c.output.length with
      inputPos := c.inputPos}
  have hback : (pairCountTM M).tm.step (captureCfg emb ret [] [] c) = ready := by
    have hstate : (captureCfg emb ret [] [] c).state = some ret := by simp [captureCfg, hs]
    simp only [MultiTapeTM.step, hstate]
    apply Cfg.ext
    · rfl
    · exact moveInputPos_zero _
    · rfl
    · funext i
      by_cases hi : i.val < M.k <;>
        simp [pairCountTM, ret, lenAction, Action.apply, captureCfg, ready, lenCfg, hi,
          sub_eq_add_neg]
    · rfl
  obtain ⟨r, hrle, hr⟩ := catalogRewind (pairCountTM M).tm
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
private lemma pairCount_computes {M : FinTM Bool} {g : List Bool → List Bool}
    {T : ℕ → ℕ} (hM : M.ComputesFunInTime g T) :
    (pairCountTM M).ComputesFunInTime
      (fun x => [match pairDecode x with
        | some (_, b) => decide (b.length ≤ (g x).length)
        | none => false]) (fun n => T n + 2 * n + 5) := by
  intro x
  obtain ⟨t, ht, c, ho, hstart⟩ := lenStart M x (g x) (T x.length) (hM x)
  obtain ⟨r, hr, hs, hout⟩ := lenParse_run M c x [] rfl c.output.length (le_refl _)
  have hc : (pairCountTM M).ComputesInTime x
      [match pairDecode x with
        | some (_, b) => decide (b.length ≤ (g x).length)
        | none => false] (t + r) := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_add, hstart]
    exact ⟨hs, by simpa only [ho] using hout⟩
  exact hc.mono (by dsimp only; omega)

/-- Copy the physical input, erase its final false-run and last true, rewind,
then replay. An all-false input halts silently during the reverse scan. -/
private def rawStripTM : FinTM Bool where
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
private def stripCfg (x : List Bool) (q : Option (Fin 4)) (i : ℕ) (hi : i ≤ x.length)
    (w : List Bool) (h : ℤ) (out : List Bool) : Cfg 1 Bool (Fin 4) x :=
  ⟨q, ⟨i + 1, by omega⟩, fun _ => bufferTape w, fun _ => h, out⟩

/-- Erasing the last written cell restores exactly the shorter buffer. -/
private lemma catalogBuffer_erase (w : List Bool) (b : Bool) :
    Function.update (bufferTape (w ++ [b])) (w.length : ℤ) none = bufferTape w := by
  rw [bufferTape_append, Function.update_idem]
  funext z
  by_cases hz : z = (w.length : ℤ)
  · subst z; simp
  · simp [Function.update_of_ne hz]

/-- The forward copy is silent and installs exactly the scanned input prefix.
**Proof sketch.** One input step appends the next bit at the buffer's right
blank; the input and work heads both advance once. -/
private lemma rawStrip_copy (x : List Bool) : ∀ j (hj : j ≤ x.length),
    rawStripTM.tm.runFrom (rawStripTM.tm.initCfg x) j =
      stripCfg x (some 0) j hj (x.take j) j [] := by
  intro j
  induction j with
  | zero => intro hj; apply Cfg.ext <;> simp [rawStripTM, stripCfg]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hin : (stripCfg x (some 0) j (by omega) (x.take j) j []).inputSymbol =
        some (x[j]'(by omega)) := inputSymbolInner j (by simp [stripCfg]; omega) (by omega)
    unfold MultiTapeTM.step
    change (rawStripTM.tm.tr (0 : Fin 4) _ _).apply _ = _
    rw [hin]
    refine Cfg.ext rfl (moveInputPos_pos_of_ne_right _ (by simp [stripCfg]; omega)) ?_ ?_ rfl
    · funext k
      change Function.update (bufferTape (x.take j)) (j : ℤ) (some (x[j]'(by omega))) =
        bufferTape (x.take (j + 1))
      rw [List.take_succ, List.getElem?_eq_getElem (by omega)]
      simpa only [List.length_take, Nat.min_eq_left (by omega : j ≤ x.length)] using
        (bufferTape_append (x.take j) (x[j]'(by omega))).symm
    · funext k; simp [rawStripTM, stripCfg, Action.apply]

/-- Rewinding the validated buffer from cell `j-1` takes `j+1` transitions.
**Proof sketch.** At the left blank, move right and enter replay. Otherwise
read a buffer cell, move left, and invoke the induction hypothesis. -/
private lemma rawStrip_rewind (x a : List Bool)
    (i : ℕ) (hi : i ≤ x.length) : ∀ j, j ≤ a.length →
    rawStripTM.tm.runFrom
      (stripCfg x (some 2) i hi a ((j : ℤ) - 1) []) (j + 1) =
      stripCfg x (some 3) i hi a 0 [] := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    simp only [rawStripTM, stripCfg, Cfg.workTapeSymbols, Nat.cast_zero,
      zero_sub, bufferTape_left]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext k; simp [Action.apply]
  | succ j ih =>
    intro hj
    have hs : rawStripTM.tm.step
        (stripCfg x (some 2) i hi a (((j + 1 : ℕ) : ℤ) - 1) []) =
        stripCfg x (some 2) i hi a ((j : ℤ) - 1) [] := by
      have hz : (((j + 1 : ℕ) : ℤ) - 1) = j := by omega
      rw [hz]
      unfold MultiTapeTM.step
      simp only [rawStripTM, stripCfg, Cfg.workTapeSymbols, bufferTape_nat,
        List.getElem?_eq_getElem (by omega : j < a.length)]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext k; simp [Action.apply, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Replay appends exactly the visited buffer prefix and preserves its tape.
**Proof sketch.** The same replay invariant as the shared extractor: induct
on the number of visited cells and use the next-prefix equation for lists. -/
private lemma rawStrip_replay (x a : List Bool) (i : ℕ) (hi : i ≤ x.length) :
    ∀ j (_hj : j ≤ a.length),
    rawStripTM.tm.runFrom (stripCfg x (some 3) i hi a 0 []) j =
      stripCfg x (some 3) i hi a j (a.take j) := by
  intro j
  induction j with
  | zero => intro hj; rfl
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    unfold MultiTapeTM.step
    simp only [rawStripTM, stripCfg, Cfg.workTapeSymbols, bufferTape_nat,
      List.getElem?_eq_getElem (by omega : j < a.length)]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ ?_
    · funext k; simp [Action.apply]
    · change a.take j ++ [a[j]'(by omega)] = a.take (j + 1)
      rw [List.take_succ, List.getElem?_eq_getElem (by omega)]
      rfl

/-- Rewind followed by replay halts with exactly the retained buffer.
**Proof sketch.** The rewind costs `|a|+1`; replay and its final blank test
cost another `|a|+1`, and no earlier phase has emitted anything. -/
private lemma rawStrip_finish (x a : List Bool) (i : ℕ) (hi : i ≤ x.length) :
    (rawStripTM.tm.runFrom (stripCfg x (some 2) i hi a (a.length - 1) [])
      (2 * (a.length + 1))).state = none ∧
    (rawStripTM.tm.runFrom (stripCfg x (some 2) i hi a (a.length - 1) [])
      (2 * (a.length + 1))).output = a := by
  have htime : 2 * (a.length + 1) = (a.length + 1) + (a.length + 1) := by omega
  rw [htime, MultiTapeTM.runFrom_add, rawStrip_rewind x a i hi a.length (le_refl _),
    MultiTapeTM.runFrom_succ_eq_step', rawStrip_replay x a i hi a.length (le_refl _)]
  simp [MultiTapeTM.step, rawStripTM, stripCfg, Cfg.workTapeSymbols, Action.apply]

/-- The reverse phase erases the last cell and moves left, branching to
replay preparation precisely when the erased bit is true. -/
private lemma rawStrip_erase (x w : List Bool) (i : ℕ) (hi : i ≤ x.length) (b : Bool) :
    rawStripTM.tm.step
      (stripCfg x (some 1) i hi (w ++ [b]) ((w ++ [b]).length - 1) []) =
      stripCfg x (some (if b then 2 else 1)) i hi w (w.length - 1) [] := by
  have hz : (((w ++ [b]).length : ℕ) : ℤ) - 1 = w.length := by simp
  rw [hz]
  unfold MultiTapeTM.step
  simp only [stripCfg, rawStripTM, Cfg.workTapeSymbols, bufferTape_nat,
    List.getElem?_append_right (by omega : w.length ≤ w.length), Nat.sub_self,
    List.getElem?_cons_zero]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
  · funext k; exact catalogBuffer_erase w b
  · funext k; simp [Action.apply, sub_eq_add_neg]

/-- Reverse erasure implements `splitAtLastTrue` exactly, including rejection
of every all-false word.
**Proof sketch.** Induct from the right. A final false is erased and the
induction continues. A final true is erased and the retained prefix is
rewound and replayed. These are exactly the `reverse.dropWhile` equations. -/
private lemma rawStrip_trim (x w : List Bool) (i : ℕ) (hi : i ≤ x.length) :
    ∃ t ≤ 3 * (w.length + 1),
      (rawStripTM.tm.runFrom (stripCfg x (some 1) i hi w (w.length - 1) []) t).state = none ∧
      (rawStripTM.tm.runFrom (stripCfg x (some 1) i hi w (w.length - 1) []) t).output =
        (splitAtLastTrue w).getD [] := by
  induction w using List.reverseRecOn with
  | nil =>
    refine ⟨1, by simp, ?_⟩
    simp [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.step, rawStripTM, stripCfg,
      Cfg.workTapeSymbols, Action.apply, splitAtLastTrue]
  | append_singleton w b ih =>
    cases b with
    | false =>
      obtain ⟨t, ht, hs, ho⟩ := ih
      refine ⟨t + 1, by simp only [List.length_append, List.length_singleton]; omega, ?_⟩
      rw [MultiTapeTM.runFrom_succ_eq_step, rawStrip_erase]
      exact ⟨hs, by simpa [splitAtLastTrue] using ho⟩
    | true =>
      refine ⟨2 * (w.length + 1) + 1,
        by simp only [List.length_append, List.length_singleton]; omega, ?_⟩
      rw [MultiTapeTM.runFrom_succ_eq_step, rawStrip_erase]
      simpa [splitAtLastTrue] using rawStrip_finish x w i hi

/-- Raw marker stripping runs in linear time, with physical output delayed
until the last true has been located and removed.
**Proof sketch.** Copy in `|x|+1` steps, including the right-blank turn;
the reverse/replay ledger uses at most another `3(|x|+1)` steps. -/
private lemma rawStrip_computes : rawStripTM.ComputesFunInTime
    (fun x => (splitAtLastTrue x).getD []) (fun n => 4 * (n + 1)) := by
  intro x
  have hstart : rawStripTM.tm.runFrom (rawStripTM.tm.initCfg x) (x.length + 1) =
      stripCfg x (some 1) x.length (le_refl _) x (x.length - 1) [] := by
    rw [MultiTapeTM.runFrom_succ_eq_step', rawStrip_copy x x.length (le_refl _)]
    have hin : (stripCfg x (some 0) x.length (le_refl _) (x.take x.length) x.length []).inputSymbol =
        none := by simp [stripCfg, Cfg.inputSymbol]
    unfold MultiTapeTM.step
    change (rawStripTM.tm.tr (0 : Fin 4) _ _).apply _ = _
    rw [hin]
    apply Cfg.ext <;> simp [rawStripTM, stripCfg, Action.apply, sub_eq_add_neg]
  obtain ⟨t, ht, hs, ho⟩ := rawStrip_trim x x x.length (le_refl _)
  have hc : rawStripTM.ComputesInTime x ((splitAtLastTrue x).getD []) (x.length + 1 + t) := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_add, hstart]
    exact ⟨hs, ho⟩
  exact hc.mono (by dsimp only; omega)

/-- A finite scanner emits whether its input contains a true bit. -/
private def anyTrueTM : FinTM Bool where
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
private lemma anyTrue_run (x rest : List Bool) : ∀ pre (hx : x = pre ++ rest),
    ∃ t ≤ rest.length + 1,
      (anyTrueTM.tm.runFrom (scanCfg x (some ()) pre.length (by simp [hx]) []) t).state = none ∧
      (anyTrueTM.tm.runFrom (scanCfg x (some ()) pre.length (by simp [hx]) []) t).output =
        [rest.any id] := by
  induction rest with
  | nil =>
    intro pre hx
    refine ⟨1, by simp, ?_⟩
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change ((anyTrueTM.tm.tr () _ _).apply _).state = none ∧ _
    rw [scanCfg_read]
    simp [hx, anyTrueTM, Action.apply, scanCfg]
  | cons b rest ih =>
    intro pre hx
    cases b with
    | true =>
      refine ⟨1, by simp, ?_⟩
      simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
      unfold MultiTapeTM.step
      change ((anyTrueTM.tm.tr () _ _).apply _).state = none ∧ _
      rw [scanCfg_read]
      simp [hx, anyTrueTM, Action.apply, scanCfg]
    | false =>
      have hs := scanStep_right anyTrueTM.tm x () (some ()) pre.length (by simp [hx]) [] none
        (by intro work; simp [hx, anyTrueTM])
      obtain ⟨t, ht, hh, ho⟩ := ih (pre ++ [false]) (by simpa [List.append_assoc] using hx)
      refine ⟨t + 1, by simp only [List.length_cons]; omega, ?_⟩
      rw [MultiTapeTM.runFrom_succ_eq_step, hs]
      simpa using And.intro hh ho

/-- The true-bit scanner starts at the first input cell and uses a linear bound. -/
private lemma anyTrue_computes : anyTrueTM.ComputesFunInTime
    (fun x => [x.any id]) (fun n => n + 1) := by
  intro x
  obtain ⟨t, ht, hs, ho⟩ := anyTrue_run x x [] rfl
  have hinit : anyTrueTM.tm.initCfg x = scanCfg x (some ()) 0 (by omega) [] := by
    apply Cfg.ext_zero_tapes <;> rfl
  have hc : anyTrueTM.ComputesInTime x [x.any id] t := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [hinit]
    exact ⟨hs, ho⟩
  exact hc.mono ht

/-- A successful aligned parse reconstructs the input's exact encoding.
**Proof sketch.** Induct over two-bit blocks: equal bits prepend one decoded
bit; the separator exposes the entire remaining suffix. -/
private lemma catalogPair_inverse (x : List Bool) :
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

/-- Marker absence is exactly the false verdict; a present marker can be
stripped after any fixed prefix without disturbing that prefix.
**Proof sketch.** Right induction follows `reverse.dropWhile`: append-false
preserves the previous result, and append-true selects the whole old word. -/
private lemma catalogMarker_cases (v : List Bool) :
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

/-- The total suffix extractor never lengthens its input, including malformed
inputs, whose extracted suffix is empty. -/
private lemma catalogPayload_length (x : List Bool) :
    ((pairDecode x).map Prod.snd |>.getD []).length ≤ x.length := by
  cases hd : pairDecode x with
  | none => simp
  | some p =>
    rcases p with ⟨a, b⟩
    have hx := catalogPair_inverse x a b hd
    simp only [Option.map_some, Option.getD_some]
    rw [hx]
    simp only [pairEncode, List.length_append]
    omega

/-- Run the given machine on the parsed payload, using the public relocated
composition engine and the payload's actual length. This is the quantitative
continuation interface for the threaded map; it does not yet emit the retained
first component or capture the transformed payload for that emission.
**Proof sketch.** The proved extractor validates and buffers before emission.
`bufferedComp_start` installs its suffix as virtual input; `bufferedSecondCfg_run`
simulates the payload machine with `bufferTape`/`virtualMove`. Charge its time
to `Tg |x|` using the nonexpanding suffix bound, not the extractor's larger
running-time bound. This distinction is necessary for arbitrary monotone `Tg`. -/
private lemma catalogPayload_computes {Mg : FinTM Bool}
    {g : List Bool → List Bool} {Tg : ℕ → ℕ}
    (hg : Mg.ComputesFunInTime g Tg) (hTg : Monotone Tg) :
    (bufferedCompTM (pairExtractTM false true) Mg).ComputesFunInTime
      (fun x => g ((pairDecode x).map Prod.snd |>.getD []))
      (fun n => 6 * (n + 1) + Tg n + 1) := by
  intro x
  let y := (pairDecode x).map Prod.snd |>.getD []
  have hF : (pairExtractTM false true).ComputesInTime x y (5 * (x.length + 1)) := by
    have hf := pairExtract_computes false true x
    cases hd : pairDecode x with
    | none => simpa [y, hd] using hf
    | some p => cases p; simpa [y, hd] using hf
  have hlen : y.length ≤ x.length := catalogPayload_length x
  obtain ⟨a, p, tapes, heads, ha, hstart⟩ :=
    bufferedComp_start (pairExtractTM false true) Mg x y (5 * (x.length + 1)) hF
  obtain ⟨b, _, hr⟩ := bufferedSecondCfg_run (pairExtractTM false true) Mg (Mg.tm.initCfg y) true
    (by simp [VirtualTag, MultiTapeTM.initCfg, Cfg.init]) p tapes heads (Tg y.length)
  have hc := (computesInTime_iff _ _ _ _).mp (hg y)
  have hbase : (bufferedCompTM (pairExtractTM false true) Mg).ComputesInTime x (g y)
      (a + Tg y.length) := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_add, hstart, hr]
    exact ⟨by simpa only [bufferedSecondCfg, Option.map_eq_none_iff] using hc.1, hc.2⟩
  have htime : Tg y.length ≤ Tg x.length := hTg hlen
  exact hbase.mono (by dsimp only; omega)

/-- **P3, prepend a fixed word** (spec, fill pending — harvest: the HALT
batch's `prefixTM`/`prefixTM_computes`, whose promotion the batch formally
requested). Emitting the fixed word `w` and then copying the input is
computable in linear time; the constant may depend on `w`, which is fixed
before the machine.

**Construction sketch.** The fixed emission chain of
`Turing.FinTM.computesFunInTime_const` for `w`, then the one-state copy
scan of `Turing.FinTM.computesFunInTime_id`; the harvest source proves the
exact budget `|w| + |x| + 1`. -/
theorem computesFunInTime_prepend (w : List Bool) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => w ++ x) fun n => c * (n + 1) := by
  refine ⟨catalogPrefixTM w, w.length + 1, fun x => (catalogPrefixTM_computes w x).mono ?_⟩
  simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
  omega

/-- **P4, input length in binary** (spec, fill pending — new; the unary
scan is a one-state sweep and the binary counter discipline is the
`Turing.incFixed` carry loop). The little-endian binary representation
`Nat.bits` of the input length is computable in linear time.

**Construction sketch.** One left-to-right input scan driving an in-place
binary counter on a work tape (the `Turing.incFixed` carry discipline, cost
amortized constant per input cell), then emit the counter word. -/
theorem computesFunInTime_lengthBits :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => Nat.bits x.length) fun n => c * (n + 1) := by
  obtain ⟨_, c, _, M, hM⟩ := Complexity.timeConstructible_id
  exact ⟨M, c, hM⟩

/-- **P5, polynomial evaluation, unary clause** (spec, fill pending —
harvest: the TMSAT batch's `polyUnaryTM`/`poly_unary_computes`, proved with
budget `(C + 5(e+1) + 4)·(n+1)^(e+1)`). The exact unary value of
`C·(n+1)^e` at the input length is computable within a constant multiple of
`(n+1)^(e+1)`. Its instances are also the exact-emission primitive the
reduction constructions consume (catalog entry P7, subsumed here).

**Construction sketch** (indexing corrected per round-1 finding 5: the
harvest source's `poly_unary_computes` with loop parameter `c` emits
exponent `c + 1`, so this contract harvests with parameter `e - 1`): for
`e > 0`, `e` nested unary loop tapes of side length `n + 1`, installed by
one input scan, the innermost loop emitting `C` trues per box point —
exactly `C·(n+1)^e` in total; for `e = 0` the output is the constant
`List.replicate C true`, a fixed emission chain. A recursive invariant
restores completed inner heads, with loop depth `r` costing at most
`(C + 1 + 5r)·(n+1)^r`. -/
theorem computesFunInTime_polyUnary (C e : ℕ) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun x => List.replicate (C * (x.length + 1) ^ e) true)
        fun n => c * (n + 1) ^ (e + 1) := by
  cases e with
  | zero =>
    simpa using computesFunInTime_const (List.replicate C true)
  | succ d =>
    refine ⟨catalogPolyUnaryTM d C, C + 5 * (d + 1) + 4, fun x => ?_⟩
    apply (catalogPoly_unary_computes d C x).mono
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.succ_pos x.length) (by omega))

/-- **P5, polynomial evaluation, binary clause** (spec, fill pending —
harvest: the TMSAT batch's composition of the unary generator with the
binary length counter). The little-endian binary representation of
`C·(n+1)^e` at the input length is computable within a constant multiple
of `(n+1)^(e+1)`.

**Construction sketch.** The unary generator above composed with the
binary length counter of `computesFunInTime_lengthBits` through the public
buffered composition (`Turing.FinTM.computesFunInTime_comp`) — the harvest
source's exact route, under the same `e - 1` harvest-indexing convention
as the unary clause (round-1 finding 5). -/
theorem computesFunInTime_polyBits (C e : ℕ) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => Nat.bits (C * (x.length + 1) ^ e))
        fun n => c * (n + 1) ^ (e + 1) := by
  obtain ⟨U, a, hU⟩ := computesFunInTime_polyUnary C e
  obtain ⟨B, b, hB⟩ := computesFunInTime_lengthBits
  obtain ⟨M, d, hM⟩ := computesFunInTime_comp hU hB
    (by intro m n h; exact Nat.mul_le_mul_left b (Nat.add_le_add_right h 1))
  refine ⟨M, d * (a + 1) * (b + 1), fun x => ?_⟩
  have hm := hM x
  simp only [Function.comp_apply, List.length_replicate] at hm
  apply hm.mono
  let P := (x.length + 1) ^ (e + 1)
  have hp : 1 ≤ P := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hb : b + 1 ≤ (b + 1) * P := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (b + 1) hp
  have hbound : a * P + b * (a * P + 1) + 1 ≤ (a + 1) * (b + 1) * P := by
    calc
      _ = a * (b + 1) * P + (b + 1) := by ring
      _ ≤ a * (b + 1) * P + (b + 1) * P := Nat.add_le_add_left hb _
      _ = _ := by ring
  calc
    _ ≤ d * ((a + 1) * (b + 1) * P) := Nat.mul_le_mul_left d hbound
    _ = _ := by ring

/-- **P6, pairing with a fixed first component** (spec, fill pending —
harvest: the HALT batch's `fixedPair_computes`, proved with the exact
budget `2|α| + |x| + 3`; its promotion was formally requested). For a
fixed word `α`, the self-delimiting pairing `pairEncode α x` is computable
in linear time. This is the threading stage: downstream threaded contracts
receive `pairEncode a b` and act on `b` while carrying `a`.

**Construction sketch.** `pairEncode α x` is literally
`(α doubled) ++ [false, true] ++ x`, so this is the prepend primitive at
that fixed word; it is kept as its own contract because consumers cite the
pairing grammar, and the harvest source proves the exact budget
`2|α| + |x| + 3`. -/
theorem computesFunInTime_pairEncodeFixed (α : List Bool) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => pairEncode α x) fun n => c * (n + 1) := by
  simpa only [pairEncode] using
    computesFunInTime_prepend ((α.flatMap fun b => [b, b]) ++ [false, true])

/-- **P6, first-component extraction** (spec, fill pending — new; the
aligned two-bit scan of the `Turing.pairDecode` grammar as a machine). On
a well-formed pair the doubled prefix is undoubled and emitted; on a
malformed input the output is `[]`.

**Construction sketch.** Output is append-only, so the scan must not emit
before the parse succeeds: undouble aligned `00`/`11` blocks onto a work
tape until the aligned `01` separator, then replay the buffer to the
output; any misaligned block halts with nothing emitted. -/
theorem computesFunInTime_pairFst :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => ((pairDecode x).map Prod.fst).getD [])
        fun n => c * (n + 1) := by
  refine ⟨pairExtractTM true false, 5, fun x => ?_⟩
  have h := pairExtract_computes true false x
  cases hd : pairDecode x with
  | none => simpa [hd] using h
  | some p => cases p; simpa [hd] using h

/-- **P6, second-component extraction** (spec, fill pending — new; the
same aligned scan, emitting the suffix after the separator instead). On a
malformed input the output is `[]`. Iterating this extractor is how the
nested-quadruple parsers of the TMSAT constructions decompose.

**Construction sketch.** Scan aligned blocks without emitting until the
separator is found (validity of the prefix must be known before any suffix
bit may be emitted), then copy the suffix verbatim; a misaligned block
halts silently. -/
theorem computesFunInTime_pairSnd :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => ((pairDecode x).map Prod.snd).getD [])
        fun n => c * (n + 1) := by
  refine ⟨pairExtractTM false true, 5, fun x => ?_⟩
  have h := pairExtract_computes false true x
  cases hd : pairDecode x with
  | none => simpa [hd] using h
  | some p => cases p; simpa [hd] using h

/-- **P6, grammar validity** (spec, fill pending — new). The single-bit
test for membership in the `Turing.pairDecode` grammar, the guard stage
every parser pipeline rejects malformed inputs with.

**Construction sketch.** One aligned two-bit scan in finite control; emit
the single verdict bit at the separator or at the first misaligned block.
No buffering is needed — only one bit is ever emitted, at the end. -/
theorem computesFunInTime_pairValid :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => [(pairDecode x).isSome])
        fun n => c * (n + 1) := by
  exact ⟨pairValidTM, 1, fun x => by simpa using pairValid_computes x⟩

/-- **P13, pair to concatenation** (spec, fill pending; round-2 addition
per round-1 finding 3 — the D-WRAP obligation's exact shape). On
`pairEncode x u`, emit `x ++ u`; malformed inputs yield `[]`, the threaded
rejection the downstream guard reads (the reduction wrapper's own
`[false]` rejection is assembled at the decider stage).

**Construction sketch.** Undouble the aligned prefix onto a work tape —
nothing emitted while validity is unknown; at the aligned separator,
replay the buffered first component and then copy the suffix verbatim; a
misaligned block halts with nothing emitted. -/
theorem computesFunInTime_pairConcat :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun z => match pairDecode z with
          | some (a, b) => a ++ b
          | none => [])
        fun n => c * (n + 1) := by
  refine ⟨pairExtractTM true true, 5, fun x => ?_⟩
  have h := pairExtract_computes true true x
  cases hd : pairDecode x with
  | none => simpa [hd] using h
  | some p => cases p; simpa [hd] using h

/-- **P14, duplication into a pair** (spec, fill pending; round-2 addition
per round-1 finding 3 — the entry stage of data-retaining pipelines:
the reduction emitter retains `x` while its duplicate feeds the generated
components). Emit `pairEncode x x`.

**Construction sketch.** Two input passes: emit each read bit doubled,
then the separator, then copy the input verbatim. No buffering is needed
— the pairing prefix is valid bit by bit, and every input is legal. -/
theorem computesFunInTime_pairDup :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => pairEncode x x) fun n => c * (n + 1) := by
  exact ⟨pairDupTM, 4, pairDup_computes⟩

/-- The threaded-map controller uses the last tape only for captured output;
all administrative actions preserve its contents and the source bank. -/
private def mapAction (M : FinTM Bool) (m d : SignType) (b : Option Bool)
    (q : Option (M.State ⊕ (Fin 7 ⊕ (Bool × Option Bool)))) :
    Action (M.k + 1) Bool (M.State ⊕ (Fin 7 ⊕ (Bool × Option Bool))) :=
  ⟨m, fun i => (none, if i.val < M.k then 0 else d), b, q⟩

/-- Capture the payload computation, rewind both relevant heads, and silently
validate the original pair. Only after validation, replay the native encoded
prefix followed by the captured payload. The source bank is never reused. -/
private def pairMapTM (M : FinTM Bool) : FinTM Bool where
  k := M.k + 1
  State := M.State ⊕ (Fin 7 ⊕ (Bool × Option Bool))
  tm := {
    q₀ := .inl M.tm.q₀
    tr := fun q inp work => match q with
      | .inl s => captureAction Sum.inl (.inr (.inl 0))
          (M.tm.tr s inp fun i => work i.castSucc)
      | .inr (.inl q) => match q.val with
        | 0 => mapAction M 0 .neg none (some (.inr (.inl 1)))
        | 1 => match work (Fin.last M.k) with
          | some _ => mapAction M 0 .neg none (some (.inr (.inl 1)))
          | none => mapAction M 0 .pos none (some (.inr (.inl 2)))
        | 2 => controlAction .neg (some (.inr (.inl 3)))
        | 3 => match inp with
          | some _ => controlAction .neg (some (.inr (.inl 3)))
          | none => controlAction .pos (some (.inr (.inr (false, none))))
        | 4 => controlAction .neg (some (.inr (.inl 5)))
        | 5 => match inp with
          | some _ => controlAction .neg (some (.inr (.inl 5)))
          | none => controlAction .pos (some (.inr (.inr (true, none))))
        | _ => match work (Fin.last M.k) with
          | some b => mapAction M 0 .pos (some b) (some (.inr (.inl 6)))
          | none => mapAction M 0 0 none none
      | .inr (.inr (emit, none)) => match inp with
        | none => mapAction M 0 0 none none
        | some b => mapAction M .pos 0 (if emit then some b else none)
            (some (.inr (.inr (emit, some b))))
      | .inr (.inr (emit, some b)) => match inp with
        | none => mapAction M 0 0 none none
        | some d => mapAction M .pos 0 (if emit then some d else none)
            (if b = d then some (.inr (.inr (emit, none)))
             else if b then none
             else some (.inr (.inl (if emit then 6 else 4)))) }

/-- An administrative configuration preserves the completed source bank and
captured word, while exposing the input and capture-head positions. -/
private def mapCfg (M : FinTM Bool) {x : List Bool} (c : Cfg M.k Bool M.State x)
    (q : Option (pairMapTM M).State) (p : Fin (x.length + 2)) (h : ℤ)
    (out : List Bool) : Cfg (M.k + 1) Bool (pairMapTM M).State x :=
  { captureCfg (fun s : M.State => (Sum.inl s : (pairMapTM M).State))
      (.inr (.inl 0)) [] out c with
    state := q
    inputPos := p
    workTapePos := fun j => if hj : j.val < M.k then c.workTapePos ⟨j, hj⟩ else h }

/-- Administrative steps change only the named heads, control, and optional
output. No work-tape cell is written. -/
private lemma mapAction_apply (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (q q' : Option (pairMapTM M).State)
    (p : Fin (x.length + 2)) (h : ℤ) (out : List Bool)
    (m d : SignType) (b : Option Bool) :
    (mapAction M m d b q').apply (mapCfg M c q p h out) =
      mapCfg M c q' (moveInputPos p m) (h + d.cast) (out ++ b.toList) := by
  refine Cfg.ext rfl rfl rfl ?_ rfl
  funext j
  by_cases hj : j.val < M.k <;> simp [mapAction, mapCfg, Action.apply, hj]

/-- Rewinding the captured word from its final cell costs its length plus one.
**Proof sketch.** At the left blank, move right to the input-rewind phase.
Otherwise a single silent left step reduces the remaining prefix length. -/
private lemma mapBuffer_rewind (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (p : Fin (x.length + 2)) :
    ∀ j, j ≤ c.output.length →
    (pairMapTM M).tm.runFrom
      (mapCfg M c (some (.inr (.inl 1))) p ((j : ℤ) - 1) []) (j + 1) =
      mapCfg M c (some (.inr (.inl 2))) p 0 [] := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    simp only [pairMapTM, mapCfg, captureCfg, Cfg.workTapeSymbols, Fin.val_last,
      Nat.lt_irrefl, ↓reduceDIte, Nat.cast_zero, zero_sub, List.nil_append, bufferTape_left]
    apply Cfg.ext
    · rfl
    · exact moveInputPos_zero _
    · rfl
    · funext i; by_cases hi : i.val < M.k <;> simp [mapAction, Action.apply, hi]
    · rfl
  | succ j ih =>
    intro hj
    have hs : (pairMapTM M).tm.step
        (mapCfg M c (some (.inr (.inl 1))) p (((j + 1 : ℕ) : ℤ) - 1) []) =
        mapCfg M c (some (.inr (.inl 1))) p ((j : ℤ) - 1) [] := by
      have hz : (((j + 1 : ℕ) : ℤ) - 1) = j := by omega
      rw [hz]
      unfold MultiTapeTM.step
      change ((pairMapTM M).tm.tr (.inr (.inl 1)) _ _).apply _ = _
      have hw : (mapCfg M c (some (.inr (.inl 1))) p j []).workTapeSymbols
          (Fin.last M.k) = some (c.output[j]'(by omega)) := by
        simp [mapCfg, captureCfg, Cfg.workTapeSymbols,
          List.getElem?_eq_getElem (by omega : j < c.output.length)]
      simp only [pairMapTM, hw]
      rw [mapAction_apply]
      simp [SignType.cast, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Capture and rewind reach the silent validator with physical output empty.
**Proof sketch.** The least source halt supplies the capture guard. Rewind the
captured word, then the input, preserving every completed source tape. -/
private lemma mapStart (M : FinTM Bool) (x w : List Bool) (T : ℕ)
    (hM : M.ComputesInTime x w T) :
    ∃ t ≤ T + w.length + x.length + 5, ∃ c : Cfg M.k Bool M.State x,
      c.output = w ∧
      (pairMapTM M).tm.runFrom ((pairMapTM M).tm.initCfg x) t =
        mapCfg M c (some (.inr (.inr (false, none)))) 1 0 [] := by
  classical
  have hh : ∃ t, (M.tm.runFrom (M.tm.initCfg x) t).state = none :=
    ⟨T, ((computesInTime_iff _ _ _ _).mp hM).1⟩
  let t := Nat.find hh
  let c := M.tm.runFrom (M.tm.initCfg x) t
  have ht : t ≤ T := Nat.find_min' hh ((computesInTime_iff _ _ _ _).mp hM).1
  have hs : c.state = none := Nat.find_spec hh
  have hc : M.ComputesInTime x c.output t := (computesInTime_iff _ _ _ _).mpr ⟨hs, rfl⟩
  have ho : c.output = w := hc.output_unique hM
  let emb : M.State → (pairMapTM M).State := Sum.inl
  let ret : (pairMapTM M).State := .inr (.inl 0)
  have hinit : (pairMapTM M).tm.initCfg x = captureCfg emb ret [] [] (M.tm.initCfg x) := by
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    · funext i; simp [captureCfg, MultiTapeTM.initCfg, Cfg.init]
    · funext i; simp [captureCfg, MultiTapeTM.initCfg, Cfg.init]
  have hcap : (pairMapTM M).tm.runFrom ((pairMapTM M).tm.initCfg x) t =
      captureCfg emb ret [] [] c := by
    rw [hinit]
    exact capture_run M.tm (pairMapTM M).tm emb ret (fun _ _ _ => rfl)
      [] [] _ t (fun s hst => Nat.find_min hh hst)
  have hback : (pairMapTM M).tm.step (captureCfg emb ret [] [] c) =
      mapCfg M c (some (.inr (.inl 1))) c.inputPos (c.output.length - 1) [] := by
    have hstate : (captureCfg emb ret [] [] c).state = some ret := by simp [captureCfg, hs]
    simp only [MultiTapeTM.step, hstate]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext i
    by_cases hi : i.val < M.k <;>
      simp [pairMapTM, ret, mapAction, Action.apply, captureCfg, mapCfg, hi, sub_eq_add_neg]
  obtain ⟨r, hrle, hr⟩ := catalogRewind (pairMapTM M).tm
    (.inr (.inl 2)) (.inr (.inl 3)) (some (.inr (.inr (false, none))))
    (fun _ _ => rfl) (fun inp _ => by cases inp <;> rfl)
    (mapCfg M c (some (.inr (.inl 2))) c.inputPos 0 []) rfl
  have hlen : c.output.length = w.length := congrArg List.length ho
  have hfirst : (pairMapTM M).tm.runFrom ((pairMapTM M).tm.initCfg x) (t + 1) =
      mapCfg M c (some (.inr (.inl 1))) c.inputPos (c.output.length - 1) [] := by
    rw [MultiTapeTM.runFrom_succ_eq_step', hcap, hback]
  refine ⟨t + 1 + (c.output.length + 1) + r, ?_, c, ho, ?_⟩
  · change r ≤ c.inputPos.val + 2 at hrle
    have := c.inputPos.isLt
    omega
  · rw [MultiTapeTM.runFrom_add _ _ r,
      MultiTapeTM.runFrom_add _ (t + 1) (c.output.length + 1), hfirst,
      mapBuffer_rewind M c c.inputPos c.output.length (le_refl _), hr]
    rfl

/-- The parser and prefix-replay phases read the indexed native input cell. -/
private lemma mapCfg_read (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (q : Option (pairMapTM M).State)
    (i : ℕ) (hi : i ≤ x.length) (h : ℤ) (out : List Bool) :
    (mapCfg M c q ⟨i + 1, by omega⟩ h out).inputSymbol = x[i]? :=
  inputSymbol_at _ i hi rfl

/-- One aligned-block read remembers its first bit. Only the replay phase
emits it; the validator remains silent. -/
private lemma mapParse_first (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (pre rest out : List Bool) (b emit : Bool)
    (hx : x = pre ++ b :: rest) :
    (pairMapTM M).tm.step
      (mapCfg M c (some (.inr (.inr (emit, none)))) ⟨pre.length + 1, by simp [hx] <;> omega⟩ 0 out) =
      mapCfg M c (some (.inr (.inr (emit, some b))))
        ⟨pre.length + 2, by simp [hx] <;> omega⟩ 0 (out ++ if emit then [b] else []) := by
  unfold MultiTapeTM.step
  change ((pairMapTM M).tm.tr (.inr (.inr (emit, none))) _ _).apply _ = _
  rw [mapCfg_read M c _ pre.length (by simp [hx])]
  have hin : x[pre.length]? = some b := by simp [hx]
  simp only [pairMapTM, hin]
  rw [mapAction_apply, moveInputPos_pos_of_ne_right _ (by simp [hx] <;> omega)]
  cases emit <;> rfl

/-- A two-bit block either continues parsing, rejects `10`, or selects the
post-separator phase. The captured payload and its origin head are preserved. -/
private lemma mapParse_block (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (pre rest out : List Bool) (b d emit : Bool)
    (hx : x = pre ++ b :: d :: rest) :
    (pairMapTM M).tm.runFrom
      (mapCfg M c (some (.inr (.inr (emit, none))))
        ⟨pre.length + 1, by simp [hx] <;> omega⟩ 0 out) 2 =
      mapCfg M c
        (if b = d then some (.inr (.inr (emit, none))) else if b then none
          else some (.inr (.inl (if emit then 6 else 4))))
        ⟨pre.length + 3, by simp [hx] <;> omega⟩ 0 (out ++ if emit then [b, d] else []) := by
  change (pairMapTM M).tm.step ((pairMapTM M).tm.step _) = _
  rw [mapParse_first M c pre (d :: rest) out b emit hx]
  unfold MultiTapeTM.step
  change ((pairMapTM M).tm.tr (.inr (.inr (emit, some b))) _ _).apply _ = _
  rw [mapCfg_read M c _ (pre.length + 1) (by simp [hx])]
  have hin : x[pre.length + 1]? = some d := by simp [hx]
  simp only [pairMapTM, hin]
  rw [mapAction_apply, moveInputPos_pos_of_ne_right _ (by simp [hx] <;> omega)]
  cases emit <;> simp [SignType.cast, List.append_assoc]

/-- The silent aligned validator either halts without output or reaches the
input-rewind seam. Its total cost is at most the unread length plus one.
**Proof sketch.** Induction over aligned two-bit blocks. Equal bits recurse,
`01` validates, and `10`, a missing separator, or an incomplete block rejects. -/
private lemma mapValidate (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (rest : List Bool) :
    ∀ pre (hx : x = pre ++ rest), ∃ t ≤ rest.length + 1,
      if (pairDecode rest).isSome then
        ∃ p, (pairMapTM M).tm.runFrom
          (mapCfg M c (some (.inr (.inr (false, none))))
            ⟨pre.length + 1, by simp [hx] <;> omega⟩ 0 []) t =
          mapCfg M c (some (.inr (.inl 4))) p 0 []
      else
        ((pairMapTM M).tm.runFrom
          (mapCfg M c (some (.inr (.inr (false, none))))
            ⟨pre.length + 1, by simp [hx] <;> omega⟩ 0 []) t).state = none ∧
        ((pairMapTM M).tm.runFrom
          (mapCfg M c (some (.inr (.inr (false, none))))
            ⟨pre.length + 1, by simp [hx] <;> omega⟩ 0 []) t).output = [] := by
  induction rest using List.twoStepInduction with
  | nil =>
    intro pre hx
    refine ⟨1, by simp, ?_⟩
    simp only [pairDecode, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
      MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change (((pairMapTM M).tm.tr (.inr (.inr (false, none))) _ _).apply _).state = none ∧ _
    rw [mapCfg_read M c _ pre.length (by simp [hx])]
    simp [hx, pairMapTM, mapAction, Action.apply, mapCfg, captureCfg]
  | singleton b =>
    intro pre hx
    refine ⟨2, by simp, ?_⟩
    have hd : pairDecode [b] = none := by cases b <;> rfl
    simp only [hd, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    rw [mapParse_first M c pre [] [] b false hx]
    unfold MultiTapeTM.step
    change (((pairMapTM M).tm.tr (.inr (.inr (false, some b))) _ _).apply _).state = none ∧ _
    rw [mapCfg_read M c _ (pre.length + 1) (by simp [hx])]
    simp [hx, pairMapTM, mapAction, Action.apply, mapCfg, captureCfg]
  | cons_cons b d rest ih _ =>
    intro pre hx
    by_cases h : b = d
    · subst d
      obtain ⟨t, ht, hh⟩ := ih (pre ++ [b, b]) (by simpa [List.append_assoc] using hx)
      refine ⟨2 + t, by simp only [List.length_cons]; omega, ?_⟩
      rw [MultiTapeTM.runFrom_add, mapParse_block M c pre rest [] b b false hx]
      simp only [↓reduceIte, List.append_nil]
      have hp : (pairDecode (b :: b :: rest)).isSome = (pairDecode rest).isSome := by
        cases b <;> simp [pairDecode]
      rw [hp]
      simpa only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero,
        show pre.length + 2 + 1 = pre.length + 3 by omega] using hh
    · cases b <;> cases d
      · exact False.elim (h rfl)
      · refine ⟨2, by simp, ?_⟩
        simp only [pairDecode, Option.isSome_some, ↓reduceIte]
        refine ⟨⟨pre.length + 3, by simp [hx] <;> omega⟩, ?_⟩
        rw [mapParse_block M c pre rest [] false true false hx]
        rfl
      · refine ⟨2, by simp, ?_⟩
        simp only [pairDecode, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
        rw [mapParse_block M c pre rest [] true false false hx]
        exact ⟨rfl, rfl⟩
      · exact False.elim (h rfl)

/-- Once validation has succeeded, replay precisely the encoded prefix and
separator and enter the captured-payload replay with its head still at zero.
**Proof sketch.** Induct on the decoded first component. Each doubled bit
costs two emitting steps; the final `01` costs two and switches replay tapes. -/
private lemma mapPrefix_replay (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (a b : List Bool) :
    ∀ pre out (hx : x = pre ++ pairEncode a b), ∃ p,
    (pairMapTM M).tm.runFrom
      (mapCfg M c (some (.inr (.inr (true, none))))
        ⟨pre.length + 1, by simp [hx, pairEncode]; omega⟩ 0 out) (2 * a.length + 2) =
      mapCfg M c (some (.inr (.inl 6))) p 0 (out ++ pairEncode a []) := by
  induction a with
  | nil =>
    intro pre out hx
    have hx' : x = pre ++ false :: true :: b := by simpa [pairEncode] using hx
    refine ⟨⟨pre.length + 3, by simp [hx'] <;> omega⟩, ?_⟩
    simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add] using
      mapParse_block M c pre b out false true true hx'
  | cons bit a ih =>
    intro pre out hx
    have hx' : x = pre ++ bit :: bit :: pairEncode a b := by
      simpa [pairEncode, List.append_assoc] using hx
    obtain ⟨p, hp⟩ := ih (pre ++ [bit, bit]) (out ++ [bit, bit])
      (by simpa [List.append_assoc] using hx')
    refine ⟨p, ?_⟩
    rw [show 2 * (bit :: a).length + 2 = 2 + (2 * a.length + 2) by simp; omega,
      MultiTapeTM.runFrom_add, mapParse_block M c pre (pairEncode a b) out bit bit true hx']
    simp only [↓reduceIte]
    simpa [pairEncode, List.append_assoc] using hp

/-- Captured-payload replay preserves the bank and emits each stored cell once.
**Proof sketch.** Induct over emitted cells, using `take_succ` and the contiguous
buffer read equation. The terminal blank supplies the final silent halt. -/
private lemma mapPayload_replay (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (p : Fin (x.length + 2)) (out : List Bool) :
    ∀ j (_hj : j ≤ c.output.length),
    (pairMapTM M).tm.runFrom
      (mapCfg M c (some (.inr (.inl 6))) p 0 out) j =
      mapCfg M c (some (.inr (.inl 6))) p j (out ++ c.output.take j) := by
  intro j
  induction j with
  | zero => intro hj; simp [mapCfg]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    unfold MultiTapeTM.step
    change ((pairMapTM M).tm.tr (.inr (.inl 6)) _ _).apply _ = _
    have hw : (mapCfg M c (some (.inr (.inl 6))) p j
        (out ++ c.output.take j)).workTapeSymbols (Fin.last M.k) =
          some (c.output[j]'(by omega)) := by
      simp [mapCfg, captureCfg, Cfg.workTapeSymbols,
        List.getElem?_eq_getElem (by omega : j < c.output.length)]
    simp only [pairMapTM, hw]
    rw [mapAction_apply]
    rw [moveInputPos_zero, List.take_succ,
      List.getElem?_eq_getElem (by omega : j < c.output.length)]
    simp only [SignType.cast, Nat.cast_add, Nat.cast_one, Option.toList_some,
      List.append_assoc]

/-- The last blank-reading step halts after the entire capture has been emitted. -/
private lemma mapPayload_finish (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (p : Fin (x.length + 2)) (out : List Bool) :
    ((pairMapTM M).tm.runFrom
      (mapCfg M c (some (.inr (.inl 6))) p 0 out) (c.output.length + 1)).state = none ∧
    ((pairMapTM M).tm.runFrom
      (mapCfg M c (some (.inr (.inl 6))) p 0 out) (c.output.length + 1)).output = out ++ c.output := by
  rw [MultiTapeTM.runFrom_succ_eq_step', mapPayload_replay M c p out _ (le_refl _)]
  simp [MultiTapeTM.step, pairMapTM, mapCfg, captureCfg, Cfg.workTapeSymbols,
    mapAction, Action.apply]

/-- The encoding has exactly two symbols per first-component bit and two
separator symbols, followed by the unmodified payload. -/
private lemma catalogPair_length (a b : List Bool) :
    (pairEncode a b).length = 2 * a.length + 2 + b.length := by
  simp [pairEncode, Nat.mul_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The complete controller retains the first component and appends the
source's captured result, rejecting malformed inputs without any emission.
**Proof sketch.** Concatenate capture/rewind, silent validation, input rewind,
encoded-prefix replay, and captured-payload replay. Source output length is
at most its running time. The two replay lengths and all input scans therefore
fit `4 (T(n) + n + 3)`; no running time is evaluated at a padded input length. -/
private lemma pairMap_computes {M : FinTM Bool} {f : List Bool → List Bool}
    {T : ℕ → ℕ} (hM : M.ComputesFunInTime f T) :
    (pairMapTM M).ComputesFunInTime
      (fun x => match pairDecode x with
        | some (a, _) => pairEncode a (f x)
        | none => []) (fun n => 4 * (T n + n + 3)) := by
  intro x
  have hlen : (f x).length ≤ T x.length := by
    have hout := ((computesInTime_iff _ _ _ _).mp (hM x)).2
    simpa only [hout] using M.tm.output_length_le x (T x.length)
  obtain ⟨t, ht, c, ho, hstart⟩ := mapStart M x (f x) (T x.length) (hM x)
  obtain ⟨u, hu, hval⟩ := mapValidate M c x [] (by simp)
  simp only [List.length_nil, Nat.zero_add] at hval
  have hpos : (⟨1, by omega⟩ : Fin (x.length + 2)) = 1 := by
    apply Fin.ext
    simp
  rw [hpos] at hval
  have hclen : c.output.length = (f x).length := congrArg List.length ho
  cases hd : pairDecode x with
  | none =>
    simp only [hd, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hval ⊢
    have hc : (pairMapTM M).ComputesInTime x [] (t + u) := by
      apply (computesInTime_iff _ _ _ _).mpr
      rw [MultiTapeTM.runFrom_add, hstart]
      exact hval
    exact hc.mono (by omega)
  | some ab =>
    rcases ab with ⟨a, b⟩
    simp only [hd, Option.isSome_some, ↓reduceIte] at hval ⊢
    obtain ⟨p, hp⟩ := hval
    obtain ⟨r, hrle, hr⟩ := catalogRewind (pairMapTM M).tm
      (.inr (.inl 4)) (.inr (.inl 5)) (some (.inr (.inr (true, none))))
      (fun _ _ => rfl) (fun inp _ => by cases inp <;> rfl)
      (mapCfg M c (some (.inr (.inl 4))) p 0 []) rfl
    have hr' : (pairMapTM M).tm.runFrom
        (mapCfg M c (some (.inr (.inl 4))) p 0 []) r =
        mapCfg M c (some (.inr (.inr (true, none)))) 1 0 [] := hr
    obtain ⟨p', hp'⟩ := mapPrefix_replay M c a b [] []
      (by simpa using catalogPair_inverse x a b hd)
    simp only [List.length_nil, Nat.zero_add, List.nil_append] at hp'
    rw [hpos] at hp'
    have hprefix : (pairMapTM M).tm.runFrom ((pairMapTM M).tm.initCfg x)
        ((t + u + r) + (2 * a.length + 2)) =
        mapCfg M c (some (.inr (.inl 6))) p' 0 (pairEncode a []) := by
      rw [MultiTapeTM.runFrom_add _ _ (2 * a.length + 2),
        MultiTapeTM.runFrom_add _ _ r, MultiTapeTM.runFrom_add _ t u,
        hstart, hp, hr', hp']
    have hc : (pairMapTM M).ComputesInTime x (pairEncode a (f x))
        (((t + u + r) + (2 * a.length + 2)) + (c.output.length + 1)) := by
      apply (computesInTime_iff _ _ _ _).mpr
      rw [MultiTapeTM.runFrom_add _ _ (c.output.length + 1), hprefix]
      obtain ⟨hs, hout⟩ := mapPayload_finish M c p' (pairEncode a [])
      refine ⟨hs, ?_⟩
      simpa [ho, pairEncode, List.append_assoc] using hout
    apply hc.mono
    have hpbound := p.isLt
    change r ≤ p.val + 2 at hrle
    have hxlen : x.length = 2 * a.length + 2 + b.length := by
      rw [catalogPair_inverse x a b hd, catalogPair_length]
    omega

/-- **C1, the threaded map combinator** (spec, fill pending; round-2
addition per round-1 finding 3 — the data-retaining assembly the
extractors deliberately do not provide: sequential composition yields
`g (f z)` only, never simultaneous access to a retained component). Given
a machine for `g`, transform a pair's payload while carrying its head
component unchanged; malformed inputs yield `[]`. Monotonicity of `Tg`
converts the payload-length bound `|b| ≤ |z|` into a time bound, exactly
as in `Turing.FinTM.computesFunInTime_comp`.

**Construction sketch.** Parse `pairEncode a b` onto two work tapes,
silent until the separator validates; run the `g`-machine on `b`
relocated-and-captured (the W1 discipline — its output lands on the
capture tape, with length bounded by its running time via
`Turing.MultiTapeTM.output_length_le`); then emit the re-encoded pair:
doubled `a`, separator, captured `g b`. -/
theorem computesFunInTime_pairMapSnd {Mg : FinTM Bool}
    {g : List Bool → List Bool} {Tg : ℕ → ℕ}
    (hg : Mg.ComputesFunInTime g Tg) (hTg : Monotone Tg) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun z => match pairDecode z with
          | some (a, b) => pairEncode a (g b)
          | none => [])
        fun n => c * (n + 1 + Tg n) := by
  have hM := pairMap_computes (catalogPayload_computes hg hTg)
  refine ⟨pairMapTM (bufferedCompTM (pairExtractTM false true) Mg), 40, fun x => ?_⟩
  have hc := hM x
  have heq : (match pairDecode x with
      | some (a, _) => pairEncode a (g ((pairDecode x).map Prod.snd |>.getD []))
      | none => []) = (match pairDecode x with
      | some (a, b) => pairEncode a (g b)
      | none => []) := by
    cases hd : pairDecode x with
    | none => rfl
    | some ab => cases ab; simp
  dsimp only at hc
  rw [heq] at hc
  exact hc.mono (by dsimp only; omega)

/-- **P8, threaded length-bound check** (spec, fill pending — new; the
original-bound re-check discipline of the Exercise-2.1 reverse verifier,
in threaded form). On `pairEncode a b`, decide `|b| ≤ C·(|a|+1)^e` — the
original input `a` travels with the payload precisely so that this bound
is checked against *it*, the audited rule being that merely fitting inside
the enlarged region does not authorize a witness. Malformed inputs answer
`false`.

**Construction sketch.** Parse the two components onto work tapes (the
extractor scans above); lay down `C·(|a|+1)^e` in unary by the
polynomial-evaluation loop; compare against `|b|` by a parallel countdown;
emit the single verdict bit. -/
theorem computesFunInTime_pairLenCheck (C e : ℕ) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun x => [match pairDecode x with
          | some (a, b) => decide (b.length ≤ C * (a.length + 1) ^ e)
          | none => false])
        fun n => c * (n + 1) ^ (e + 1) := by
  obtain ⟨F, a, hF⟩ := computesFunInTime_pairFst
  obtain ⟨U, b, hU⟩ := computesFunInTime_polyUnary C e
  obtain ⟨G, d, hG⟩ := computesFunInTime_comp hF hU
    (by
      intro m n h
      exact Nat.mul_le_mul_left b
        (Nat.pow_le_pow_left (Nat.add_le_add_right h 1) (e + 1)))
  refine ⟨pairCountTM G, d * (a + b * (a + 1) ^ (e + 1) + 1) + 7, fun x => ?_⟩
  have hc := pairCount_computes hG x
  have hh : (pairCountTM G).ComputesInTime x
      [match pairDecode x with
        | some (u, v) => decide (v.length ≤ C * (u.length + 1) ^ e)
        | none => false]
      (d * (a * (x.length + 1) + b * (a * (x.length + 1) + 1) ^ (e + 1) + 1) +
        2 * x.length + 5) := by
    cases hd : pairDecode x with
    | none => simpa [hd, Function.comp_apply] using hc
    | some uv => cases uv; simpa [hd, Function.comp_apply] using hc
  apply hh.mono
  let P := (x.length + 1) ^ (e + 1)
  have hp : 1 ≤ P := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hn : x.length + 1 ≤ P := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right (Nat.succ_pos x.length)
      (show 1 ≤ e + 1 by omega)
  have hbase : a * (x.length + 1) + 1 ≤ (a + 1) * (x.length + 1) := by
    simp only [Nat.add_mul, Nat.one_mul]; omega
  have hpow : (a * (x.length + 1) + 1) ^ (e + 1) ≤ (a + 1) ^ (e + 1) * P := by
    simpa only [Nat.mul_pow] using Nat.pow_le_pow_left hbase (e + 1)
  have hsum : a * (x.length + 1) + b * (a * (x.length + 1) + 1) ^ (e + 1) + 1 ≤
      (a + b * (a + 1) ^ (e + 1) + 1) * P := by
    calc
      _ ≤ a * P + b * ((a + 1) ^ (e + 1) * P) + P :=
        Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left a hn)
          (Nat.mul_le_mul_left b hpow)) hp
      _ = _ := by ring
  calc
    _ = d * (a * (x.length + 1) + b * (a * (x.length + 1) + 1) ^ (e + 1) + 1) +
        (2 * x.length + 5) := by omega
    _ ≤ d * ((a + b * (a + 1) ^ (e + 1) + 1) * P) + 7 * P :=
      Nat.add_le_add (Nat.mul_le_mul_left d hsum) (by omega)
    _ = (d * (a + b * (a + 1) ^ (e + 1) + 1) + 7) * P := by ring

/-- **P9, marker strip** (spec, fill pending — harvest: the semantic layer
is the Exercise-2.1 batch's proved `stripCertificate` family; the machine
is new). On `pairEncode a v`, strip `v` at its **last** `true`
(`Turing.splitAtLastTrue`) and re-emit the threaded pair with the stripped
witness; an all-`false` region or a malformed input yields `[]` (the
rejection the downstream guard reads).

**Construction sketch.** Parse `a` and `v` onto work tapes; locate the
last `true` of `v` by one reverse sweep; then — and only then — emit the
re-encoded pair (doubled `a`, separator, the prefix of `v` before that
marker). All-`false` regions and parse failures halt with nothing
emitted. -/
theorem computesFunInTime_stripLast :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun x => match pairDecode x with
          | some (a, v) =>
            match splitAtLastTrue v with
            | some u => pairEncode a u
            | none => []
          | none => [])
        fun n => c * (n + 1) ^ 2 := by
  obtain ⟨S, a, hS⟩ := computesFunInTime_pairSnd
  obtain ⟨D, b, hD⟩ := computesFunInTime_comp hS anyTrue_computes
    (by intro m n h; exact Nat.add_le_add_right h 1)
  have hD' : D.ComputesFunInTime
      (fun x => [((pairDecode x).map Prod.snd |>.getD []).any id])
      (fun n => b * (a * (n + 1) + (a * (n + 1) + 1) + 1)) := by
    simpa only [Function.comp_apply] using hD
  obtain ⟨E, c, hE⟩ := computesFunInTime_const ([] : List Bool)
  obtain ⟨M, d, hM⟩ := computesFunInTime_cond hD' rawStrip_computes hE
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
      rcases catalogMarker_cases v with ⟨ha, hs⟩ | ⟨w, ha, hs, hp⟩
      · simpa [hd, ha, hs] using hm
      · have hx : splitAtLastTrue x = some (pairEncode u w) := by
          rw [catalogPair_inverse x u v hd]
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
  have hn : x.length + 1 ≤ (x.length + 1) ^ 2 := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right (Nat.succ_pos x.length)
      (show 1 ≤ 2 by omega)
  calc
    _ ≤ d * ((2 * b * (a + 1) + (4 + c) + 1) * (x.length + 1)) := Nat.mul_le_mul_left d hb
    _ ≤ d * ((2 * b * (a + 1) + (4 + c) + 1) * (x.length + 1) ^ 2) :=
      Nat.mul_le_mul_left d (Nat.mul_le_mul_left _ hn)
    _ = _ := by ring

/-- The audited split-search step preserves every existing candidate bit;
at the one-past-end state it stalls. -/
private def splitStep (w s : List Bool) : List Bool :=
  if s.length ≤ w.length then s ++ [true] else s

/-- Split-search acceptance is the exact padding length equation. -/
private def splitAccept (C e : ℕ) (w s : List Bool) : Bool :=
  decide (s.length + C * (s.length + 1) ^ e = w.length)

/-- The length invariant is closed even on arbitrary candidate bit patterns. -/
private lemma splitStep_inv (w s : List Bool) (hs : s.length ≤ w.length + 1) :
    (splitStep w s).length ≤ w.length + 1 := by
  unfold splitStep
  split <;> simp_all <;> omega

/-- All orbit points tested by the loop are precisely the unary candidates.
**Proof sketch.** Before fuel is exhausted the current length is the iteration
index, so the step appends one true. The extra one-past-end state is included. -/
private lemma splitStep_orbit (w : List Bool) : ∀ i, i ≤ w.length + 1 →
    (splitStep w)^[i] [] = List.replicate i true := by
  intro i
  induction i with
  | zero => intro hi; rfl
  | succ i ih =>
    intro hi
    rw [Function.iterate_succ_apply', ih (by omega)]
    simp only [splitStep, List.length_replicate, if_pos (by omega : i ≤ w.length)]
    exact (List.replicate_succ').symm

/-- Extensional equality of search predicates on the searched list preserves
both the least-success index and failure. -/
private lemma catalogFind_congr {α : Type} (xs : List α) (p q : α → Bool)
    (h : ∀ a ∈ xs, p a = q a) : xs.find? p = xs.find? q := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.find?_cons, h a (by simp)]
    rw [ih (fun b hb => h b (by simp [hb]))]

/-- The orbit predicate and `solveSplit` use the same finite search, including
its unsuccessful branch. The Boolean equality is converted explicitly. -/
private lemma splitFind_eq (C e : ℕ) (w : List Bool) :
    (List.range (w.length + 1)).find?
      (fun i => splitAccept C e w ((splitStep w)^[i] [])) = solveSplit C e w.length := by
  apply catalogFind_congr
  intro i hi
  have hi' : i ≤ w.length := by simpa only [List.mem_range, Nat.lt_succ_iff] using hi
  rw [splitStep_orbit w i (by omega)]
  apply Bool.eq_iff_iff.mpr
  simp only [splitAccept, List.length_replicate, decide_eq_true_eq, beq_iff_eq]

/-- Failed split search is equivalent to rejecting every candidate within fuel. -/
private lemma splitFind_none (C e : ℕ) (w : List Bool) :
    solveSplit C e w.length = none ↔
      ∀ i ≤ w.length, splitAccept C e w ((splitStep w)^[i] []) = false := by
  rw [← splitFind_eq, List.find?_eq_none]
  simp only [List.mem_range, Nat.lt_succ_iff, Bool.not_eq_true]

/-- Each successful orbit payload is exactly the split at the returned index;
exhaustion returns the same empty word on both sides. -/
private lemma splitLoop_result (C e : ℕ) (w : List Bool) :
    (match (List.range (w.length + 1)).find?
        (fun i => splitAccept C e w ((splitStep w)^[i] [])) with
      | some i => pairEncode (w.take ((splitStep w)^[i] []).length)
          (w.drop ((splitStep w)^[i] []).length)
      | none => []) =
    (match solveSplit C e w.length with
      | some i => pairEncode (w.take i) (w.drop i)
      | none => []) := by
  rw [splitFind_eq]
  cases hs : solveSplit C e w.length with
  | none => rfl
  | some i =>
    have hi := List.mem_of_find?_eq_some hs
    have hi' : i ≤ w.length := by simpa only [List.mem_range, Nat.lt_succ_iff] using hi
    simp only [splitStep_orbit w i (by omega), List.length_replicate]

/-- The loop overhead raises the body's polynomial exponent by exactly one.
**Proof sketch.** Bound the additive one by `(n+1)^(e+1)` and the factor `n+2`
by `2(n+1)`, then combine powers. This includes `n=0` and `e=0`. -/
private lemma splitLoop_bound (c A e n : ℕ) :
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
private def splitPos (w : List Bool) (j : ℕ) : Fin (w.length + 2) :=
  ⟨min j w.length + 1, by omega⟩

/-- A saturated countdown read is blank exactly after all input bits. -/
private lemma splitPos_read {k : ℕ} {S : Type} (w : List Bool)
    (cfg : Cfg k Bool S w) (j : ℕ) (hp : cfg.inputPos = splitPos w j) :
    cfg.inputSymbol = if h : j < w.length then some (w[j]'h) else none := by
  by_cases hj : j < w.length
  · rw [dif_pos hj]
    exact inputSymbolInner j
      (by simp [hp, splitPos, Nat.min_eq_left (by omega : j ≤ w.length), Nat.add_comm]) hj
  · rw [dif_neg hj]
    simp [Cfg.inputSymbol, hp, splitPos, Nat.min_eq_right (by omega : w.length ≤ j)]

/-- A forward move increments a saturated unary countdown position. -/
private lemma splitPos_succ (w : List Bool) (j : ℕ) :
    moveInputPos (splitPos w j) .pos = splitPos w (j + 1) := by
  by_cases hj : j < w.length
  · rw [moveInputPos_pos_of_ne_right _ (by simp [splitPos] <;> omega)]
    apply Fin.ext
    simp only [splitPos, Fin.val_mk]
    omega
  · have he : splitPos w j = ⟨w.length + 1, by omega⟩ := by
      apply Fin.ext
      simp [splitPos, Nat.min_eq_right (by omega : w.length ≤ j)]
    rw [he, SignType.pos_eq_one, moveInputPos_rightBoundary]
    apply Fin.ext
    simp [splitPos, Nat.min_eq_right (by omega : w.length ≤ j + 1)]

/-- A partially cleared unary scratch word, with its remaining suffix exposed. -/
private def splitScratch (q j : ℕ) (z : ℤ) : Option Bool :=
  if (j : ℤ) ≤ z ∧ z < q then some true else none

/-- Clearing the exposed scratch cell advances the cleared prefix by one. -/
private lemma splitScratch_erase (q j : ℕ) :
    Function.update (splitScratch q j) (j : ℤ) none = splitScratch q (j + 1) := by
  funext z
  by_cases hz : z = (j : ℤ)
  · subst z; simp [splitScratch]
  · rw [Function.update_of_ne hz]
    have he : ((j : ℤ) ≤ z ∧ z < q) ↔ (((j + 1 : ℕ) : ℤ) ≤ z ∧ z < q) := by omega
    simp only [splitScratch, he]

/-- The rejection cleanup preserves all candidate bits, appends only within
the input-length range, clears every unary scratch tape, and restores heads.
State 4 is an absorbing return seam, suitable for a first-return embedding. -/
private def splitRestoreTM (k : ℕ) : FinTM Bool where
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
private def splitRestoreScan (k : ℕ) (w s : List Bool) (j : ℕ) :
    Cfg (k + 1) Bool (splitRestoreTM k).State w :=
  ⟨some (0, decide (w.length < j)), splitPos w j,
    Fin.cases (bufferTape s) (fun _ => splitScratch (s.length + 1) j), fun _ => j, []⟩

/-- The silent cleanup scans each candidate bit once, including false bits.
**Proof sketch.** Each transition preserves tape 0, clears one cell on every
scratch tape, and advances all heads. The overflow flag records precisely
whether more candidate cells than native input cells have been consumed. -/
private lemma splitRestore_scan (k : ℕ) (w s : List Bool) : ∀ j, j ≤ s.length →
    (splitRestoreTM k).tm.runFrom (splitRestoreScan k w s 0) j =
      splitRestoreScan k w s j := by
  intro j
  induction j with
  | zero => intro hj; rfl
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hw : (splitRestoreScan k w s j).workTapeSymbols 0 = some (s[j]'(by omega)) := by
      simp [splitRestoreScan, Cfg.workTapeSymbols,
        List.getElem?_eq_getElem (by omega : j < s.length)]
    have hin := splitPos_read w (splitRestoreScan k w s j) j rfl
    unfold MultiTapeTM.step
    change ((splitRestoreTM k).tm.tr (0, decide (w.length < j)) _ _).apply _ = _
    simp only [splitRestoreTM, hw]
    refine Cfg.ext ?_ (splitPos_succ w j) ?_ ?_ rfl
    · change some (0, decide (w.length < j) ||
        (splitRestoreScan k w s j).inputSymbol.isNone) = some (0, decide (w.length < j + 1))
      rw [hin]
      by_cases hjn : j < w.length
      · simp [hjn, show ¬w.length < j by omega, show ¬w.length < j + 1 by omega]
      · simp [hjn, show w.length < j + 1 by omega]
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · exact splitScratch_erase _ _
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i <;> simp [Action.apply, splitRestoreScan]

/-- A cleaned configuration has only the candidate on tape zero; all work
heads are synchronized and the physical output is empty. -/
private def splitRestoreClean (k : ℕ) (w s : List Bool)
    (q : (splitRestoreTM k).State) (p : Fin (w.length + 2)) (h : ℤ) :
    Cfg (k + 1) Bool (splitRestoreTM k).State w :=
  ⟨some q, p, Fin.cases (bufferTape s) (fun _ => fun _ => none), fun _ => h, []⟩

/-- The end-of-scan step clears the final extra scratch cell and appends to
tape 0 exactly when the old candidate length is at most the input length. -/
private lemma splitRestore_append (k : ℕ) (w s : List Bool) :
    (splitRestoreTM k).tm.step (splitRestoreScan k w s s.length) =
      splitRestoreClean k w (splitStep w s) (1, false)
        (splitPos w s.length) (s.length - 1) := by
  have hw : (splitRestoreScan k w s s.length).workTapeSymbols 0 = none := by
    simp [splitRestoreScan, Cfg.workTapeSymbols]
  unfold MultiTapeTM.step
  change ((splitRestoreTM k).tm.tr (0, decide (w.length < s.length)) _ _).apply _ = _
  simp only [splitRestoreTM, hw]
  by_cases hs : s.length ≤ w.length
  · have hflag : decide (w.length < s.length) = false := by simp; omega
    rw [hflag]
    refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa [Action.apply, splitRestoreClean, splitStep, hs] using (bufferTape_append s true).symm
      · change Function.update (splitScratch (s.length + 1) s.length) (s.length : ℤ) none = _
        rw [splitScratch_erase]
        funext z
        simp [splitRestoreClean, splitScratch]
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i <;> simp [Action.apply, splitRestoreScan, splitRestoreClean, sub_eq_add_neg]
  · have hflag : decide (w.length < s.length) = true := by simp; omega
    rw [hflag]
    refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [Action.apply, splitRestoreScan, splitRestoreClean, splitStep, hs]
      · change Function.update (splitScratch (s.length + 1) s.length) (s.length : ℤ) none = _
        rw [splitScratch_erase]
        funext z
        simp [splitRestoreClean, splitScratch]
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i <;> simp [Action.apply, splitRestoreScan, splitRestoreClean, sub_eq_add_neg]

/-- Candidate-guided rewind restores every head, including heads on tapes
that have already been cleared. No candidate bit is altered. -/
private lemma splitRestore_rewind (k : ℕ) (w s : List Bool) (p : Fin (w.length + 2)) :
    ∀ j, j ≤ s.length →
      (splitRestoreTM k).tm.runFrom
        (splitRestoreClean k w s (1, false) p ((j : ℤ) - 1)) (j + 1) =
        splitRestoreClean k w s (2, false) p 0 := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    simp only [MultiTapeTM.step, splitRestoreClean, splitRestoreTM, Cfg.workTapeSymbols,
      Fin.cases_zero, Nat.cast_zero, zero_sub, bufferTape_left]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext i; simp [Action.apply, splitRestoreScan]
  | succ j ih =>
    intro hj
    have hs : (splitRestoreTM k).tm.step
        (splitRestoreClean k w s (1, false) p (((j + 1 : ℕ) : ℤ) - 1)) =
        splitRestoreClean k w s (1, false) p ((j : ℤ) - 1) := by
      have he : (((j + 1 : ℕ) : ℤ) - 1) = j := by omega
      rw [he]
      simp only [MultiTapeTM.step, splitRestoreClean, splitRestoreTM, Cfg.workTapeSymbols,
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
private lemma splitRestore_run (k : ℕ) (w s : List Bool) :
    ∃ t ≤ 2 * s.length + w.length + 5,
      (splitRestoreTM k).tm.runFrom (splitRestoreScan k w s 0) t =
        Cfg.ofWords (4, false) (stateWord (k + 1) (splitStep w s)) := by
  have hlen : s.length ≤ (splitStep w s).length := by
    unfold splitStep
    split <;> simp
  obtain ⟨r, hr, he⟩ := catalogRewind (splitRestoreTM k).tm (2, false) (3, false)
    (some (4, false)) (fun _ _ => rfl) (fun inp _ => by cases inp <;> rfl)
    (splitRestoreClean k w (splitStep w s) (2, false) (splitPos w s.length) 0) rfl
  have hp : (splitPos w s.length).val ≤ w.length + 1 := by simp [splitPos] <;> omega
  have hfirst : (splitRestoreTM k).tm.runFrom (splitRestoreScan k w s 0) (s.length + 1) =
      splitRestoreClean k w (splitStep w s) (1, false) (splitPos w s.length) (s.length - 1) := by
    rw [MultiTapeTM.runFrom_succ_eq_step', splitRestore_scan k w s _ (le_refl _),
      splitRestore_append]
  refine ⟨(s.length + 1) + (s.length + 1) + r, ?_, ?_⟩
  · change r ≤ (splitPos w s.length).val + 2 at hr
    omega
  · rw [MultiTapeTM.runFrom_add _ _ r,
      MultiTapeTM.runFrom_add _ (s.length + 1) (s.length + 1),
      hfirst, splitRestore_rewind k w (splitStep w s) _ _ hlen, he]
    refine Cfg.ext ?_ ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i <;>
        simp [splitRestoreClean, Cfg.ofWords, stateWord]
    · rfl
    · rfl

/-- Replace source emissions by native-input consumption. Tape zero retains
the candidate; the source bank occupies successor-indexed tapes. A finite
flag remembers consumption past the native right boundary. -/
private def splitCountAction {k : ℕ} {S H : Type} (emb : S → Bool → H) (ret : Bool → H)
    (over : Bool) (inp : Option Bool) (a : Action k Bool S) : Action (k + 1) Bool H :=
  let over' := over || (a.output.isSome && inp.isNone)
  ⟨if a.output.isSome then .pos else 0, Fin.cases (none, 0) a.workTapes, none,
    some (match a.state with | some q => emb q over' | none => ret over')⟩

/-- Source configurations use an empty virtual input and arbitrary initialized
work tapes. Their output length is consumed after the candidate's length. -/
private def splitCountCfg {k : ℕ} {S H : Type} (emb : S → Bool → H) (ret : Bool → H)
    (w s : List Bool) (c : Cfg k Bool S []) : Cfg (k + 1) Bool H w :=
  let over := decide (w.length < s.length + c.output.length)
  ⟨some (match c.state with | some q => emb q over | none => ret over),
    splitPos w (s.length + c.output.length), Fin.cases (bufferTape s) c.workTapes,
    Fin.cases 0 c.workTapePos, []⟩

/-- Consuming one additional symbol updates the saturation flag exactly. -/
private lemma splitCount_over {k : ℕ} {S : Type} (w : List Bool)
    (cfg : Cfg k Bool S w) (j : ℕ) (hp : cfg.inputPos = splitPos w j) :
    (decide (w.length < j) || cfg.inputSymbol.isNone) = decide (w.length < j + 1) := by
  rw [splitPos_read w cfg j hp]
  by_cases hj : j < w.length
  · simp [hj, show ¬w.length < j by omega, show ¬w.length < j + 1 by omega]
  · simp [hj, show w.length < j + 1 by omega]

/-- One transformed step consumes exactly its optional source emission,
preserves the candidate, and reproduces all source-bank writes and moves.
**Proof sketch.** Split on the optional output and on tape zero versus source
tapes. The one-emission case is precisely the saturated-position increment
and overflow update; the zero-emission case leaves both unchanged. -/
private lemma splitCount_apply {k : ℕ} {S H : Type} (emb : S → Bool → H) (ret : Bool → H)
    (w s : List Bool) (c : Cfg k Bool S []) (a : Action k Bool S) :
    (splitCountAction emb ret (decide (w.length < s.length + c.output.length))
      (splitCountCfg emb ret w s c).inputSymbol a).apply (splitCountCfg emb ret w s c) =
      splitCountCfg emb ret w s (a.apply c) := by
  have hflag := splitCount_over w (splitCountCfg emb ret w s c)
    (s.length + c.output.length) rfl
  cases ho : a.output with
  | none =>
    refine Cfg.ext ?_ ?_ ?_ ?_ rfl
    · simp [splitCountAction, splitCountCfg, Action.apply, ho]
    · simpa [splitCountAction, splitCountCfg, Action.apply, ho] using
        moveInputPos_zero (splitPos w (s.length + c.output.length))
    · funext i; refine Fin.cases ?_ (fun i => ?_) i <;> rfl
    · funext i; refine Fin.cases ?_ (fun i => ?_) i <;>
        simp [splitCountAction, splitCountCfg, Action.apply]
  | some b =>
    refine Cfg.ext ?_ ?_ ?_ ?_ rfl
    · simpa [splitCountAction, splitCountCfg, Action.apply, ho, Nat.add_assoc] using
        congrArg (fun flag => some (match a.state with | some q => emb q flag | none => ret flag)) hflag
    · simpa [splitCountAction, splitCountCfg, Action.apply, ho, Nat.add_assoc] using
        splitPos_succ w (s.length + c.output.length)
    · funext i; refine Fin.cases ?_ (fun i => ?_) i <;> rfl
    · funext i; refine Fin.cases ?_ (fun i => ?_) i <;>
        simp [splitCountAction, splitCountCfg, Action.apply]

/-- A counted source run follows the original work-bank computation exactly,
including a final emitting halt, while consuming its output on native input.
**Proof sketch.** Empty virtual input always reads blank. Apply the one-step
correspondence through the source's first halt, as in `capture_run`; the
physical output stays empty throughout. -/
private lemma splitCount_run {k : ℕ} {S H : Type}
    (tm : MultiTapeTM k Bool S) (host : MultiTapeTM (k + 1) Bool H)
    (emb : S → Bool → H) (ret : Bool → H)
    (hagree : ∀ q over inp work, host.tr (emb q over) inp work =
      splitCountAction emb ret over inp (tm.tr q none (fun i => work i.succ)))
    (w s : List Bool) (c : Cfg k Bool S []) (t : ℕ)
    (hlive : ∀ j < t, ¬(tm.runFrom c j).Halted) :
    host.runFrom (splitCountCfg emb ret w s c) t =
      splitCountCfg emb ret w s (tm.runFrom c t) := by
  have hstep (d : Cfg k Bool S []) (hs : ¬d.Halted) :
      host.step (splitCountCfg emb ret w s d) = splitCountCfg emb ret w s (tm.step d) := by
    cases hq : d.state with
    | none => exact False.elim (hs hq)
    | some q =>
      have hstate : (splitCountCfg emb ret w s d).state =
          some (emb q (decide (w.length < s.length + d.output.length))) := by
        simp [splitCountCfg, hq]
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
      have hwork : (fun i => (splitCountCfg emb ret w s d).workTapeSymbols i.succ) =
          d.workTapeSymbols := by
        funext i; simp [splitCountCfg, Cfg.workTapeSymbols]
      simp only [MultiTapeTM.step, hstate, hq]
      rw [hagree, hwork, hsource]
      exact splitCount_apply emb ret w s d _
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
private lemma splitPoly_loop_end (c C q : ℕ) (hq : 0 < q) :
    (catalogPolyUnaryTM c C).tm.runFrom
      (catalogPolyCfg (C := C) [] q (.loop (Fin.last c)) (fun _ => 0) [])
      (catalogPolyCost q C (c + 1) + 1) =
      {catalogPolyCfg (C := C) [] q (.advance (Fin.last (c + 1))) (fun _ => 0)
        (List.replicate (C * q ^ (c + 1)) true) with state := none} := by
  have hl := catalogPoly_loop (c := c) (C := C) [] q hq c (by omega)
    (fun _ => 0) (by simp) [] q 0 (by omega)
  have hout : q * (C * q ^ c) = C * q ^ (c + 1) := by rw [Nat.pow_succ]; ring
  have hloop : (catalogPolyUnaryTM c C).tm.runFrom
      (catalogPolyCfg (C := C) [] q (.loop (Fin.last c)) (fun _ => 0) [])
      (catalogPolyCost q C (c + 1)) =
      catalogPolyCfg (C := C) [] q (.advance (Fin.last (c + 1))) (fun _ => 0)
        (List.replicate (C * q ^ (c + 1)) true) := by
    simpa [catalogPolyCost, hout] using hl
  rw [MultiTapeTM.runFrom_succ_eq_step', hloop]
  simp only [MultiTapeTM.step, catalogPolyCfg, catalogPolyUnaryTM, Fin.val_last,
    Nat.lt_irrefl, ↓reduceDIte]
  refine Cfg.ext rfl ?_ rfl ?_ ?_
  · rfl
  · funext i; simp [MultiTapeTM.step, catalogPolyUnaryTM, Action.apply, catalogPolyCfg]
  · simp [MultiTapeTM.step, catalogPolyUnaryTM, Action.apply, catalogPolyCfg]

/-- A run reaching an absorbing control state has a least such entry, and its
configuration at that first entry is already the final configuration.
**Proof sketch.** Choose the least hit. Absorption makes its entire suffix
constant, so the bounded endpoint identifies the first-hit configuration. -/
private lemma catalogFirstEntry {k : ℕ} {S : Type} {w : List Bool}
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
private lemma splitRestore_first (k : ℕ) (w s : List Bool) :
    ∃ t, 0 < t ∧ t ≤ 2 * s.length + w.length + 5 ∧
      (∀ j < t, ((splitRestoreTM k).tm.runFrom (splitRestoreScan k w s 0) j).state
        ≠ some (4, false)) ∧
      (splitRestoreTM k).tm.runFrom (splitRestoreScan k w s 0) t =
        Cfg.ofWords (4, false) (stateWord (k + 1) (splitStep w s)) := by
  obtain ⟨T, hTle, hT⟩ := splitRestore_run k w s
  have hfix (z : Cfg (k + 1) Bool (splitRestoreTM k).State w)
      (hz : z.state = some (4, false)) : (splitRestoreTM k).tm.step z = z := by
    unfold MultiTapeTM.step
    rw [hz]
    change (controlAction 0 (some (4, false))).apply z = z
    rw [controlAction_apply, moveInputPos_zero]
    cases z
    simp_all
  obtain ⟨t, ht, hi, he⟩ := catalogFirstEntry (splitRestoreTM k).tm (4, false)
    (splitRestoreScan k w s 0) _ T hfix rfl hT
  refine ⟨t, ?_, ht.trans hTle, hi, he⟩
  by_contra h
  have ht0 : t = 0 := by omega
  have hstate := congrArg Cfg.state he
  simp only [ht0, MultiTapeTM.runFrom_zero, splitRestoreScan, Cfg.ofWords,
    Option.some.injEq, Prod.mk.injEq] at hstate
  have hf := congrArg (fun q : (splitRestoreTM k).State => q.1.val) hstate
  norm_num at hf

/-- Native countdown acceptance is exactly equality of the consumed length
and the original input length; overflow and short counts both reject. -/
private lemma splitCount_accept {k : ℕ} {S H : Type} (emb : S → Bool → H) (ret : Bool → H)
    (w s : List Bool) (c : Cfg k Bool S []) :
    (!decide (w.length < s.length + c.output.length) &&
      (splitCountCfg emb ret w s c).inputSymbol.isNone) =
        decide (s.length + c.output.length = w.length) := by
  rw [splitPos_read w (splitCountCfg emb ret w s c) (s.length + c.output.length) rfl]
  by_cases hlt : s.length + c.output.length < w.length
  · simp [hlt, show ¬s.length + c.output.length = w.length by omega]
  · by_cases he : s.length + c.output.length = w.length
    · simp [he]
    · simp [hlt, he, show w.length < s.length + c.output.length by omega]

/-- The counted simulation can be stopped at the source's first halt without
losing the exact initialized-bank endpoint. This removes any padded halted
tail from a source time bound before entering the next controller phase. -/
private lemma splitCount_firstHalt {k : ℕ} {S H : Type}
    (tm : MultiTapeTM k Bool S) (host : MultiTapeTM (k + 1) Bool H)
    (emb : S → Bool → H) (ret : Bool → H)
    (hagree : ∀ q over inp work, host.tr (emb q over) inp work =
      splitCountAction emb ret over inp (tm.tr q none (fun i => work i.succ)))
    (w s : List Bool) (c d : Cfg k Bool S []) (T : ℕ)
    (hd : d.state = none) (hT : tm.runFrom c T = d) :
    ∃ t ≤ T, host.runFrom (splitCountCfg emb ret w s c) t = splitCountCfg emb ret w s d := by
  classical
  have hh : ∃ t, (tm.runFrom c t).state = none := ⟨T, by rw [hT, hd]⟩
  let t := Nat.find hh
  have ht : t ≤ T := Nat.find_min' hh (by rw [hT, hd])
  have hs : (tm.runFrom c t).state = none := Nat.find_spec hh
  have he := tm.runFrom_add c t (T - t)
  rw [Nat.add_sub_of_le ht, hT, tm.runFrom_of_halt _ hs] at he
  refine ⟨t, ht, ?_⟩
  rw [splitCount_run tm host emb ret hagree w s c t (fun j hj => Nat.find_min hh hj), ← he]

/-- Prepare the polynomial loop bank by copying the candidate's length to all
scratch tapes in parallel, adding the extra side-length cell, and rewinding
all work heads along the untouched candidate. State 2 is the return seam. -/
private def splitPrepareTM (k : ℕ) : FinTM Bool where
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
private def splitPrepareScan (k : ℕ) (w s : List Bool) (j : ℕ) :
    Cfg (k + 1) Bool (splitPrepareTM k).State w :=
  ⟨some (0, decide (w.length < j)), splitPos w j,
    Fin.cases (bufferTape s) (fun _ => catalogPolyTape j), fun _ => j, []⟩

/-- Preparation copies a unary side length without reading or changing any
candidate bit value. The same induction covers a candidate past native EOF. -/
private lemma splitPrepare_scan (k : ℕ) (w s : List Bool) : ∀ j, j ≤ s.length →
    (splitPrepareTM k).tm.runFrom (splitPrepareScan k w s 0) j =
      splitPrepareScan k w s j := by
  intro j
  induction j with
  | zero => intro hj; rfl
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hw : (splitPrepareScan k w s j).workTapeSymbols 0 = some (s[j]'(by omega)) := by
      simp [splitPrepareScan, Cfg.workTapeSymbols,
        List.getElem?_eq_getElem (by omega : j < s.length)]
    unfold MultiTapeTM.step
    change ((splitPrepareTM k).tm.tr (0, decide (w.length < j)) _ _).apply _ = _
    simp only [splitPrepareTM, hw]
    refine Cfg.ext ?_ (splitPos_succ w j) ?_ ?_ rfl
    · exact congrArg (fun over => some (0, over))
        (splitCount_over w (splitPrepareScan k w s j) j rfl)
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · exact catalogPolyTape_write j
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i <;> simp [Action.apply, splitPrepareScan]

/-- Prepared scratch tapes have side length `|s|+1`, with synchronized heads;
the overflow flag records the candidate's length alone. -/
private def splitPrepareReady (k : ℕ) (w s : List Bool)
    (q : Fin 3) (h : ℤ) : Cfg (k + 1) Bool (splitPrepareTM k).State w :=
  ⟨some (q, decide (w.length < s.length)), splitPos w s.length,
    Fin.cases (bufferTape s) (fun _ => catalogPolyTape (s.length + 1)), fun _ => h, []⟩

/-- Adding the extra side-length cell handles the empty candidate uniformly. -/
private lemma splitPrepare_extra (k : ℕ) (w s : List Bool) :
    (splitPrepareTM k).tm.step (splitPrepareScan k w s s.length) =
      splitPrepareReady k w s 1 (s.length - 1) := by
  have hw : (splitPrepareScan k w s s.length).workTapeSymbols 0 = none := by
    simp [splitPrepareScan, Cfg.workTapeSymbols]
  unfold MultiTapeTM.step
  change ((splitPrepareTM k).tm.tr (0, decide (w.length < s.length)) _ _).apply _ = _
  simp only [splitPrepareTM, hw]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
  · funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · exact catalogPolyTape_write s.length
  · funext i
    refine Fin.cases ?_ (fun i => ?_) i <;>
      simp [Action.apply, splitPrepareScan, splitPrepareReady, sub_eq_add_neg]

/-- Rewind the synchronized bank along the preserved candidate; each scratch
tape retains its extra cell even though the rewind uses the candidate length. -/
private lemma splitPrepare_rewind (k : ℕ) (w s : List Bool) : ∀ j, j ≤ s.length →
    (splitPrepareTM k).tm.runFrom (splitPrepareReady k w s 1 ((j : ℤ) - 1)) (j + 1) =
      splitPrepareReady k w s 2 0 := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    simp only [MultiTapeTM.step, splitPrepareReady, splitPrepareTM, Cfg.workTapeSymbols,
      Fin.cases_zero, Nat.cast_zero, zero_sub, bufferTape_left]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext i; simp [Action.apply]
  | succ j ih =>
    intro hj
    have hs : (splitPrepareTM k).tm.step (splitPrepareReady k w s 1 (((j + 1 : ℕ) : ℤ) - 1)) =
        splitPrepareReady k w s 1 ((j : ℤ) - 1) := by
      have he : (((j + 1 : ℕ) : ℤ) - 1) = j := by omega
      rw [he]
      simp only [MultiTapeTM.step, splitPrepareReady, splitPrepareTM, Cfg.workTapeSymbols,
        Fin.cases_zero, bufferTape_nat, List.getElem?_eq_getElem (by omega : j < s.length)]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext i; simp [Action.apply, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- From the audited state-word seam, preparation takes exactly `2(|s|+1)`
silent steps and initializes every loop head at zero. -/
private lemma splitPrepare_run (k : ℕ) (w s : List Bool) :
    (splitPrepareTM k).tm.runFrom
      (Cfg.ofWords (input := w) (0, false) (stateWord (k + 1) s)) (2 * (s.length + 1)) =
      splitPrepareReady k w s 2 0 := by
  have hinit : Cfg.ofWords (input := w) (0, false) (stateWord (k + 1) s) =
      splitPrepareScan k w s 0 := by
    refine Cfg.ext (by simp [splitPrepareScan, Cfg.ofWords]) ?_ ?_ rfl rfl
    · simp [splitPrepareScan, Cfg.ofWords, splitPos]
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i <;>
        simp [splitPrepareScan, Cfg.ofWords, stateWord]
      funext z
      simp [catalogPolyTape]
  have hfirst : (splitPrepareTM k).tm.runFrom (splitPrepareScan k w s 0) (s.length + 1) =
      splitPrepareReady k w s 1 (s.length - 1) := by
    rw [MultiTapeTM.runFrom_succ_eq_step', splitPrepare_scan k w s _ (le_refl _), splitPrepare_extra]
  rw [hinit, show 2 * (s.length + 1) = (s.length + 1) + (s.length + 1) by omega,
    MultiTapeTM.runFrom_add, hfirst, splitPrepare_rewind k w s s.length (le_refl _)]

/-- Preparation can be exposed at its first return-state entry, with no
premature visit and without changing its exact initialized-bank endpoint. -/
private lemma splitPrepare_first (k : ℕ) (w s : List Bool) :
    ∃ t ≤ 2 * (s.length + 1),
      (∀ j < t, ((splitPrepareTM k).tm.runFrom
        (Cfg.ofWords (input := w) (0, false) (stateWord (k + 1) s)) j).state ≠
          some (2, decide (w.length < s.length))) ∧
      (splitPrepareTM k).tm.runFrom
        (Cfg.ofWords (input := w) (0, false) (stateWord (k + 1) s)) t =
          splitPrepareReady k w s 2 0 := by
  apply catalogFirstEntry (splitPrepareTM k).tm (2, decide (w.length < s.length))
  · intro z hz
    unfold MultiTapeTM.step
    rw [hz]
    change (controlAction 0 (some (2, decide (w.length < s.length)))).apply z = z
    rw [controlAction_apply, moveInputPos_zero]
    cases z
    simp_all
  · rfl
  · exact splitPrepare_run k w s

/-- A phase trace excludes the round anchor even at its two endpoints. -/
private def splitSafe {k : ℕ} {S : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (anchor : S) (c : Cfg k Bool S w) (t : ℕ) : Prop :=
  ∀ j ≤ t, (tm.runFrom c j).state ≠ some anchor

/-- Safe traces concatenate at their literal configuration seam. -/
private lemma splitSafe_add {k : ℕ} {S : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (anchor : S) (c : Cfg k Bool S w) (u v : ℕ)
    (hu : splitSafe tm anchor c u) (hv : splitSafe tm anchor (tm.runFrom c u) v) :
    splitSafe tm anchor c (u + v) := by
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
private lemma splitEmbed_cut {k : ℕ} {S H : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (host : MultiTapeTM k Bool H)
    (emb : S → H) (anchor : H) (stop : S → Prop) [DecidablePred stop]
    (haway : ∀ q, emb q ≠ anchor)
    (hfix : ∀ c : Cfg k Bool S w, (∃ q, c.state = some q ∧ stop q) → tm.step c = c)
    (hagree : ∀ q, ¬stop q → ∀ inp work,
      host.tr (emb q) inp work = (tm.tr q inp work).mapState emb)
    (c d : Cfg k Bool S w) (T : ℕ)
    (hd : ∃ q, d.state = some q ∧ stop q) (hT : tm.runFrom c T = d) :
    ∃ t ≤ T, host.runFrom (c.mapState emb) t = d.mapState emb ∧
      splitSafe host anchor (c.mapState emb) t := by
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
private def splitRewindTM (k : ℕ) : FinTM Bool where
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
private def splitEmitTM (k : ℕ) : FinTM Bool where
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
private inductive SplitBodyState (S : Type) where
  | anchor
  | prepare (q : Fin 3 × Bool)
  | count (q : S) (over : Bool)
  | check (over : Bool)
  | rewind (accept : Bool) (q : Fin 3)
  | restore (q : Fin 5 × Bool)
  | emit (q : Fin 4)

private instance splitBodyStateFintype (S : Type) [Fintype S] :
    Fintype (SplitBodyState S) := derive_fintype% _

/-- Equality of controller states compares only matching phases and their
finite payloads. Keep the instance private, including its generated helpers. -/
private instance splitBodyStateDecidableEq (S : Type) [DecidableEq S] :
    DecidableEq (SplitBodyState S) := by
  intro a b
  cases a <;> cases b
  all_goals try (solve | apply isFalse; intro h; cases h)
  · exact isTrue rfl
  · exact decidable_of_iff _ (Iff.symm (iff_of_eq (SplitBodyState.prepare.injEq _ _)))
  · exact decidable_of_iff _ (Iff.symm (iff_of_eq (SplitBodyState.count.injEq _ _ _ _)))
  · exact decidable_of_iff _ (Iff.symm (iff_of_eq (SplitBodyState.check.injEq _ _)))
  · exact decidable_of_iff _ (Iff.symm (iff_of_eq (SplitBodyState.rewind.injEq _ _ _ _)))
  · exact decidable_of_iff _ (Iff.symm (iff_of_eq (SplitBodyState.restore.injEq _ _)))
  · exact decidable_of_iff _ (Iff.symm (iff_of_eq (SplitBodyState.emit.injEq _ _)))

/-- Combined round controller. The polynomial source starts on the prepared
bank, and its emissions are counted against native input without physical
output. Every seam transition is explicit, including the final anchor return. -/
private def splitBodyTM (M : FinTM Bool) (start : M.State) : FinTM Bool where
  k := M.k + 1
  State := SplitBodyState M.State
  tm := {
    q₀ := .anchor
    tr := fun q inp work => match q with
      | .anchor => controlAction 0 (some (.prepare (0, false)))
      | .prepare p =>
        if p.1 = 2 then controlAction 0 (some (.count start p.2))
        else ((splitPrepareTM M.k).tm.tr p inp work).mapState .prepare
      | .count q over => splitCountAction .count .check over inp
          (M.tm.tr q none (fun i => work i.succ))
      | .check over => controlAction 0 (some (.rewind (!over && inp.isNone) 0))
      | .rewind ok p =>
        if p = 2 then controlAction 0 (some (if ok then .emit 0 else .restore (0, false)))
        else ((splitRewindTM M.k).tm.tr p inp work).mapState (.rewind ok)
      | .restore p =>
        if p = (4, false) then controlAction 0 (some .anchor)
        else ((splitRestoreTM M.k).tm.tr p inp work).mapState .restore
      | .emit p => ((splitEmitTM M.k).tm.tr p inp work).mapState .emit }

/-- The source bank has the candidate's successor length on each tape and
all heads at zero; its virtual input is empty. -/
private def splitBank (M : FinTM Bool) (s : List Bool)
    (q : Option M.State) (out : List Bool) : Cfg M.k Bool M.State [] :=
  ⟨q, 1, fun _ => catalogPolyTape (s.length + 1), fun _ => 0, out⟩

/-- The genuine initial configuration is the empty-candidate anchor seam;
there is no unproved startup work hidden in a zero-time witness. -/
private lemma splitBody_start (M : FinTM Bool) (start : M.State) (w : List Bool) :
    (splitBodyTM M start).tm.initCfg w =
      Cfg.ofWords .anchor (stateWord (M.k + 1) []) := by
  rw [initCfg_ofWords]
  congr 1
  funext i
  simp [stateWord]

/-- A complete source embedding commutes with every step, including halt. -/
private lemma splitEmbed_run {k : ℕ} {S H : Type} {w : List Bool}
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
private lemma splitBody_prepare (M : FinTM Bool) (start : M.State) (w s : List Bool) :
    ∃ t ≤ 2 * (s.length + 1),
      (splitBodyTM M start).tm.runFrom
        (Cfg.ofWords (.prepare (0, false)) (stateWord (M.k + 1) s)) (t + 1) =
          splitCountCfg SplitBodyState.count SplitBodyState.check w s
            (splitBank M s (some start) []) ∧
      splitSafe (splitBodyTM M start).tm .anchor
        (Cfg.ofWords (input := w) (.prepare (0, false)) (stateWord (M.k + 1) s)) (t + 1) := by
  obtain ⟨t, ht, he, hsafe⟩ := splitEmbed_cut (splitPrepareTM M.k).tm
    (splitBodyTM M start).tm SplitBodyState.prepare .anchor (fun q => q.1 = 2)
    (by intro q; simp)
    (by
      rintro z ⟨⟨q, over⟩, hz, hq⟩
      change q = 2 at hq
      subst q
      simp only [MultiTapeTM.step, hz]
      change (controlAction 0 (some (2, over))).apply z = z
      rw [controlAction_apply, moveInputPos_zero]
      cases z; simp_all)
    (by intro q hq inp work; simp [splitBodyTM, hq])
    (Cfg.ofWords (input := w) (0, false) (stateWord (M.k + 1) s))
    (splitPrepareReady M.k w s 2 0) (2 * (s.length + 1))
    ⟨_, rfl, rfl⟩ (splitPrepare_run M.k w s)
  have hstep : (splitBodyTM M start).tm.step
      ((splitPrepareReady M.k w s 2 0).mapState SplitBodyState.prepare) =
      splitCountCfg SplitBodyState.count SplitBodyState.check w s
        (splitBank M s (some start) []) := by
    simp only [MultiTapeTM.step, Cfg.mapState, splitPrepareReady, Option.map_some,
      splitBodyTM, ↓reduceIte]
    refine Cfg.ext ?_ ?_ rfl ?_ rfl
    · simp [Action.apply, controlAction, splitCountCfg, splitBank]
    · simp [Action.apply, controlAction, splitCountCfg, splitBank]
    · funext i
      refine Fin.cases ?_ (fun j => ?_) i <;>
        simp [Action.apply, controlAction, splitCountCfg, splitBank]
  have hinit : (Cfg.ofWords (input := w) (0, false) (stateWord (M.k + 1) s)).mapState
      (SplitBodyState.prepare (S := M.State)) = Cfg.ofWords (.prepare (0, false)) (stateWord (M.k + 1) s) := rfl
  rw [hinit] at he hsafe
  have hend : (splitBodyTM M start).tm.runFrom
      (Cfg.ofWords (.prepare (0, false)) (stateWord (M.k + 1) s)) (t + 1) =
      splitCountCfg SplitBodyState.count SplitBodyState.check w s
        (splitBank M s (some start) []) := by
    rw [MultiTapeTM.runFrom_succ_eq_step', he, hstep]
  refine ⟨t, ht, hend, ?_⟩
  intro j hj
  by_cases hjt : j ≤ t
  · exact hsafe j hjt
  · have hj' : j = t + 1 := by omega
    rw [hj', hend]
    simp [splitCountCfg, splitBank]

/-- Counted evaluation reaches its first source halt; every prefix remains
in a count or check state and therefore cannot revisit the round anchor.
**Proof sketch.** Choose the least source halt and remove its constant halted
suffix. Apply the counted correspondence to every prefix through that halt;
its control image is disjoint from the anchor, including the return state. -/
private lemma splitBody_count (M : FinTM Bool) (start : M.State) (w s : List Bool)
    (out : List Bool) (T : ℕ)
    (hT : M.tm.runFrom (splitBank M s (some start) []) T = splitBank M s none out) :
    ∃ t ≤ T, (splitBodyTM M start).tm.runFrom
      (splitCountCfg SplitBodyState.count SplitBodyState.check w s (splitBank M s (some start) [])) t =
      splitCountCfg SplitBodyState.count SplitBodyState.check w s (splitBank M s none out) ∧
      splitSafe (splitBodyTM M start).tm .anchor
        (splitCountCfg SplitBodyState.count SplitBodyState.check w s (splitBank M s (some start) [])) t := by
  classical
  let c := splitBank M s (some start) []
  let d := splitBank M s none out
  have hh : ∃ t, (M.tm.runFrom c t).state = none := ⟨T, by rw [hT]; rfl⟩
  let t := Nat.find hh
  have ht : t ≤ T := Nat.find_min' hh (by rw [hT]; rfl)
  have he : M.tm.runFrom c t = d := by
    have h := M.tm.runFrom_add c t (T - t)
    rw [Nat.add_sub_of_le ht, hT, M.tm.runFrom_of_halt _ (Nat.find_spec hh)] at h
    exact h.symm
  have hp (j : ℕ) (hj : j ≤ t) := splitCount_run M.tm (splitBodyTM M start).tm
    SplitBodyState.count SplitBodyState.check (fun _ _ _ _ => rfl) w s c j
    (fun l hl => Nat.find_min hh (by omega))
  refine ⟨t, ht, ?_, ?_⟩
  · rw [hp t (le_refl _), he]
  · intro j hj
    rw [hp j hj]
    cases hq : (M.tm.runFrom c j).state <;> simp [splitCountCfg, hq]

/-- Rewind preserves the exact source bank and physical output. Its terminal
state is cut before dispatch to the accepting emitter or rejecting cleanup.
**Proof sketch.** Use the quantitative native rewind, then cut its absorbing
return and embed that prefix while retaining the acceptance bit in control. -/
private lemma splitBody_rewind (M : FinTM Bool) (start : M.State) (w : List Bool)
    (ok : Bool) (c : Cfg (M.k + 1) Bool (Fin 3) w)
    (hc : c.state = some 0) :
    ∃ t ≤ c.inputPos.val + 2,
      (splitBodyTM M start).tm.runFrom (c.mapState (SplitBodyState.rewind ok)) t =
        ({c with state := some (2 : Fin 3), inputPos := 1}).mapState (SplitBodyState.rewind ok) ∧
      splitSafe (splitBodyTM M start).tm .anchor (c.mapState (SplitBodyState.rewind ok)) t := by
  obtain ⟨T, hT, he⟩ := catalogRewind (splitRewindTM M.k).tm (0 : Fin 3) (1 : Fin 3) (some (2 : Fin 3))
    (fun _ _ => rfl) (fun _ _ => rfl) c hc
  obtain ⟨t, ht, hend, hsafe⟩ := splitEmbed_cut (splitRewindTM M.k).tm
    (splitBodyTM M start).tm (SplitBodyState.rewind ok) .anchor (fun q => q = (2 : Fin 3))
    (by intro q; simp)
    (by
      rintro z ⟨q, hz, rfl⟩
      simp only [MultiTapeTM.step, hz]
      change (controlAction 0 (some (2 : Fin 3))).apply z = z
      rw [controlAction_apply, moveInputPos_zero]
      cases z; simp_all)
    (by intro q hq inp work; simp [splitBodyTM, hq])
    c {c with state := some (2 : Fin 3), inputPos := 1} T ⟨(2 : Fin 3), rfl, rfl⟩ he
  exact ⟨t, ht.trans hT, hend, hsafe⟩

/-- Rejection cleanup is embedded up to its absorbing return, so its exact
restoration and the no-anchor property hold simultaneously in the body.
**Proof sketch.** Apply the exact restoration run and cut at its absorbing
false-flag return. Its host control remains in the restore phase; the final
transition to the anchor is accounted for separately by the round proof. -/
private lemma splitBody_restore (M : FinTM Bool) (start : M.State) (w s : List Bool) :
    ∃ t ≤ 2 * s.length + w.length + 5,
      (splitBodyTM M start).tm.runFrom
        ((splitRestoreScan M.k w s 0).mapState SplitBodyState.restore) t =
        Cfg.ofWords (.restore (4, false)) (stateWord (M.k + 1) (splitStep w s)) ∧
      splitSafe (splitBodyTM M start).tm .anchor
        ((splitRestoreScan M.k w s 0).mapState SplitBodyState.restore) t := by
  obtain ⟨T, hT, he⟩ := splitRestore_run M.k w s
  obtain ⟨t, ht, hend, hsafe⟩ := splitEmbed_cut (splitRestoreTM M.k).tm
    (splitBodyTM M start).tm SplitBodyState.restore .anchor (fun q => q = (4, false))
    (by intro q; simp)
    (by
      rintro z ⟨q, hz, rfl⟩
      simp only [MultiTapeTM.step, hz]
      change (controlAction 0 (some (4, false))).apply z = z
      rw [controlAction_apply, moveInputPos_zero]
      cases z; simp_all)
    (by intro q hq inp work; simp [splitBodyTM, hq])
    (splitRestoreScan M.k w s 0)
    (Cfg.ofWords (4, false) (stateWord (M.k + 1) (splitStep w s))) T
    ⟨_, rfl, rfl⟩ he
  exact ⟨t, ht.trans hT, hend, hsafe⟩

/-- Emitter configurations preserve the initialized scratch bank and use the
candidate head only to count the doubled native prefix. -/
private def splitEmitCfg (k : ℕ) (w s : List Bool) (q : Option (Fin 4))
    (j h : ℕ) (out : List Bool) : Cfg (k + 1) Bool (Fin 4) w :=
  ⟨q, splitPos w j, Fin.cases (bufferTape s) (fun _ => catalogPolyTape (s.length + 1)),
    Fin.cases (h : ℤ) (fun _ => 0), out⟩

/-- Two transitions emit two copies of the current native bit and advance
both the native head and the candidate counter. Arbitrary candidate bit
values are read only for their presence.
**Proof sketch.** Induct on the number of doubled cells. The two transitions
read the same native bit, emit it twice, and only then advance both heads. -/
private lemma splitEmit_double (k : ℕ) (w s : List Bool) (hs : s.length ≤ w.length) :
    ∀ j, j ≤ s.length → (splitEmitTM k).tm.runFrom
      (splitEmitCfg k w s (some 0) 0 0 []) (2 * j) =
      splitEmitCfg k w s (some 0) j j ((w.take j).flatMap fun b => [b, b]) := by
  intro j
  induction j with
  | zero => intro hj; rfl
  | succ j ih =>
    intro hj
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by omega,
      MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hread (q : Fin 4) (out : List Bool) :
        (splitEmitCfg k w s (some q) j j out).inputSymbol = some (w[j]'(by omega)) := by
      rw [splitPos_read w _ j rfl, dif_pos (by omega)]
    have hwork : (splitEmitCfg k w s (some 0) j j
        ((w.take j).flatMap fun b => [b, b])).workTapeSymbols 0 = some (s[j]'(by omega)) := by
      simp [splitEmitCfg, Cfg.workTapeSymbols, List.getElem?_eq_getElem (by omega : j < s.length)]
    have hfirst : (splitEmitTM k).tm.step
        (splitEmitCfg k w s (some 0) j j ((w.take j).flatMap fun b => [b, b])) =
        splitEmitCfg k w s (some 1) j j
          (((w.take j).flatMap fun b => [b, b]) ++ [w[j]'(by omega)]) := by
      unfold MultiTapeTM.step
      change ((splitEmitTM k).tm.tr (0 : Fin 4) _ _).apply _ = _
      simp only [splitEmitTM, hwork, hread]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext i; simp [Action.apply, splitEmitCfg]
    rw [hfirst]
    unfold MultiTapeTM.step
    change ((splitEmitTM k).tm.tr (1 : Fin 4) _ _).apply _ = _
    simp only [splitEmitTM, hread]
    refine Cfg.ext rfl (splitPos_succ w j) ?_ ?_ ?_
    · funext i
      refine Fin.cases ?_ (fun l => ?_) i <;> rfl
    · funext i
      refine Fin.cases ?_ (fun l => ?_) i <;> simp [Action.apply, splitEmitCfg]
    · change (((w.take j).flatMap fun b => [b, b]) ++ [w[j]'(by omega)]) ++
          [w[j]'(by omega)] = (w.take (j + 1)).flatMap fun b => [b, b]
      simp only [List.take_succ, List.getElem?_eq_getElem (by omega : j < w.length),
        Option.toList_some, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.append_assoc, List.cons_append, List.nil_append]

/-- Once the counter is exhausted, emit the two separator bits without
moving the native head away from the beginning of the suffix. -/
private lemma splitEmit_separator (k : ℕ) (w s : List Bool) (out : List Bool) :
    (splitEmitTM k).tm.runFrom (splitEmitCfg k w s (some 0) s.length s.length out) 2 =
      splitEmitCfg k w s (some 3) s.length s.length (out ++ [false, true]) := by
  have hwork : (splitEmitCfg k w s (some 0) s.length s.length out).workTapeSymbols 0 = none := by
    simp [splitEmitCfg, Cfg.workTapeSymbols]
  have hf : (splitEmitTM k).tm.step (splitEmitCfg k w s (some 0) s.length s.length out) =
      splitEmitCfg k w s (some 2) s.length s.length (out ++ [false]) := by
    unfold MultiTapeTM.step
    change ((splitEmitTM k).tm.tr (0 : Fin 4) _ _).apply _ = _
    simp only [splitEmitTM, hwork]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext i; simp [Action.apply, splitEmitCfg]
  rw [show 2 = 1 + 1 by omega, MultiTapeTM.runFrom_succ_eq_step,
    show (splitEmitTM k).tm.step _ = _ from hf, MultiTapeTM.runFrom_succ_eq_step,
    MultiTapeTM.runFrom_zero]
  refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ ?_
  · funext i; simp [MultiTapeTM.step, splitEmitTM, Action.apply, splitEmitCfg]
  · simp [MultiTapeTM.step, splitEmitTM, Action.apply, splitEmitCfg, List.append_assoc]

/-- The suffix-copy phase preserves all work tapes and copies native bits
verbatim, including the empty suffix and its final blank-reading halt.
**Proof sketch.** Induct on the remaining suffix while allowing arbitrary
already-copied prefix and output. The nonempty case copies one native bit;
the empty case reads the right blank and halts without an extra emission. -/
private lemma splitEmit_suffix (k : ℕ) (w s rest : List Bool) :
    ∀ pre out h, w = pre ++ rest → (splitEmitTM k).tm.runFrom
      (splitEmitCfg k w s (some 3) pre.length h out) (rest.length + 1) =
      splitEmitCfg k w s none w.length h (out ++ rest) := by
  induction rest with
  | nil =>
    intro pre out h hw
    have he : w = pre := by simpa using hw
    clear hw
    subst w
    simp only [List.append_nil, List.length_nil, MultiTapeTM.runFrom_succ_eq_step,
      MultiTapeTM.runFrom_zero]
    have hr := splitPos_read pre (splitEmitCfg k pre s (some 3) pre.length h out) pre.length rfl
    simp only [Nat.lt_irrefl, ↓reduceDIte] at hr
    unfold MultiTapeTM.step
    change ((splitEmitTM k).tm.tr (3 : Fin 4) _ _).apply _ = _
    rw [hr]
    simp [splitEmitTM, controlAction, splitEmitCfg]
  | cons b rest ih =>
    intro pre out h hw
    have hread : (splitEmitCfg k w s (some 3) pre.length h out).inputSymbol = some b := by
      rw [splitPos_read w _ pre.length rfl]
      simp [hw]
    have hstep : (splitEmitTM k).tm.step (splitEmitCfg k w s (some 3) pre.length h out) =
        splitEmitCfg k w s (some 3) (pre ++ [b]).length h (out ++ [b]) := by
      unfold MultiTapeTM.step
      change ((splitEmitTM k).tm.tr (3 : Fin 4) _ _).apply _ = _
      rw [hread]
      refine Cfg.ext rfl ?_ rfl ?_ rfl
      · simpa only [List.length_append, List.length_singleton] using splitPos_succ w pre.length
      · funext i; simp [splitEmitTM, Action.apply, splitEmitCfg]
    simp only [List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step, hstep]
    simpa only [List.append_assoc, List.singleton_append] using
      ih (pre ++ [b]) (out ++ [b]) h (by simpa [List.append_assoc] using hw)

/-- The accepting emitter produces exactly the encoded native split in
`|s|+|w|+3` steps. Its candidate may contain any bit pattern.
**Proof sketch.** Double exactly the native prefix counted by the candidate,
emit the separator, and copy the remaining native suffix. Concatenate the
three exact runs and cancel the prefix length in the time expression. -/
private lemma splitEmit_run (k : ℕ) (w s : List Bool) (hs : s.length ≤ w.length) :
    (splitEmitTM k).tm.runFrom (splitEmitCfg k w s (some 0) 0 0 [])
      (s.length + w.length + 3) =
      splitEmitCfg k w s none w.length s.length
        (pairEncode (w.take s.length) (w.drop s.length)) := by
  have ht : s.length + w.length + 3 =
      2 * s.length + 2 + ((w.drop s.length).length + 1) := by
    simp only [List.length_drop]; omega
  rw [ht, MultiTapeTM.runFrom_add,
    MultiTapeTM.runFrom_add _ (2 * s.length) 2,
    splitEmit_double k w s hs _ (le_refl _), splitEmit_separator]
  have h := splitEmit_suffix k w s (w.drop s.length) (w.take s.length)
    (((w.take s.length).flatMap fun b => [b, b]) ++ [false, true]) s.length
    (List.take_append_drop s.length w).symm
  simpa [List.length_take, Nat.min_eq_left hs, pairEncode] using h

/-- A single transition is safe when both its endpoints exclude the anchor. -/
private lemma splitSafe_one {k : ℕ} {S : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (anchor : S) (c d : Cfg k Bool S w)
    (he : tm.step c = d) (hc : c.state ≠ some anchor) (hd : d.state ≠ some anchor) :
    tm.runFrom c 1 = d ∧ splitSafe tm anchor c 1 := by
  refine ⟨he, ?_⟩
  intro j hj
  rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
  · exact hc
  · change (tm.step c).state ≠ _
    rw [he]; exact hd

/-- Concatenate two safe exact phase runs. -/
private lemma splitSafe_join {k : ℕ} {S : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (anchor : S) (c d f : Cfg k Bool S w) (u v : ℕ)
    (h1 : tm.runFrom c u = d) (hs1 : splitSafe tm anchor c u)
    (h2 : tm.runFrom d v = f) (hs2 : splitSafe tm anchor d v) :
    tm.runFrom c (u + v) = f ∧ splitSafe tm anchor c (u + v) := by
  refine ⟨by rw [MultiTapeTM.runFrom_add, h1, h2], ?_⟩
  apply splitSafe_add tm anchor c u v hs1
  rw [h1]; exact hs2

/-- A completed source gives a complete body round, including acceptance,
rejection, positive duration, and anchor exclusion over every strict interior
step. The bound explicitly includes all dispatches, rewinds, and emission.
**Proof sketch.** Depart the anchor in one step. Concatenate safe preparation,
counting, decision, and rewind traces. Equality accepts and emits native
slices. Inequality dispatches to the exact scratch restoration, followed by
one explicit return to the anchor. All intermediate states belong to disjoint
phases; the only anchor step is the final rejecting transition. -/
private lemma splitBody_round (M : FinTM Bool) (start : M.State) (w s out : List Bool)
    (T : ℕ) (hT : M.tm.runFrom (splitBank M s (some start) []) T = splitBank M s none out) :
    ∃ t, 0 < t ∧ t ≤ T + 5 * s.length + 3 * w.length + 20 ∧
      (∀ j, 0 < j → j < t →
        ((splitBodyTM M start).tm.runFrom
          (Cfg.ofWords (input := w) .anchor (stateWord (M.k + 1) s)) j).state ≠ some .anchor) ∧
      if decide (s.length + out.length = w.length) then
        ((splitBodyTM M start).tm.runFrom
          (Cfg.ofWords (input := w) .anchor (stateWord (M.k + 1) s)) t).state = none ∧
        ((splitBodyTM M start).tm.runFrom
          (Cfg.ofWords (input := w) .anchor (stateWord (M.k + 1) s)) t).output =
            pairEncode (w.take s.length) (w.drop s.length)
      else (splitBodyTM M start).tm.runFrom
        (Cfg.ofWords (input := w) .anchor (stateWord (M.k + 1) s)) t =
          Cfg.ofWords .anchor (stateWord (M.k + 1) (splitStep w s)) := by
  let tm := (splitBodyTM M start).tm
  let z : Cfg (M.k + 1) Bool (SplitBodyState M.State) w :=
    Cfg.ofWords .anchor (stateWord (M.k + 1) s)
  let p : Cfg (M.k + 1) Bool (SplitBodyState M.State) w :=
    Cfg.ofWords (.prepare (0, false)) (stateWord (M.k + 1) s)
  let d := splitCountCfg SplitBodyState.count SplitBodyState.check w s (splitBank M s none out)
  let ok := decide (s.length + out.length = w.length)
  let c : Cfg (M.k + 1) Bool (Fin 3) w :=
    ⟨some 0, splitPos w (s.length + out.length),
      Fin.cases (bufferTape s) (fun _ => catalogPolyTape (s.length + 1)),
      Fin.cases 0 (fun _ => 0), []⟩
  let r : Cfg (M.k + 1) Bool (SplitBodyState M.State) w :=
    ({c with state := some (2 : Fin 3), inputPos := 1} : Cfg (M.k + 1) Bool (Fin 3) w).mapState
    (SplitBodyState.rewind (S := M.State) ok)
  have hdepart : tm.runFrom z 1 = p := by
    change (controlAction 0 (some (.prepare (0, false)))).apply z = p
    rw [controlAction_apply, moveInputPos_zero]
    rfl
  obtain ⟨a, ha, hprep, hpreps⟩ := splitBody_prepare M start w s
  obtain ⟨b, hb, hcount, hcounts⟩ := splitBody_count M start w s out T hT
  obtain ⟨h1, hs1⟩ := splitSafe_join tm .anchor p _ d (a + 1) b hprep hpreps hcount hcounts
  have hcheck : tm.step d = c.mapState (SplitBodyState.rewind ok) := by
    unfold MultiTapeTM.step
    change (controlAction 0 (some (.rewind
      (!decide (w.length < s.length + out.length) && d.inputSymbol.isNone) 0))).apply d = _
    rw [controlAction_apply, moveInputPos_zero]
    have hok := splitCount_accept SplitBodyState.count SplitBodyState.check w s
      (splitBank M s none out)
    change (!decide (w.length < s.length + out.length) && d.inputSymbol.isNone) = ok at hok
    rw [hok]
    rfl
  obtain ⟨hcheck', hchecks⟩ := splitSafe_one tm .anchor d _ hcheck
    (by simp [d, splitCountCfg, splitBank]) (by simp [c, Cfg.mapState])
  obtain ⟨h2, hs2⟩ := splitSafe_join tm .anchor p d _ (a + 1 + b) 1 h1 hs1 hcheck' hchecks
  obtain ⟨v, hv, hrew, hrews⟩ := splitBody_rewind M start w ok c rfl
  obtain ⟨h3, hs3⟩ := splitSafe_join tm .anchor p _ r (a + 1 + b + 1) v h2 hs2 hrew hrews
  have hv' : v ≤ w.length + 3 := by
    have hp : c.inputPos.val ≤ w.length + 1 := by simp [c, splitPos]
    omega
  by_cases hok : s.length + out.length = w.length
  · have hs : s.length ≤ w.length := by omega
    let ec := splitEmitCfg M.k w s (some 0) 0 0 []
    let ed := splitEmitCfg M.k w s none w.length s.length
      (pairEncode (w.take s.length) (w.drop s.length))
    have hdispatch : tm.step r = ec.mapState SplitBodyState.emit := by
      simp only [r, c, Cfg.mapState, Option.map_some, MultiTapeTM.step,
        tm, splitBodyTM, ↓reduceIte, ok, hok, decide_true]
      rw [controlAction_apply, moveInputPos_zero]
      refine Cfg.ext rfl ?_ rfl rfl rfl
      simp [ec, splitEmitCfg, splitPos]
    obtain ⟨hd, hds⟩ := splitSafe_one tm .anchor r _ hdispatch
      (by simp [r, Cfg.mapState]) (by simp [ec, Cfg.mapState, splitEmitCfg])
    obtain ⟨h4, hs4⟩ := splitSafe_join tm .anchor p r _ (a + 1 + b + 1 + v) 1 h3 hs3 hd hds
    have hemit : tm.runFrom (ec.mapState SplitBodyState.emit) (s.length + w.length + 3) =
        ed.mapState SplitBodyState.emit := by
      rw [splitEmbed_run (splitEmitTM M.k).tm tm SplitBodyState.emit (fun _ _ _ => rfl)]
      exact congrArg (Cfg.mapState SplitBodyState.emit) (splitEmit_run M.k w s hs)
    have hemits : splitSafe tm .anchor (ec.mapState SplitBodyState.emit) (s.length + w.length + 3) := by
      intro j hj
      rw [splitEmbed_run (splitEmitTM M.k).tm tm SplitBodyState.emit (fun _ _ _ => rfl)]
      cases hq : ((splitEmitTM M.k).tm.runFrom ec j).state <;> simp [Cfg.mapState, hq]
    obtain ⟨h5, hs5⟩ := splitSafe_join tm .anchor p _ _ (a + 1 + b + 1 + v + 1)
      (s.length + w.length + 3) h4 hs4 hemit hemits
    let u := a + 1 + b + 1 + v + 1 + (s.length + w.length + 3)
    have hend : tm.runFrom z (1 + u) = ed.mapState SplitBodyState.emit := by
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
  · let rc := (splitRestoreScan M.k w s 0).mapState (SplitBodyState.restore (S := M.State))
    have hdispatch : tm.step r = rc := by
      simp only [r, c, Cfg.mapState, Option.map_some, MultiTapeTM.step,
        tm, splitBodyTM, ↓reduceIte, ok, hok, decide_false, Bool.false_eq_true]
      rw [controlAction_apply, moveInputPos_zero]
      refine Cfg.ext ?_ ?_ ?_ ?_ rfl
      · simp [rc, splitRestoreScan, Cfg.mapState]
      · simp [rc, splitRestoreScan, Cfg.mapState, splitPos]
      · funext i
        refine Fin.cases ?_ (fun l => ?_) i
        · rfl
        · funext z; simp [rc, splitRestoreScan, Cfg.mapState, splitScratch, catalogPolyTape]
      · funext i
        refine Fin.cases ?_ (fun l => ?_) i <;> rfl
    obtain ⟨hd, hds⟩ := splitSafe_one tm .anchor r rc hdispatch
      (by simp [r, Cfg.mapState]) (by simp [rc, Cfg.mapState, splitRestoreScan])
    obtain ⟨h4, hs4⟩ := splitSafe_join tm .anchor p r rc (a + 1 + b + 1 + v) 1 h3 hs3 hd hds
    obtain ⟨l, hl, hrest, hrests⟩ := splitBody_restore M start w s
    obtain ⟨h5, hs5⟩ := splitSafe_join tm .anchor p rc _ (a + 1 + b + 1 + v + 1) l h4 hs4 hrest hrests
    let u := a + 1 + b + 1 + v + 1 + l
    have hreturn : tm.step (Cfg.ofWords (.restore (4, false)) (stateWord (M.k + 1) (splitStep w s))) =
        Cfg.ofWords (input := w) .anchor (stateWord (M.k + 1) (splitStep w s)) := by
      change (controlAction 0 (some (SplitBodyState.anchor (S := M.State)))).apply _ = _
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
private lemma splitSolve_of_body (C e : ℕ) (body : FinTM Bool) (anchor : body.State)
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
        if splitAccept C e w s then
          (body.tm.runFrom (Cfg.ofWords (input := w) anchor (stateWord body.k s)) t).state = none ∧
          (body.tm.runFrom (Cfg.ofWords (input := w) anchor (stateWord body.k s)) t).output =
            pairEncode (w.take s.length) (w.drop s.length)
        else
          body.tm.runFrom (Cfg.ofWords (input := w) anchor (stateWord body.k s)) t =
            Cfg.ofWords anchor (stateWord body.k (splitStep w s))) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun w => match solveSplit C e w.length with
          | some i => pairEncode (w.take i) (w.drop i)
          | none => []) (fun n => c * (n + 1) ^ (e + 2)) := by
  obtain ⟨F, a, hF⟩ := computesFunInTime_lengthBits
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
  obtain ⟨M, c, hM⟩ := exists_loopFindTM body F anchor
    (fun w s => s.length ≤ w.length + 1) splitStep (splitAccept C e)
    (fun w s => pairEncode (w.take s.length) (w.drop s.length)) (fun _ => [])
    id (fun n => (A + a) * (n + 1) ^ (e + 1)) hF'
    (by intro w; simp) splitStep_inv
    (by
      intro w
      obtain ⟨t, ht, hi, hh⟩ := hstart w
      exact ⟨t, ht.trans (hbody w.length), hi, hh⟩)
    (by
      intro w s hs
      obtain ⟨t, htpos, ht, hi, hh⟩ := hround w s hs
      exact ⟨t, htpos, ht.trans (hbody w.length), hi, hh⟩)
  refine ⟨M, 2 * c * (A + a + 1), fun w => ?_⟩
  have hm := hM w
  dsimp only [id_eq] at hm
  convert hm.mono (splitLoop_bound c (A + a) e w.length) using 1
  exact (splitLoop_result C e w).symm

/-- The positive-exponent source is the already proved nested-loop phase,
started on the prepared bank rather than rerunning input initialization. -/
private lemma splitSource_poly (c C : ℕ) (s : List Bool) :
    (catalogPolyUnaryTM c C).tm.runFrom
      (splitBank (catalogPolyUnaryTM c C) s (some (.loop (Fin.last c))) [])
      (catalogPolyCost (s.length + 1) C (c + 1) + 1) =
      splitBank (catalogPolyUnaryTM c C) s none
        (List.replicate (C * (s.length + 1) ^ (c + 1)) true) := by
  simpa [splitBank, catalogPolyCfg] using splitPoly_loop_end c C (s.length + 1) (by omega)

/-- Exponent zero uses the fixed prefix source on empty virtual input, with
no scratch tapes. Its last blank-reading step is included in the bound. -/
private lemma splitSource_constant (C : ℕ) (s : List Bool) :
    (catalogPrefixTM (List.replicate C true)).tm.runFrom
      (splitBank (catalogPrefixTM (List.replicate C true)) s (some (0 : Fin ((List.replicate C true).length + 1))) []) (C + 1) =
      splitBank (catalogPrefixTM (List.replicate C true)) s none (List.replicate C true) := by
  have hi : splitBank (catalogPrefixTM (List.replicate C true)) s (some (0 : Fin ((List.replicate C true).length + 1))) [] =
      (catalogPrefixTM (List.replicate C true)).tm.initCfg [] := by
    apply Cfg.ext_zero_tapes <;> rfl
  rw [hi, MultiTapeTM.runFrom_succ_eq_step']
  have he := catalogPrefixTM_emit (List.replicate C true) [] C (by simp)
  rw [he]
  simp only [List.take_replicate, Nat.min_self]
  apply Cfg.ext_zero_tapes <;>
    simp [MultiTapeTM.step, catalogPrefixTM, catalogPrefixCfg, Cfg.inputSymbol,
      Fin.ext_iff, Action.apply, splitBank]

/-- The invariant bounds every candidate, including the one-past-end stall,
inside one common body envelope. The factor `2^e` covers the prepared side
length `|s|+1 ≤ 2(|w|+1)` without increasing the exponent.
**Proof sketch.** Bound the source by its proved box cost, compare the two
side lengths, and absorb all linear controller overhead into forty copies of
the positive polynomial envelope. -/
private lemma splitBody_envelope (C e l n T : ℕ) (hl : l ≤ n + 1)
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
private lemma splitSolve_source (C e : ℕ) (M : FinTM Bool) (start : M.State)
    (B : ℕ → ℕ)
    (hsource : ∀ s : List Bool, M.tm.runFrom (splitBank M s (some start) []) (B s.length) =
      splitBank M s none (List.replicate (C * (s.length + 1) ^ e) true))
    (hbound : ∀ l, B l ≤ (C + 1 + 5 * e) * (l + 1) ^ e + 1) :
    ∃ (N : FinTM Bool) (c : ℕ),
      N.ComputesFunInTime
        (fun w => match solveSplit C e w.length with
          | some i => pairEncode (w.take i) (w.drop i)
          | none => []) (fun n => c * (n + 1) ^ (e + 2)) := by
  apply splitSolve_of_body C e (splitBodyTM M start) .anchor
    ((C + 1 + 5 * e) * 2 ^ e + 40)
  · intro w
    refine ⟨0, Nat.zero_le _, ?_, ?_⟩
    · intro j hj; omega
    · exact splitBody_start M start w
  · intro w s hs
    obtain ⟨t, htpos, ht, hsafe, hend⟩ := splitBody_round M start w s
      (List.replicate (C * (s.length + 1) ^ e) true) (B s.length) (hsource s)
    refine ⟨t, htpos, ht.trans (splitBody_envelope C e s.length w.length (B s.length)
      hs (hbound s.length)), hsafe, ?_⟩
    simpa only [splitAccept, List.length_replicate] using hend

/-- Close the two exponent cases privately, so compiler-generated proof
helpers also remain private. Both cases instantiate the concrete body and
its proved round contract through the exact source interfaces. -/
private lemma splitSolve_closed (C e : ℕ) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun w => match solveSplit C e w.length with
          | some i => pairEncode (w.take i) (w.drop i)
          | none => [])
        fun n => c * (n + 1) ^ (e + 2) := by
  cases e with
  | zero =>
    apply splitSolve_source C 0 (catalogPrefixTM (List.replicate C true))
      (0 : Fin ((List.replicate C true).length + 1)) (fun _ => C + 1)
    · intro s
      simpa using splitSource_constant C s
    · intro l; simp
  | succ e =>
    apply splitSolve_source C (e + 1) (catalogPolyUnaryTM e C) (.loop (Fin.last e))
      (fun l => catalogPolyCost (l + 1) C (e + 1) + 1)
    · exact splitSource_poly e C
    · intro l
      exact Nat.add_le_add_right (catalogPolyCost_le (l + 1) C (by omega) (e + 1)) 1

/-- **P10, padding split search** (spec, fill pending — new; the bounded
search both padding constructions perform, realizable as a
`Turing.FinTM.exists_loopFindTM` instance over the polynomial-evaluation
primitive — the decision loop returns only a Boolean and cannot carry the
split). Search for the unique `i ≤ |w|` with `i + C·(i+1)^e = |w|`
(`Turing.solveSplit`); on success emit the threaded split
`pairEncode (w.take i) (w.drop i)`, and on failure `[]` — rejection when
no length-equation solution exists is the audited obligation.

**Construction sketch** (round 2: an `exists_loopFindTM` instance — the
decision loop exposes only a Boolean and cannot carry the payload,
round-1 finding 3; the narrowing from the catalog's supplied-predicate
search to this fixed length-equation search is recorded in
`machine-library-design.md` §9b). Instance data: round state
`s = List.replicate i true`, the candidate in unary;
`Inv w s := s.length ≤ w.length + 1`;
`stepF w s := if s.length ≤ w.length then s ++ [true] else s` (stall past
the end keeps the invariant step-closed); `acceptF w s` holds iff
`s.length + C·(s.length + 1)^e = w.length`, evaluated by the polynomial
loop and a countdown compare;
`out w s := pairEncode (w.take s.length) (w.drop s.length)` — always
nonempty, so success is distinguishable from the `[]` exhaustion; fuel
`R n := n`, so the orbit is exactly the candidates `0, …, n` and
`List.range.find?` returns the least solution, which strict monotonicity
of `i ↦ i + C·(i+1)^e` makes unique — `Turing.solveSplit`'s own
semantics. -/
theorem computesFunInTime_splitSolve (C e : ℕ) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun w => match solveSplit C e w.length with
          | some i => pairEncode (w.take i) (w.drop i)
          | none => [])
        fun n => c * (n + 1) ^ (e + 2) := by
  exact splitSolve_closed C e

/-- **P11, fixed-width increment** (spec, fill pending — harvest: the
enumerator batch's `enumCarryTM`/`enumCarry_correct`, proved with cost at
most twice the width plus two). The little-endian fixed-width successor
(`Turing.incFixed`), with `[]` on overflow, is computable in linear time.
The in-place form of the same carry loop is the loop combinator's fuel
counter.

**Construction sketch.** Two passes: the first scan detects overflow (all
trues) — nothing may be emitted while that is unknown; on a live word the
second pass emits falses over the carry prefix, a true at the first false,
and the remainder verbatim. The harvest source's in-place variant costs at
most twice the width plus two. -/
theorem computesFunInTime_incFixed :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => (incFixed x).getD []) fun n => c * (n + 1) := by
  exact ⟨incFixedTM, 3, incFixed_computes⟩

end Turing.FinTM


## ===== TCSlib/Complexity/TuringMachine/Configuration.lean =====

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


## ===== TCSlib/Complexity/TuringMachine/Deterministic.lean =====

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
* added the repository-standard `set_option` header.
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
(including [AB09]) only consider the number of cells that contain
a non-blank symbol at some point in the execution or the number of cells written to. This allows
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


## ===== TCSlib/Complexity/TuringMachine/Finite.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Fintype.Basic
import TCSlib.Complexity.TuringMachine.Deterministic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Bundled finite Turing machines

The raw model `Turing.MultiTapeTM k Symbol State` deliberately does not require `Symbol` or
`State` to be finite: semantics, simulations, and resource counting do not need it, and
compound state types arise freely in constructions. Finiteness is nevertheless
mathematically essential for complexity theory — with infinitely many states a machine can
memorize its whole input in the state and decide any language in linear time, and an
infinite transition table has no string encoding.

This file provides the bundled layer `Turing.FinTM`: a machine together with `Fintype` and
`DecidableEq` instances for its state type. All headline definitions of the Chapter 1
development (`DTIME`, `P`, machine encodings, the universal machine) are stated exclusively
over `FinTM`, so the finiteness hypothesis can never be dropped by accident. The instances
are carried as *data* (not `Finite` propositions) because the machine-encoding function
`⌞M⌟` must enumerate the transition table.

The alphabet parameter `Symbol` stays explicit and unbundled: the Chapter 1 headline
definitions fix `Symbol := Bool` (see `TCSlib.Complexity.ClassP.DTIME`), and results that
need a finite alphabet for a general `Symbol` take `[Fintype Symbol]` hypotheses at use
sites.

## Main definitions

* `Turing.FinTM Symbol` — a multi-tape TM over alphabet `Option Symbol` with a bundled
  finite state type. [AB09, §1.2]
* `Turing.FinTM.ComputesInTime` — the machine halts on `input` within `t` steps with
  `output` on the output tape (time-only variant of
  `Turing.MultiTapeTM.ComputesInTimeAndSpace`). [AB09, Definition 1.3]
* `Turing.FinTM.ComputesFunInTime` — the machine computes `f` in time `T`.
  [AB09, Definition 1.3]
* `Turing.FinTM.Computes` — the machine computes `f` with no time constraint; the
  notion of computability underlying the uncomputability results. [AB09, §1.4, p. 20]

## Main results

* `Turing.FinTM.ComputesInTime.mono` — halting is absorbing, so the time bound can be
  weakened.
* `Turing.FinTM.ComputesInTime.output_unique` — determinism: a machine has at most one
  completed output on a given input.
* `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.Computes.exists_computesInTime_iff` —
  the space-free unfolding of a timed computation, and the completed-output
  characterization of a total machine (promoted from the epoch-1 fill).
* `Turing.FinTM.not_computesInTime_zero` — no machine computes anything in zero steps
  (the initial state is not the halting state).
* `Turing.MultiTapeTM.output_length_le`, `Turing.MultiTapeTM.output_prefix` — raw-layer
  output lemmas (at most one symbol is emitted per step, and output only grows), stated
  here rather than in the vendored `Deterministic.lean` to keep the vendored files
  unmodified.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2, §1.3.)
-/

namespace Turing

/-!
### Raw-layer output lemmas

Additions on top of the vendored files (kept here so the vendored `Deterministic.lean`
stays byte-comparable with upstream).
-/

namespace MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- The output of an initialized run after `t` steps has length at most `t`: each step
appends at most one symbol.

**Proof sketch.** Induction on `t` with `Turing.MultiTapeTM.runFrom_succ_eq_step'` and
`Turing.MultiTapeTM.step_output` (`Option.toList` has length at most one); the initial
output is `[]`. -/
theorem output_length_le (tm : MultiTapeTM k Symbol State) (input : List Symbol) (t : ℕ) :
    ((tm.runFrom (tm.initCfg input) t).output).length ≤ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.step_output]
    have hone : (tm.outputSymbol (tm.runFrom (tm.initCfg input) t)).toList.length ≤ 1 := by
      cases tm.outputSymbol (tm.runFrom (tm.initCfg input) t) <;> simp
    simp only [List.length_append]
    omega

/-- Output is monotone along a run: the output at an earlier time is a prefix of the
output at any later time.

**Proof sketch.** It suffices to treat one step (`Turing.MultiTapeTM.step_output`: a
step appends), then induct on the difference using
`Turing.MultiTapeTM.runFrom_add` and transitivity of `List.IsPrefix`. -/
theorem output_prefix (tm : MultiTapeTM k Symbol State) (cfg : Cfg k Symbol State input)
    {t t' : ℕ} (h : t ≤ t') :
    (tm.runFrom cfg t).output <+: (tm.runFrom cfg t').output := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  rw [MultiTapeTM.runFrom_add]
  generalize tm.runFrom cfg t = c
  induction d with
  | zero => simp
  | succ d ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.step_output]
    exact ih.trans (List.prefix_append _ _)

end MultiTapeTM

/-- A multi-tape Turing machine over the alphabet `Option Symbol` bundled with a finite
state type. This is the machine of [AB09, §1.2] up to the declared model variations
(append-only output tape, start-marker-free initialization — see the deviations list in
`TCSlib.Complexity.ClassP.DTIME`): the raw `MultiTapeTM` is internal plumbing, and
every headline complexity-theoretic definition is stated over `FinTM`.

The instances are data (`Fintype`/`DecidableEq`, not `Finite`) because encoding a machine
as a string requires enumerating its transition table. -/
structure FinTM (Symbol : Type) : Type 1 where
  /-- number of work tapes -/
  k : ℕ
  /-- the state type -/
  State : Type
  /-- the state type is finite, as data -/
  [fintypeState : Fintype State]
  /-- states are decidably discernible, needed to tabulate the transition function -/
  [decEqState : DecidableEq State]
  /-- the underlying machine -/
  tm : MultiTapeTM k Symbol State

namespace FinTM

attribute [instance] FinTM.fintypeState FinTM.decEqState

variable {Symbol : Type}

/-- The machine `M` halts on `input` within `t` steps with `output` written on its output
tape. Time-only variant of `Turing.MultiTapeTM.ComputesInTimeAndSpace` (the space used is
existentially discarded). [AB09, Definition 1.3] -/
def ComputesInTime (M : FinTM Symbol) (input output : List Symbol) (t : ℕ) : Prop :=
  ∃ s, M.tm.ComputesInTimeAndSpace input output t s

/-- The machine `M` computes the string function `f`, halting within `T |input|` steps on
every input. [AB09, Definition 1.3: "M computes f in T(n)-time"] -/
def ComputesFunInTime (M : FinTM Symbol) (f : List Symbol → List Symbol) (T : ℕ → ℕ) : Prop :=
  ∀ input : List Symbol, M.ComputesInTime input (f input) (T input.length)

/-- The machine `M`, over alphabet `Γ`, computes the string function `f` on `α`-strings
*via* the symbol embedding `e : α ↪ Γ`: on every input `x.map e` it halts within
`T |x|` steps with `(f x).map e` on its output tape. This is how a machine over a
larger alphabet is said to compute a function on a smaller one; it is the interface of
the alphabet-robustness results [AB09, §1.3.1]. -/
def ComputesFunInTimeVia {α Γ : Type} (M : FinTM Γ) (e : α ↪ Γ)
    (f : List α → List α) (T : ℕ → ℕ) : Prop :=
  ∀ x : List α, M.ComputesInTime (x.map e) ((f x).map e) (T x.length)

/-- The machine `M` *computes* the string function `f`, with no time constraint: on
every input it eventually halts with `f input` on the output tape. This is the notion
of computability underlying the uncomputability results [AB09, §1.4, p. 20; §1.5];
`Turing.FinTM.ComputesFunInTime` is the time-bounded refinement, and the two are
related by `Turing.FinTM.ComputesFunInTime.computes` (below) and
`Turing.FinTM.Computes.exists_computesFunInTime`
(in `TCSlib.Complexity.Uncomputability.Computable`). -/
def Computes (M : FinTM Symbol) (f : List Symbol → List Symbol) : Prop :=
  ∀ input : List Symbol, ∃ t, M.ComputesInTime input (f input) t

/-- Halting is absorbing, so a time bound can be weakened: if `M` produces `output`
within `t` steps it also does so within any `t' ≥ t` steps.

**Proof sketch.** By `Turing.MultiTapeTM.runFrom_add` the run to step `t'` factors through
step `t`; the state there is `none`, so `Turing.MultiTapeTM.runFrom_of_halt` shows the
configuration no longer changes, and in particular state and output at step `t'` agree with
step `t`. The space used up to step `t'` exists (it is whatever `spaceUsed` evaluates to),
which discharges the existential. -/
theorem ComputesInTime.mono {M : FinTM Symbol} {input output : List Symbol} {t t' : ℕ}
    (h : M.ComputesInTime input output t) (hle : t ≤ t') :
    M.ComputesInTime input output t' := by
  simp only [ComputesInTime, MultiTapeTM.ComputesInTimeAndSpace] at h ⊢
  obtain ⟨s, hhalt, hout, -⟩ := h
  have hrun : M.tm.runFrom (M.tm.initCfg input) t' = M.tm.runFrom (M.tm.initCfg input) t := by
    conv_lhs => rw [← Nat.add_sub_cancel' hle]
    rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hhalt]
  exact ⟨_, by rw [hrun]; exact hhalt, by rw [hrun]; exact hout, rfl⟩

/-- No machine computes anything in zero steps: the initial configuration is in the
initial state, which is not the halting state. In particular a time budget of `0`
(e.g. from a vanishing time bound) is never satisfiable. -/
theorem not_computesInTime_zero (M : FinTM Symbol) (input output : List Symbol) :
    ¬M.ComputesInTime input output 0 := by
  rintro ⟨s, hhalt, -⟩
  simp [MultiTapeTM.runFrom_zero] at hhalt

/-- Determinism of completed outputs: a machine has at most one completed output on a
given input — if `M` halts on `input` with `w` within `t` steps and with `w'` within
`t'` steps, then `w = w'`. Together with `Turing.FinTM.ComputesInTime.mono` this
makes the halting relation of a machine a partial function.

**Proof.** Absorb both computations to time `max t t'`
(`Turing.FinTM.ComputesInTime.mono`); both then name the output of one and the same
run. -/
theorem ComputesInTime.output_unique {M : FinTM Symbol} {input w w' : List Symbol}
    {t t' : ℕ} (h : M.ComputesInTime input w t) (h' : M.ComputesInTime input w' t') :
    w = w' := by
  have h₁ := h.mono (Nat.le_max_left t t')
  have h₂ := h'.mono (Nat.le_max_right t t')
  simp only [ComputesInTime, MultiTapeTM.ComputesInTimeAndSpace] at h₁ h₂
  obtain ⟨s, -, hout, -⟩ := h₁
  obtain ⟨s', -, hout', -⟩ := h₂
  rw [← hout, ← hout']

/-- A time-bounded computation is in particular a computation. -/
theorem ComputesFunInTime.computes {M : FinTM Symbol} {f : List Symbol → List Symbol}
    {T : ℕ → ℕ} (h : M.ComputesFunInTime f T) : M.Computes f :=
  fun input => ⟨T input.length, h input⟩

/-- `ComputesInTime` without the space witness: the machine has halted by time `t`
with completed output exactly `w`. The space existential is uniquely determined by
the run, so it can always be discharged. (Promoted from the epoch-1 fill and
generalized from `Bool` to an arbitrary alphabet, per the epoch-1 audit,
finding 4.) -/
theorem computesInTime_iff (M : FinTM Symbol) (x w : List Symbol) (t : ℕ) :
    M.ComputesInTime x w t ↔
      (M.tm.runFrom (M.tm.initCfg x) t).state = none ∧
      (M.tm.runFrom (M.tm.initCfg x) t).output = w := by
  constructor
  · rintro ⟨s, hs, ho, -⟩
    exact ⟨hs, ho⟩
  · rintro ⟨hs, ho⟩
    exact ⟨_, hs, ho, rfl⟩

/-- A total machine's completed outputs are exactly its prescribed values: if `M`
computes `g`, then `M` halts on `x` with completed output `w` — in some number of
steps — iff `w = g x`. Existence of a computation together with determinism of
completed outputs (`Turing.FinTM.ComputesInTime.output_unique`). (Promoted from
the epoch-1 fill per the epoch-1 audit, finding 4.) -/
theorem Computes.exists_computesInTime_iff {M : FinTM Symbol}
    {g : List Symbol → List Symbol} (hM : M.Computes g) (x w : List Symbol) :
    (∃ t, M.ComputesInTime x w t) ↔ w = g x := by
  obtain ⟨t, ht⟩ := hM x
  constructor
  · rintro ⟨s, hs⟩
    exact hs.output_unique ht
  · rintro rfl
    exact ⟨t, ht⟩

end FinTM

end Turing


## ===== TCSlib/Complexity/TuringMachine/Simulation.lean =====

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


## ===== TCSlib/Complexity/TuringMachine/Sweep.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Tactic.Ring
import Mathlib.Data.List.FinRange
import TCSlib.Complexity.TuringMachine.Finite

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Sweep gadgets

The generic zipper/transduction layer for sweep-based tape simulations,
promoted out of the one-work-tape construction at the epoch-2/epoch-3
boundary per the epoch-2 audit's promotion recommendations 2-4 (statements
preserved verbatim; only the `private` modifiers were removed). The
controller-specific representations of that construction (its cell type,
alphabet, and finite control) deliberately stay private in
`TCSlib.Complexity.TuringMachine.Robustness.SingleTape`.

## Contents

* **Tape zippers** (`Turing.FinTM.sweepTape`, `sweepCfg`, `sweepRevCfg`, with
  their read/write/turn identities and the beyond-the-zone variants): a finite
  window of a work tape as two stacks around a frontier, scanned in either
  direction, with arbitrary inactive native input and output.
* **Finite transductions** (`Turing.FinTM.sweepFold`, `sweep_run`,
  `sweep_run_reverse`, `sweepFold_append`, `sweep_generate`): a local
  transition-table hypothesis realizes a complete sweep at exact cost, in
  either direction, returning the full resulting configuration.
* **Indexed transducers** (`Turing.FinTM.indexedVisit`, `indexedFold`, and the
  forward/reverse complete-block specializations): a table-valued control that
  changes only the entry named by each cell. The `Nodup` hypothesis of
  `indexedFold` is load-bearing (epoch-2 audit, recommendation 4): two visits
  to the same index could change the control twice.
* **Source bounds** (`Turing.FinTM.source_bounds`): on an initialized run,
  every work head lies in `[-t, t]` at time `t` and every cell outside that
  interval is blank. Initialized runs only — not asserted for arbitrary
  starting configurations (epoch-2 audit, recommendation 2).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.3, Claim 1.6 — the simulation these
  gadgets were built for; the module itself is internal infrastructure.)
-/

namespace Turing.FinTM

/-- A finite tape zipper; the left list is stored nearest-cell first. -/
def sweepTape {A : Type} (z : ℤ) (l r : List (Option A))
    (p : ℤ) : Option A :=
  if p < z then (l[(z - 1 - p).toNat]?).join else (r[(p - z).toNat]?).join

/-- Read the current cell of a zipper. -/
lemma sweepTape_read {A : Type} (z : ℤ) (l r : List (Option A)) :
    sweepTape z l r z = r.head?.join := by
  simp only [sweepTape, lt_self_iff_false, ↓reduceIte, sub_self, Int.toNat_zero]
  cases r <;> rfl

/-- A write followed by a right move transfers one cell to the left stack.
**Proof sketch.** At the written coordinate both sides read the new symbol.
Strictly to its left or right, the old and new list indices differ by one,
exactly compensating for the cons or tail operation. -/
lemma sweepTape_right {A : Type} (z : ℤ) (l r : List (Option A))
    (a b : Option A) :
    Function.update (sweepTape z l (a :: r)) z b =
      sweepTape (z + 1) (b :: l) r := by
  funext p
  by_cases hp : p = z
  · subst p
    simp [sweepTape]
  · rw [Function.update_of_ne hp]
    by_cases h : p < z
    · have h' : p < z + 1 := by omega
      have he : (z + 1 - 1 - p).toNat = (z - 1 - p).toNat + 1 := by omega
      simp only [sweepTape, if_pos h, if_pos h', he, List.getElem?_cons_succ]
    · have h' : ¬p < z + 1 := by omega
      have he : (p - z).toNat = (p - (z + 1)).toNat + 1 := by omega
      simp only [sweepTape, if_neg h, if_neg h', he, List.getElem?_cons_succ]

/-- A configuration at a sweep frontier, with arbitrary native input and output. -/
def sweepCfg {A S : Type} {x : List A} (q : Option S)
    (p : Fin (x.length + 2)) (z : ℤ) (l r : List (Option A)) (out : List A) :
    Cfg 1 A S x := ⟨q, p, fun _ => sweepTape z l r, fun _ => z, out⟩

/-- A sweep's local write, with the native input and output left stationary. -/
def sweepAct {A S : Type} (q : S) (a : Option A) (d : SignType) :
    Action 1 A S := ⟨0, fun _ => (some a, d), none, some q⟩

/-- The one-cell tape identity lifts to configurations. -/
lemma sweepCfg_right {A S : Type} {x : List A} (q : Option S) (q' : S)
    (p : Fin (x.length + 2)) (z : ℤ) (l r : List (Option A)) (out : List A)
    (a b : Option A) :
    (sweepAct q' b .pos).apply (sweepCfg q p z l (a :: r) out) =
      sweepCfg (some q') p (z + 1) (b :: l) r out := by
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ ?_
  · funext i
    exact sweepTape_right z l r a b
  · funext i
    rfl
  · exact List.append_nil _

/-- A finite-state left-to-right transduction, recording both its final state
and its rewritten word. -/
def sweepFold {R C : Type} (visit : R → C → R × C) (s : R) :
    List C → R × List C
  | [] => (s, [])
  | a :: as =>
    let v := visit s a
    let rest := sweepFold visit v.1 as
    (rest.1, v.2 :: rest.2)

/-- A local transition rule realizes a complete finite forward sweep.
**Proof sketch.** Induct on the unprocessed word. One machine step writes the
transduced first cell and moves it to the reversed left stack; the induction
hypothesis processes the tail. Input position and output are preserved at every
step, and the number of transitions is exactly the word length. -/
lemma sweep_run {A S R C : Type} (tm : MultiTapeTM 1 A S)
    (state : R → S) (symbol : C → A) (visit : R → C → R × C)
    (htr : ∀ s a inp, tm.tr (state s) inp (fun _ => some (symbol a)) =
      sweepAct (state (visit s a).1) (some (symbol (visit s a).2)) .pos)
    {x : List A} (p : Fin (x.length + 2)) (out : List A)
    (as : List C) (s : R) (z : ℤ) (l r : List (Option A)) :
    tm.runFrom (sweepCfg (some (state s)) p z l
      (as.map (fun a => some (symbol a)) ++ r) out) as.length =
    sweepCfg (some (state (sweepFold visit s as).1)) p (z + as.length)
      (((sweepFold visit s as).2.map (fun a => some (symbol a))).reverse ++ l) r out := by
  induction as generalizing s z l with
  | nil => simp only [List.map_nil, List.nil_append, List.length_nil,
      MultiTapeTM.runFrom_zero, sweepFold, Int.natCast_zero, add_zero, List.reverse_nil]
  | cons a as ih =>
    simp only [List.map_cons, List.cons_append, List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hr : (sweepCfg (some (state s)) p z l
        (some (symbol a) :: (as.map (fun a => some (symbol a)) ++ r)) out).workTapeSymbols =
        fun _ => some (symbol a) := by
      funext i
      exact sweepTape_read z l _
    change tm.runFrom ((tm.tr (state s) _ _).apply _) as.length = _
    rw [hr, htr]
    rw [sweepCfg_right, ih]
    simp only [sweepFold, List.map_cons, List.reverse_cons, List.append_assoc,
      List.cons_append, List.nil_append, Int.natCast_add, Int.natCast_one]
    congr 1
    omega

/-- The same zipper viewed while scanning toward decreasing coordinates. -/
def sweepRevCfg {A S : Type} {x : List A} (q : Option S)
    (p : Fin (x.length + 2)) (z : ℤ) (l r : List (Option A)) (out : List A) :
    Cfg 1 A S x :=
  ⟨q, p, fun _ w => sweepTape (-z) l r (-w), fun _ => z, out⟩

/-- Reflection converts the forward zipper identity into a left-moving step. -/
lemma sweepRevCfg_left {A S : Type} {x : List A} (q : Option S) (q' : S)
    (p : Fin (x.length + 2)) (z : ℤ) (l r : List (Option A)) (out : List A)
    (a b : Option A) :
    (sweepAct q' b .neg).apply (sweepRevCfg q p z l (a :: r) out) =
      sweepRevCfg (some q') p (z - 1) (b :: l) r out := by
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ ?_
  · funext i w
    have h := congrFun (sweepTape_right (-z) l r a b) (-w)
    have he : -(z - 1) = -z + 1 := by omega
    change Function.update (fun w => sweepTape (-z) l (a :: r) (-w)) z b w =
      sweepTape (-(z - 1)) (b :: l) r (-w)
    simpa only [Function.update_apply, neg_inj, he] using h
  · funext i
    rfl
  · exact List.append_nil _

/-- The finite transduction lemma for the return sweep, with the exact cost. -/
lemma sweep_run_reverse {A S R C : Type} (tm : MultiTapeTM 1 A S)
    (state : R → S) (symbol : C → A) (visit : R → C → R × C)
    (htr : ∀ s a inp, tm.tr (state s) inp (fun _ => some (symbol a)) =
      sweepAct (state (visit s a).1) (some (symbol (visit s a).2)) .neg)
    {x : List A} (p : Fin (x.length + 2)) (out : List A)
    (as : List C) (s : R) (z : ℤ) (l r : List (Option A)) :
    tm.runFrom (sweepRevCfg (some (state s)) p z l
      (as.map (fun a => some (symbol a)) ++ r) out) as.length =
    sweepRevCfg (some (state (sweepFold visit s as).1)) p (z - as.length)
      (((sweepFold visit s as).2.map (fun a => some (symbol a))).reverse ++ l) r out := by
  induction as generalizing s z l with
  | nil => simp only [List.map_nil, List.nil_append, List.length_nil,
      MultiTapeTM.runFrom_zero, sweepFold, Int.natCast_zero, sub_zero, List.reverse_nil]
  | cons a as ih =>
    simp only [List.map_cons, List.cons_append, List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hr : (sweepRevCfg (some (state s)) p z l
        (some (symbol a) :: (as.map (fun a => some (symbol a)) ++ r)) out).workTapeSymbols =
        fun _ => some (symbol a) := by
      funext i
      exact sweepTape_read (-z) l _
    change tm.runFrom ((tm.tr (state s) _ _).apply _) as.length = _
    rw [hr, htr, sweepRevCfg_left, ih]
    simp only [sweepFold, List.map_cons, List.reverse_cons, List.append_assoc,
      List.cons_append, List.nil_append, Int.natCast_add, Int.natCast_one]
    congr 1
    omega

/-- Turning round exchanges the two finite stacks. -/
lemma sweepTape_turn {A : Type} (z : ℤ) (l r : List (Option A)) :
    sweepTape z l r = fun w => sweepTape (-(z - 1)) r l (-w) := by
  funext w
  by_cases h : w < z
  · have h' : ¬ -w < -(z - 1) := by omega
    have he : -w - -(z - 1) = z - 1 - w := by omega
    simp only [sweepTape, if_pos h, if_neg h', he]
  · have h' : -w < -(z - 1) := by omega
    have he : -(z - 1) - 1 - -w = w - z := by omega
    simp only [sweepTape, if_neg h, if_pos h', he]

/-- Concatenating two scans threads the finite control between them. -/
lemma sweepFold_append {R C : Type} (visit : R → C → R × C)
    (s : R) (as bs : List C) :
    sweepFold visit s (as ++ bs) =
      let first := sweepFold visit s as
      let second := sweepFold visit first.1 bs
      (second.1, first.2 ++ second.2) := by
  induction as generalizing s with
  | nil => rfl
  | cons a as ih => simp only [List.cons_append, sweepFold, ih]

/-- A transducer whose state is a table, changing only the entry named by a cell. -/
def indexedVisit {I V C : Type} [DecidableEq I]
    (visit : I → V → C → V × C) (s : I → V) (a : I × C) :
    (I → V) × (I × C) :=
  let v := visit a.1 (s a.1) a.2
  (Function.update s a.1 v.1, (a.1, v.2))

/-- On a block with distinct tape indices, each local rule sees the original
table entry. This is the block invariant for both sweeps.
**Proof sketch.** Induct on the index list. The first update does not affect
any remaining index because the list has no duplicates. For the final table,
split an arbitrary queried index into the first index, a tail member, or neither. -/
lemma indexedFold {I V C : Type} [DecidableEq I]
    (visit : I → V → C → V × C) (cell : I → C) (is : List I) (hi : is.Nodup)
    (s : I → V) :
    sweepFold (indexedVisit visit) s (is.map (fun i => (i, cell i))) =
      (fun i => if i ∈ is then (visit i (s i) (cell i)).1 else s i,
        is.map (fun i => (i, (visit i (s i) (cell i)).2))) := by
  induction is generalizing s with
  | nil => simp [sweepFold]
  | cons i is ih =>
    obtain ⟨hin, ht⟩ := List.nodup_cons.mp hi
    simp only [List.map_cons, sweepFold, indexedVisit]
    rw [ih ht]
    apply Prod.ext
    · funext j
      by_cases hj : j = i
      · subst j
        simp [hin]
      · simp only [Function.update_of_ne hj, List.mem_cons]
        by_cases hm : j ∈ is <;> simp [hj, hm]
    · dsimp only
      congr 1
      apply List.map_congr_left
      intro j hj
      have hji : j ≠ i := by rintro rfl; exact hin hj
      simp only [Function.update_of_ne hji]

/-- Each simulated tape contributes exactly one cell to an interleaved block. -/
lemma indexedFold_block {k : ℕ} {V C : Type}
    (visit : Fin k → V → C → V × C) (cell : Fin k → C) (s : Fin k → V) :
    sweepFold (indexedVisit visit) s ((List.finRange k).map (fun i => (i, cell i))) =
      (fun i => (visit i (s i) (cell i)).1,
        (List.finRange k).map (fun i => (i, (visit i (s i) (cell i)).2))) := by
  simpa only [List.mem_finRange, ↓reduceIte] using
    indexedFold visit cell (List.finRange k) (List.nodup_finRange k) s


/-- The return sweep's block rule is valid in reverse tape-index order too. -/
lemma indexedFold_block_reverse {k : ℕ} {V C : Type}
    (visit : Fin k → V → C → V × C) (cell : Fin k → C) (s : Fin k → V) :
    sweepFold (indexedVisit visit) s (((List.finRange k).map (fun i => (i, cell i))).reverse) =
      (fun i => (visit i (s i) (cell i)).1,
        ((List.finRange k).map (fun i => (i, (visit i (s i) (cell i)).2))).reverse) := by
  rw [← List.map_reverse, ← List.map_reverse]
  simpa only [List.mem_reverse, List.mem_finRange, ↓reduceIte] using
    indexedFold visit cell (List.finRange k).reverse
      (by simpa using List.nodup_finRange k) s


/-- One blank cell can be made explicit at the end of the zipper. -/
lemma sweepTape_nil {A : Type} (z : ℤ) (l : List (Option A)) :
    sweepTape z l [] = sweepTape z l [none] := by
  funext p
  unfold sweepTape
  split
  · rfl
  · cases (p - z).toNat <;> rfl

/-- The forward write identity also applies beyond the stored zone. -/
lemma sweepCfg_right_any {A S : Type} {x : List A} (q : Option S) (q' : S)
    (p : Fin (x.length + 2)) (z : ℤ) (l r : List (Option A)) (out : List A)
    (b : Option A) :
    (sweepAct q' b .pos).apply (sweepCfg q p z l r out) =
      sweepCfg (some q') p (z + 1) (b :: l) r.tail out := by
  cases r with
  | cons a r => exact sweepCfg_right q q' p z l r out a b
  | nil =>
    have hc : sweepCfg q p z l ([] : List (Option A)) out =
        sweepCfg q p z l [none] out := by
      refine Cfg.ext rfl rfl ?_ rfl rfl
      funext i
      exact sweepTape_nil z l
    rw [hc]
    exact sweepCfg_right q q' p z l [] out none b

/-- The backward write identity also applies beyond the stored zone. -/
lemma sweepRevCfg_left_any {A S : Type} {x : List A} (q : Option S) (q' : S)
    (p : Fin (x.length + 2)) (z : ℤ) (l r : List (Option A)) (out : List A)
    (b : Option A) :
    (sweepAct q' b .neg).apply (sweepRevCfg q p z l r out) =
      sweepRevCfg (some q') p (z - 1) (b :: l) r.tail out := by
  cases r with
  | cons a r => exact sweepRevCfg_left q q' p z l r out a b
  | nil =>
    have hc : sweepRevCfg q p z l ([] : List (Option A)) out =
        sweepRevCfg q p z l [none] out := by
      refine Cfg.ext rfl rfl ?_ rfl rfl
      funext i w
      exact congrFun (sweepTape_nil (-z) l) (-w)
    rw [hc]
    exact sweepRevCfg_left q q' p z l [] out none b

/-- A fixed finite sequence of writes, in either direction, takes its exact
length. The hypothesis is the local controller rule, and has no global-run premise. -/
lemma sweep_generate {A S : Type} {x : List A}
    (tm : MultiTapeTM 1 A S) (w : List A)
    (cfg : Fin (w.length + 1) → ℤ → List (Option A) → List (Option A) → Cfg 1 A S x)
    (d : ℤ)
    (hstep : ∀ (i : ℕ) (hi : i < w.length) z l r,
      tm.step (cfg ⟨i, by omega⟩ z l r) =
        cfg ⟨i + 1, by omega⟩ (z + d) (some w[i] :: l) r.tail)
    (z : ℤ) (l r : List (Option A)) (n : ℕ) (hn : n ≤ w.length) :
    tm.runFrom (cfg 0 z l r) n =
      cfg ⟨n, by omega⟩ (z + d * n) ((w.take n).map some |>.reverse |>.append l)
        (r.drop n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega), hstep n (by omega)]
    have hz : z + d * n + d = z + d * (n + 1 : ℕ) := by push_cast; ring
    rw [hz, List.take_succ, List.getElem?_eq_getElem (by omega)]
    simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil,
      List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, ← List.drop_one, List.drop_drop]
    rfl


/-- Source heads and nonblank cells stay within the elapsed-time interval.
**Proof sketch.** Heads start at zero and move by at most one per step.
A write can only change the cell under an old head, so it cannot create a
nonblank cell outside the larger interval at the next time. -/
lemma source_bounds {Γ : Type} (M : FinTM Γ) (x : List Γ) (t : ℕ) :
    (∀ i, -(t : ℤ) ≤ (M.tm.runFrom (M.tm.initCfg x) t).workTapePos i ∧
      (M.tm.runFrom (M.tm.initCfg x) t).workTapePos i ≤ t) ∧
    (∀ i z, z < -(t : ℤ) ∨ (t : ℤ) < z →
      (M.tm.runFrom (M.tm.initCfg x) t).workTapes i z = none) := by
  induction t with
  | zero => simp [MultiTapeTM.initCfg, Cfg.init]
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step']
    constructor
    · intro i
      have hp := M.tm.workTapePos_step_le (M.tm.runFrom (M.tm.initCfg x) t) i
      rw [abs_le] at hp
      have := ih.1 i
      push_cast
      omega
    · intro i z hz
      have hz' : z < -(t : ℤ) ∨ (t : ℤ) < z := by omega
      have hne : z ≠ (M.tm.runFrom (M.tm.initCfg x) t).workTapePos i := by
        have := ih.1 i
        omega
      unfold MultiTapeTM.step
      cases hs : (M.tm.runFrom (M.tm.initCfg x) t).state with
      | none => exact ih.2 i z hz'
      | some q =>
        dsimp only [Action.apply]
        cases hw : ((M.tm.tr q (M.tm.runFrom (M.tm.initCfg x) t).inputSymbol
          (M.tm.runFrom (M.tm.initCfg x) t).workTapeSymbols).workTapes i).1
        · exact ih.2 i z hz'
        · dsimp only
          rw [Function.update_of_ne hne]
          exact ih.2 i z hz'

end Turing.FinTM


## ===== TCSlib/Complexity/TuringMachine/Composition.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Order.Monotone.Defs
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option
import TCSlib.Complexity.TuringMachine.Simulation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Composition of Turing machine computations

Basic computability combinators for the bundled machines: the identity and constant
functions are linear-time computable, and time-bounded computability is closed under
composition. Composition is the load-bearing lemma of the whole development — the
universal machine (phase 3) and the `HALT` reduction (phase 4) are built from it — and
it is the part [AB09] never spells out, dispatching it with "high-level descriptions"
of machines. The Isabelle AFP `Cook_Levin` entry spends a large fraction of its effort
exactly here.

## Design

Composition is stated at the *specification* level (`ComputesFunInTime`), not as an
operator on raw machines: the composed machine is existentially produced. Internally
(proof obligation, not API) the construction simulates `M₁` with its emissions
redirected to a fresh work tape, then simulates `M₂` reading that tape in place of its
input tape.

**Convention obligation status** (phase-1 audit finding 4; phase-2 audit finding 3):
this file does *not* formally discharge the append-only vs read-write output-tape
bridge. Every statement here — hypotheses and conclusions alike — lives in the
append-only model, and [AB09]'s read-write-output machine is not formalized in this
development, so no simulation between the two conventions can even be stated yet. The
obligation is recorded in the plan's decision log as **waived**, with the compensating
restriction that no exact-step-count transfer from [AB09] is ever claimed: every bound
*adapted from the source* carries an existential constant (purely internal results,
such as the oracle lockstep lemmas, are legitimately exact but never cross a
convention), and every result is self-contained in-model. A formal bridge (a
read-write-output machine variant plus a simulation theorem) will be added if and only
if a downstream result needs it. What this file *does* provide is the buffer-and-flush
technique — an emission can be deferred to a work tape and flushed at the end — which
is what delayed or revisable output looks like *within this model*; whether the
append-only convention matches [AB09]'s read-write one remains formally unestablished,
per the waiver.

The generic simulation gadgets this file's machines are assembled from — emission
chains, control actions, disjoint tape-block embeddings with their lockstep run
lemmas, the input-head rewind, and the two-machine branch union — live in
`TCSlib.Complexity.TuringMachine.Simulation` (split out at the epoch-1/epoch-2
boundary, per the epoch-1 audit findings 5 and 11 and the policy file-size
standard); this file keeps only its concrete machines and their theorems.

## Main results

* Time-bounded combinators (all over the binary alphabet):
  `Turing.FinTM.computesFunInTime_id`, `Turing.FinTM.computesFunInTime_const`,
  `Turing.FinTM.computesFunInTime_ifEq`, `Turing.FinTM.computesFunInTime_comp`.
* **Partial (guarded) combinators** — the phase-4 API mandated by the phase-3 audit
  (round 2, finding 10 and Argument F: the total-function composition cannot take
  the partially computing universal evaluator as a component):
  `Turing.FinTM.exists_comp_partial` composes two arbitrary machines at the level of
  their halting relations, with the intermediate output buffered on a work tape;
  `Turing.FinTM.exists_cond` branches between two machines on a decided predicate.
  Both are stated untimed; time-bounded refinements are deliberately deferred until
  a result needs them.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2-§1.3; the "high-level description"
  convention on p. 14.)
* [Balbach22] F. J. Balbach, *The Cook-Levin theorem*, Archive of Formal Proofs
  (Isabelle), 2022 — the composition-combinator architecture this file follows in
  spirit.
-/

namespace Turing.FinTM

/-- The one-state copy machine: emits each input bit moving right, and halts on the
boundary blank. -/
private def idTM : FinTM Bool where
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
private lemma idTM_run (x : List Bool) : ∀ t, t ≤ x.length →
    (idTM.tm.runFrom (idTM.tm.initCfg x) t).state = some () ∧
    (((idTM.tm.runFrom (idTM.tm.initCfg x) t).inputPos : ℕ) = t + 1) ∧
    (idTM.tm.runFrom (idTM.tm.initCfg x) t).output = x.take t := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨rfl, ?_, rfl⟩
    simp [MultiTapeTM.runFrom]
  | succ t ih =>
    intro ht
    obtain ⟨hstate, hpos, hout⟩ := ih (Nat.le_of_succ_le ht)
    have hrun1 : idTM.tm.runFrom (idTM.tm.initCfg x) (t + 1) =
        (idTM.tm.tr () (some (x[t]'(by omega)))
          ((idTM.tm.runFrom (idTM.tm.initCfg x) t).workTapeSymbols)).apply
          (idTM.tm.runFrom (idTM.tm.initCfg x) t) := by
      rw [MultiTapeTM.runFrom_succ_eq_step']
      unfold MultiTapeTM.step
      rw [hstate]
      dsimp only
      rw [inputSymbolInner (p := t) (by omega) (by omega)]
    refine ⟨?_, ?_, ?_⟩
    · rw [hrun1]
      simp [idTM, Action.apply]
    · rw [hrun1]
      simp only [idTM, Action.apply]
      rw [moveInputPos_pos_of_ne_right _ (by omega)]
      show ((idTM.tm.runFrom (idTM.tm.initCfg x) t).inputPos : ℕ) + 1 = t + 2
      omega
    · rw [hrun1]
      simp only [idTM, Action.apply]
      rw [hout, List.take_succ, List.getElem?_eq_getElem (by omega)]

/-- The identity function is computable in linear time: the copy machine halts within
`n + 1` steps having emitted its input verbatim (invariant `idTM_run`, then one
halting step on the boundary blank). -/
theorem computesFunInTime_id :
    ∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime id fun n => c * (n + 1) := by
  refine ⟨idTM, 1, fun x => ?_⟩
  obtain ⟨hstate, hpos, hout⟩ := idTM_run x x.length (le_refl _)
  have h0 : (idTM.tm.runFrom (idTM.tm.initCfg x) x.length).inputPos ≠ 0 := by
    intro h
    rw [h] at hpos
    simp at hpos
  have hsym : (idTM.tm.runFrom (idTM.tm.initCfg x) x.length).inputSymbol = none := by
    unfold Cfg.inputSymbol
    rw [dif_neg h0, dif_pos (by omega)]
  have hrun1 : idTM.tm.runFrom (idTM.tm.initCfg x) (x.length + 1) =
      (idTM.tm.tr () none
        ((idTM.tm.runFrom (idTM.tm.initCfg x) x.length).workTapeSymbols)).apply
        (idTM.tm.runFrom (idTM.tm.initCfg x) x.length) := by
    rw [MultiTapeTM.runFrom_succ_eq_step']
    unfold MultiTapeTM.step
    rw [hstate]
    dsimp only
    rw [hsym]
  have hbase : idTM.ComputesInTime x x (x.length + 1) := by
    refine ⟨_, ?_, ?_, rfl⟩
    · rw [hrun1]
      simp [idTM, Action.apply]
    · rw [hrun1]
      simp only [idTM, Action.apply]
      rw [hout]
      simp
  exact hbase.mono (le_of_eq (one_mul _).symm)

/-- The zero-work-tape machine whose states form the emission chain for `w`. -/
private def constTM (w : List Bool) : FinTM Bool where
  k := 0
  State := Fin (w.length + 1)
  tm := { q₀ := 0, tr := fun i _ _ => emitAction w id i }

/-- Every constant function is computable in linear time (in fact in time `|w| + 1`,
which the stated bound dominates once `c ≥ |w| + 1`).

**Proof sketch.** A zero-work-tape machine with `|w| + 1` states `s₀, …, s_{|w|}`:
state `sᵢ` emits the `i`-th symbol of `w` and moves to `s_{i+1}`, ignoring the input;
`s_{|w|}` halts. -/
theorem computesFunInTime_const (w : List Bool) :
    ∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime (fun _ => w) fun n => c * (n + 1) := by
  refine ⟨constTM w, w.length + 1, fun x => ?_⟩
  obtain ⟨hs, ho⟩ := emit_halts (constTM w).tm w id (fun _ _ _ => rfl)
    ((constTM w).tm.initCfg x) rfl
  have hbase : (constTM w).ComputesInTime x w (w.length + 1) := by
    exact ⟨_, hs, by simpa only [MultiTapeTM.initCfg, Cfg.init, List.nil_append] using ho, rfl⟩
  exact hbase.mono (Nat.le_mul_of_pos_right _ (by omega))

/-- The hardcoded comparator, followed by the chosen fixed-word emission chain. -/
private def ifEqTM (w₀ u v : List Bool) : FinTM Bool where
  k := 0
  State := Fin (w₀.length + 1) ⊕ (Fin (u.length + 1) ⊕ Fin (v.length + 1))
  tm :=
    { q₀ := .inl 0
      tr := fun q inp _ => match q with
        | .inl i =>
          if h : i.val < w₀.length then
            if inp = some w₀[i.val] then
              controlAction .pos (some (.inl ⟨i.val + 1, by omega⟩))
            else controlAction 0 (some (.inr (.inr 0)))
          else if inp = none then controlAction 0 (some (.inr (.inl 0)))
            else controlAction 0 (some (.inr (.inr 0)))
        | .inr (.inl i) => emitAction u (fun j => .inr (.inl j)) i
        | .inr (.inr i) => emitAction v (fun j => .inr (.inr j)) i }

/-- Once the comparator has chosen its output chain, that chain emits the selected
word and halts, independently of the input-head position. -/
private lemma ifEq_finish (w₀ u v x : List Bool) (b : Bool)
    (cfg : Cfg 0 Bool (ifEqTM w₀ u v).State x)
    (hs : cfg.state = some (.inr (cond b (.inl 0) (.inr 0)))) (ho : cfg.output = []) :
    ((ifEqTM w₀ u v).tm.runFrom cfg ((cond b u v).length + 1)).state = none ∧
    ((ifEqTM w₀ u v).tm.runFrom cfg ((cond b u v).length + 1)).output = cond b u v := by
  cases b
  · simpa only [Bool.cond_false, ho, List.nil_append] using
      emit_halts (ifEqTM w₀ u v).tm v (fun j => .inr (.inr j))
        (fun _ _ _ => rfl) cfg hs
  · simpa only [Bool.cond_true, ho, List.nil_append] using
      emit_halts (ifEqTM w₀ u v).tm u (fun j => .inr (.inl j))
        (fun _ _ _ => rfl) cfg hs

/-- Comparison invariant: the first `i` symbols match, and the head is at `i + 1`.

**Proof sketch.** Induct on the number of remaining comparison symbols. A matching
symbol advances the invariant. A mismatch selects the second emission chain. With
no symbols remaining, the boundary blank selects the first chain and an extra
symbol selects the second. The emission-chain lemma supplies the remaining time. -/
private lemma ifEq_run (w₀ u v x : List Bool) : ∀ (r i : ℕ) (hlen : w₀.length = i + r), i ≤ x.length → x.take i = w₀.take i →
    ∀ (cfg : Cfg 0 Bool (ifEqTM w₀ u v).State x),
      cfg.state = some (.inl ⟨i, by omega⟩) → cfg.inputPos.val = i + 1 → cfg.output = [] →
      ∃ t, t ≤ r + max u.length v.length + 2 ∧
        ((ifEqTM w₀ u v).tm.runFrom cfg t).state = none ∧
        ((ifEqTM w₀ u v).tm.runFrom cfg t).output = if x = w₀ then u else v := by
  intro r
  induction r with
  | zero =>
    intro i hlen hix hprefix cfg hs hp ho
    have hi : ¬i < w₀.length := by omega
    have hsym := inputSymbol_at cfg i hix hp
    by_cases he : x = w₀
    · subst x
      have hb : w₀[i]? = none := List.getElem?_eq_none_iff.mpr (by omega)
      have hstep : (ifEqTM w₀ u v).tm.step cfg =
          (controlAction 0 (some (.inr (.inl 0)))).apply cfg := by
        unfold MultiTapeTM.step
        rw [hs]
        simp only [ifEqTM, hsym, dif_neg hi, hb, ite_true]
      have hs' : ((ifEqTM w₀ u v).tm.step cfg).state = some (.inr (.inl 0)) := by
        rw [hstep]
        rfl
      have ho' : ((ifEqTM w₀ u v).tm.step cfg).output = [] := by
        simp [hstep, controlAction, Action.apply, ho]
      have hf := ifEq_finish w₀ u v w₀ true _ hs' ho'
      refine ⟨u.length + 1 + 1, by omega, ?_⟩
      rw [MultiTapeTM.runFrom_succ_eq_step]
      simpa only [Bool.cond_true, if_pos rfl] using hf
    · have hx : i < x.length := by
        by_contra hh
        have hxt : x.take i = x := List.take_of_length_le (by omega)
        have hwt : w₀.take i = w₀ := List.take_of_length_le (by omega)
        exact he (by rw [← hxt, ← hwt]; exact hprefix)
      have hb : x[i]? = some x[i] := List.getElem?_eq_getElem hx
      have hstep : (ifEqTM w₀ u v).tm.step cfg =
          (controlAction 0 (some (.inr (.inr 0)))).apply cfg := by
        unfold MultiTapeTM.step
        rw [hs]
        simp only [ifEqTM, hsym, dif_neg hi, hb, Option.some_ne_none, ite_false]
      have hs' : ((ifEqTM w₀ u v).tm.step cfg).state = some (.inr (.inr 0)) := by
        rw [hstep]
        rfl
      have ho' : ((ifEqTM w₀ u v).tm.step cfg).output = [] := by
        simp [hstep, controlAction, Action.apply, ho]
      have hf := ifEq_finish w₀ u v x false _ hs' ho'
      refine ⟨v.length + 1 + 1, by omega, ?_⟩
      rw [MultiTapeTM.runFrom_succ_eq_step]
      simpa only [Bool.cond_false, if_neg he] using hf
  | succ r ih =>
    intro i hlen hix hprefix cfg hs hp ho
    have hi : i < w₀.length := by omega
    have hsym := inputSymbol_at cfg i hix hp
    by_cases hm : x[i]? = some w₀[i]
    · obtain ⟨hx, hbit⟩ := List.getElem?_eq_some_iff.mp hm
      have hstep : (ifEqTM w₀ u v).tm.step cfg =
          (controlAction .pos (some (.inl ⟨i + 1, by omega⟩))).apply cfg := by
        unfold MultiTapeTM.step
        rw [hs]
        simp only [ifEqTM, hsym, dif_pos hi, hm, ite_true]
      have hs' : ((ifEqTM w₀ u v).tm.step cfg).state =
          some (.inl ⟨i + 1, by omega⟩) := by rw [hstep]; rfl
      have hp' : ((ifEqTM w₀ u v).tm.step cfg).inputPos.val = (i + 1) + 1 := by
        rw [hstep]
        change (moveInputPos cfg.inputPos .pos).val = i + 1 + 1
        rw [moveInputPos_pos_of_ne_right _ (by omega)]
        simp only
        omega
      have ho' : ((ifEqTM w₀ u v).tm.step cfg).output = [] := by
        simp [hstep, controlAction, Action.apply, ho]
      have hprefix' : x.take (i + 1) = w₀.take (i + 1) := by
        rw [List.take_succ, List.take_succ, hprefix, hm, List.getElem?_eq_getElem hi]
      obtain ⟨t, ht, htstate, htout⟩ := ih (i + 1) (by omega) (by omega) hprefix'
        ((ifEqTM w₀ u v).tm.step cfg) hs' hp' ho'
      refine ⟨t + 1, by omega, ?_⟩
      rw [MultiTapeTM.runFrom_succ_eq_step]
      exact ⟨htstate, htout⟩
    · have he : x ≠ w₀ := by
        intro he
        subst x
        exact hm (List.getElem?_eq_getElem hi)
      have hstep : (ifEqTM w₀ u v).tm.step cfg =
          (controlAction 0 (some (.inr (.inr 0)))).apply cfg := by
        unfold MultiTapeTM.step
        rw [hs]
        simp only [ifEqTM, hsym, dif_pos hi, if_neg hm]
      have hs' : ((ifEqTM w₀ u v).tm.step cfg).state = some (.inr (.inr 0)) := by
        rw [hstep]
        rfl
      have ho' : ((ifEqTM w₀ u v).tm.step cfg).output = [] := by
        simp [hstep, controlAction, Action.apply, ho]
      have hf := ifEq_finish w₀ u v x false _ hs' ho'
      refine ⟨v.length + 1 + 1, by omega, ?_⟩
      rw [MultiTapeTM.runFrom_succ_eq_step]
      simpa only [Bool.cond_false, if_neg he] using hf

/-- Testing equality with a fixed string is computable in linear time: for any fixed
`w₀ u v`, the function `w ↦ u` if `w = w₀` and `w ↦ v` otherwise. (Instantiated by
the `HALT` reduction as the postprocessor `w ↦ if w = [true] then [false] else
[true]`; see `TCSlib.Complexity.Uncomputability.Halting`.)

**Proof sketch.** Hardcode `w₀`, `u`, and `v` in the states. The machine walks the
input left to right comparing it against `w₀` symbol by symbol (`|w₀| + 1`
comparison states); on the first mismatch — including the input ending early (blank
read) or running long (a symbol where `w₀` is exhausted) — it switches to an
emission chain for `v`, and after matching all of `w₀` and then reading the boundary
blank it switches to an emission chain for `u` (at most `|u| + |v| + 2` further
states, one emitted symbol per step). Every run halts within
`|w₀| + max |u| |v| + 3` steps — a constant, absorbed as `c * (n + 1)`. -/
theorem computesFunInTime_ifEq (w₀ u v : List Bool) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun w => if w = w₀ then u else v) fun n => c * (n + 1) := by
  refine ⟨ifEqTM w₀ u v, w₀.length + max u.length v.length + 3, fun x => ?_⟩
  obtain ⟨t, ht, hs, ho⟩ := ifEq_run w₀ u v x w₀.length 0 (by omega) (by omega) rfl
    ((ifEqTM w₀ u v).tm.initCfg x) rfl (by simp) rfl
  have hbase : (ifEqTM w₀ u v).ComputesInTime x (if x = w₀ then u else v) t :=
    ⟨_, hs, ho, rfl⟩
  exact hbase.mono (Nat.le_trans (by omega) (Nat.le_mul_of_pos_right _ (by omega)))

/-- **Composition.** If `f` is computable within `T₁` and `g` within a monotone `T₂`,
then `g ∘ f` is computable within `c · (T₁ n + T₂ (T₁ n) + 1)`.

The inner bound `T₂ (T₁ n)` is valid because the intermediate string is no longer than
the time that produced it: `|f x| ≤ T₁ |x|` by `Turing.MultiTapeTM.output_length_le`.
Monotonicity of `T₂` is genuinely needed to convert that length bound into a time
bound.

**Proof sketch.** Build `M` with `M₁.k + M₂.k + 1` work tapes over `Bool`. Phase one
simulates `M₁` step for step on the true input, with `M₁`'s emissions written instead
onto the dedicated intermediate tape (constant overhead per step; this is the
append-only-output buffering discussed in the module docstring). Phase two rewinds the
intermediate tape head (at most `T₁ n` steps) and simulates `M₂` step for step, with
`M₂`'s input-head reads served from the intermediate tape and `M₂`'s emissions going to
the real output tape. Phase two costs constant overhead per step of `M₂`, which halts
within `T₂ |f x| ≤ T₂ (T₁ n)` steps. Bookkeeping (phase switching, boundary detection
on the intermediate tape) is absorbed into `c`.

**Implementation note (epoch 2).** The shared `bufferedCompTM` has
`M₁.k + (1 + M₂.k)` tapes and uses one physical step per simulated step.
The first halting time is at most `T₁ |x|`; rewind and dispatch take exactly
`|f x| + 2` steps, including the unconditional first left move. Consequently
`2 * T₁ |x| + T₂ (T₁ |x|) + 2` suffices, and the theorem uses `c = 2`. -/
theorem computesFunInTime_comp {M₁ M₂ : FinTM Bool} {f g : List Bool → List Bool}
    {T₁ T₂ : ℕ → ℕ}
    (h₁ : M₁.ComputesFunInTime f T₁) (h₂ : M₂.ComputesFunInTime g T₂)
    (hT₂ : Monotone T₂) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (g ∘ f) fun n => c * (T₁ n + T₂ (T₁ n) + 1) := by
  refine ⟨bufferedCompTM M₁ M₂, 2, fun x => ?_⟩
  obtain ⟨a, p, tapes, heads, ha, hstart⟩ :=
    bufferedComp_start M₁ M₂ x (f x) (T₁ x.length) (h₁ x)
  have hlen : (f x).length ≤ T₁ x.length := by
    have ho := ((computesInTime_iff _ _ _ _).mp (h₁ x)).2
    simpa only [ho] using M₁.tm.output_length_le x (T₁ x.length)
  -- This is the only use of monotonicity: transfer the intermediate length bound.
  have htime : T₂ (f x).length ≤ T₂ (T₁ x.length) := hT₂ hlen
  obtain ⟨b, _, hr⟩ := bufferedSecondCfg_run M₁ M₂ (M₂.tm.initCfg (f x)) true
    (by simp [VirtualTag, MultiTapeTM.initCfg, Cfg.init]) p tapes heads (T₂ (f x).length)
  have hc := (computesInTime_iff _ _ _ _).mp (h₂ (f x))
  have hbase : (bufferedCompTM M₁ M₂).ComputesInTime x (g (f x))
      (a + T₂ (f x).length) := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_add, hstart, hr]
    exact ⟨by simpa only [bufferedSecondCfg, Option.map_eq_none_iff] using hc.1, hc.2⟩
  exact hbase.mono (by dsimp only; omega)

/-- **Partial (guarded) sequential composition** — the phase-4 API obligation
identified by the phase-3 audit (round 2, finding 10 and Argument F):
`Turing.FinTM.computesFunInTime_comp` requires both components to compute *total*
functions, so it cannot take a partially computing machine — such as the universal
evaluator — as a component. This lemma composes two arbitrary machines at the level
of their halting relations, with **no totality or time hypotheses**: `M` behaves on
`x` exactly as `M₂` behaves on `M₁`'s completed output — halting, completed outputs,
and divergence all correspond.

Statement notes. The intermediate string `y` is existentially quantified, but by
`Turing.FinTM.ComputesInTime.output_unique` at most one `y` satisfies the first
conjunct, so the right-hand side reads "`M₁` halts on `x` (necessarily with a unique
`y`), and then `M₂` halts on `y` with `w`". If `M₁` diverges on `x`, or halts but
`M₂` diverges on its output, both sides are empty — `M` diverges. A time-bounded
refinement is deliberately not stated; it will be added if and when a result needs
it.

**Proof sketch** (buffered intermediate output, per the audit's design). `M` carries
`M₁`'s and `M₂`'s work tapes plus a fresh *buffer* tape. Phase one simulates `M₁` on
the true input step for step, with each emission of `M₁` written to the buffer tape
(write, move right) instead of the output tape; the append-only output discipline
makes the buffer region a verbatim copy of `M₁`'s output, contiguous from the
initial head cell. If `M₁` never halts, neither does `M`. On `M₁`'s halting
transition, `M` rewinds the buffer head to the leftmost written cell — the head
rests on the blank immediately *right* of the written word, so the rewind's first
left move is unconditional (testing the current cell before moving would stop at the
wrong end; phase-4 audit, finding 3), then left while reading a symbol, then one
step right. Phase two simulates `M₂` with its *input-tape
reads served from the buffer*: the buffer holds exactly `y` with blank cells on both
sides, and `M` maintains `M₂`'s virtual input position on it, mirroring the clamped
input-head semantics of `Turing.moveInputPos` at both boundaries — the same
virtual-boundary emulation as the universal machine's sketch
(`TCSlib.Complexity.TuringMachine.Universal`); a blank read identifies a boundary,
and *which* boundary is determined by the direction of arrival, tracked in the
state — for an empty intermediate word the simulation starts with the right-boundary
tag already set, the left boundary one inward move away (phase-4 audit, finding 3).
`M₂`'s work-tape actions go to its own fresh tapes and its emissions to the
real output tape, untouched during phase one. `M` halts exactly when the simulated
`M₂` halts; step-for-step run correspondence in each phase gives both directions of
the iff.

**Implementation note (epoch 2).** The buffer and virtual-input invariants are
public in `Simulation.lean`. The arrival tag is constrained only at boundaries;
stationary moves preserve it, including suppressed outward moves. Dispatch always
sets it to true, which is already the right-boundary tag when the word is empty.
A simulated phase-one halt remains live through the exact `|y| + 2` rewind.
For the forward implication, phase-one divergence contradicts a completed run;
otherwise extend that completed run beyond the verified phase-two start using
absorbing halting, and recover the second completed computation by lockstep. -/
theorem exists_comp_partial (M₁ M₂ : FinTM Bool) :
    ∃ M : FinTM Bool, ∀ x w : List Bool,
      (∃ t, M.ComputesInTime x w t) ↔
        ∃ y : List Bool,
          (∃ t, M₁.ComputesInTime x y t) ∧ ∃ t, M₂.ComputesInTime y w t := by
  classical
  refine ⟨bufferedCompTM M₁ M₂, fun x w => ?_⟩
  constructor
  · rintro ⟨t, ht⟩
    -- A divergent first component would keep every composite configuration live.
    have hh : ∃ s, (M₁.tm.runFrom (M₁.tm.initCfg x) s).state = none := by
      by_contra h
      have hr := bufferedFirstCfg_run M₁ M₂ (M₁.tm.initCfg x) t
        (fun s _ hs => h ⟨s, hs⟩)
      rw [← bufferedFirstCfg_init] at hr
      have hc := ((computesInTime_iff _ _ _ _).mp ht).1
      rw [hr] at hc
      simp only [bufferedFirstCfg, Option.some_ne_none] at hc
    obtain ⟨s, hs⟩ := hh
    let y := (M₁.tm.runFrom (M₁.tm.initCfg x) s).output
    have hy : M₁.ComputesInTime x y s := (computesInTime_iff _ _ _ _).mpr ⟨hs, rfl⟩
    obtain ⟨a, p, tapes, heads, _, ha⟩ := bufferedComp_start M₁ M₂ x y s hy
    -- Extend a completed run past the verified administrative prefix.
    have hc := (computesInTime_iff _ x w (a + t)).mp (ht.mono (by omega))
    rw [MultiTapeTM.runFrom_add, ha] at hc
    obtain ⟨b, _, hr⟩ := bufferedSecondCfg_run M₁ M₂ (M₂.tm.initCfg y) true
      (by simp [VirtualTag, MultiTapeTM.initCfg, Cfg.init]) p tapes heads t
    rw [hr] at hc
    refine ⟨y, ⟨s, hy⟩, t, (computesInTime_iff _ _ _ _).mpr ?_⟩
    exact ⟨by simpa only [bufferedSecondCfg, Option.map_eq_none_iff] using hc.1, hc.2⟩
  · rintro ⟨y, ⟨s, hs⟩, ⟨t, ht⟩⟩
    obtain ⟨a, p, tapes, heads, _, ha⟩ := bufferedComp_start M₁ M₂ x y s hs
    obtain ⟨b, _, hr⟩ := bufferedSecondCfg_run M₁ M₂ (M₂.tm.initCfg y) true
      (by simp [VirtualTag, MultiTapeTM.initCfg, Cfg.init]) p tapes heads t
    have hc := (computesInTime_iff _ _ _ _).mp ht
    refine ⟨a + t, (computesInTime_iff _ _ _ _).mpr ?_⟩
    rw [MultiTapeTM.runFrom_add, ha, hr]
    exact ⟨by simpa only [bufferedSecondCfg, Option.map_eq_none_iff] using hc.1, hc.2⟩

/-- A finite controller runs `D` with its first emission captured in a register,
rewinds, then enters the selected branch on disjoint fresh tapes. A simulated halt
is represented by a live control state so that dispatch occurs only after `D` halts.
An empty register at dispatch halts safely. -/
private def condTM (D M₁ M₂ : FinTM Bool) : FinTM Bool where
  k := D.k + (M₁.k + M₂.k)
  State := (Option D.State × Option Bool) ⊕ (Option Bool ⊕ (M₁.State ⊕ M₂.State))
  tm :=
    { q₀ := .inl (some D.tm.q₀, none)
      tr := fun q inp work => match q with
        | .inl (some q, reg) =>
          let a := D.tm.tr q inp (fun i => work (Fin.castAdd (M₁.k + M₂.k) i))
          ⟨a.inputTape, Fin.addCases a.workTapes (fun _ => (none, 0)), none,
            some (.inl (a.state, reg.or a.output))⟩
        | .inl (none, reg) => controlAction .neg (some (.inr (.inl reg)))
        | .inr (.inl reg) => match inp with
          | some _ => controlAction .neg (some (.inr (.inl reg)))
          | none => controlAction .pos
              (reg.map (fun b => .inr (.inr (branchTM M₁ M₂ b).tm.q₀)))
        | .inr (.inr q) => rightAction D.k (fun s => .inr (.inr s))
            ((branchTM M₁ M₂ false).tm.tr q inp (fun i => work (Fin.natAdd D.k i))) }

/-- Embed a controller configuration with its output suppressed and the first
output symbol stored in the finite register. All branch tapes remain blank. -/
private def controlCfg (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg D.k Bool D.State x) : Cfg (condTM D M₁ M₂).k Bool (condTM D M₁ M₂).State x where
  state := some (.inl (c.state, c.output.head?))
  inputPos := c.inputPos
  workTapes := Fin.addCases c.workTapes (fun _ _ => none)
  workTapePos := Fin.addCases c.workTapePos (fun _ => 0)
  output := []

/-- Before the simulated controller halts, one composite step exactly updates its
configuration and the first-emission register. The head-of-append identity makes
this invariant valid even without any assumption on the controller's output. -/
private lemma controlCfg_step (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg D.k Bool D.State x) (hs : c.state ≠ none) :
    (condTM D M₁ M₂).tm.step (controlCfg D M₁ M₂ c) =
      controlCfg D M₁ M₂ (D.tm.step c) := by
  unfold MultiTapeTM.step
  cases hq : c.state with
  | none => exact False.elim (hs hq)
  | some q =>
    have hs' : (controlCfg D M₁ M₂ c).state = some (.inl (some q, c.output.head?)) := by
      simp [controlCfg, hq]
    rw [hs']
    dsimp only [condTM]
    have hr : (fun i => (controlCfg D M₁ M₂ c).workTapeSymbols
        (Fin.castAdd (M₁.k + M₂.k) i)) = c.workTapeSymbols := by
      funext i
      simp [controlCfg, Cfg.workTapeSymbols]
    have hi : (controlCfg D M₁ M₂ c).inputSymbol = c.inputSymbol := rfl
    rw [hr, hi]
    refine Cfg.ext ?_ rfl ?_ ?_ ?_
    · simp [controlCfg, Action.apply, List.head?_append, Option.head?_toList]
    · funext i
      refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [controlCfg, Action.apply]
    · funext i
      refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [controlCfg, Action.apply]
    · simp [controlCfg, Action.apply]

/-- Controller lockstep holds through its first halting step. Subsequent composite
steps perform the rewind, so no claim of lockstep after halting is made. -/
private lemma controlCfg_run (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg D.k Bool D.State x) (t : ℕ)
    (h : ∀ s, s < t → (D.tm.runFrom c s).state ≠ none) :
    (condTM D M₁ M₂).tm.runFrom (controlCfg D M₁ M₂ c) t =
      controlCfg D M₁ M₂ (D.tm.runFrom c t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (fun s hs => h s (by omega)),
      controlCfg_step D M₁ M₂ _ (h t (by omega)), MultiTapeTM.runFrom_succ_eq_step']

/-- A completed singleton controller computation reaches the selected branch's
fresh initial configuration after a finite prefix.

**Proof sketch.** Choose the first halting time of `D` and use controller lockstep.
Output uniqueness identifies its completed output with `[b]`, so the register is
`some b`, including when that bit was emitted early. Rewind from the resulting
input position; the branch tapes and real output have remained untouched. -/
private lemma condTM_start (D M₁ M₂ : FinTM Bool) (x : List Bool) (b : Bool)
    (hD : ∃ t, D.ComputesInTime x [b] t) :
    ∃ (t : ℕ) (tapes : Fin D.k → ℤ → Option Bool) (heads : Fin D.k → ℤ),
      (condTM D M₁ M₂).tm.runFrom ((condTM D M₁ M₂).tm.initCfg x) t =
        rightCfg (fun q => .inr (.inr q)) ((branchTM M₁ M₂ b).tm.initCfg x) tapes heads := by
  classical
  obtain ⟨tD, hDc⟩ := hD
  have hh : ∃ t, (D.tm.runFrom (D.tm.initCfg x) t).state = none :=
    ⟨tD, ((computesInTime_iff D x [b] tD).mp hDc).1⟩
  let t := Nat.find hh
  let cf := D.tm.runFrom (D.tm.initCfg x) t
  have hstop : cf.state = none := Nat.find_spec hh
  have hc : D.ComputesInTime x cf.output t :=
    (computesInTime_iff D x cf.output t).mpr ⟨hstop, rfl⟩
  have hout : cf.output = [b] := hc.output_unique hDc
  have hi : (condTM D M₁ M₂).tm.initCfg x = controlCfg D M₁ M₂ (D.tm.initCfg x) := by
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    · funext i
      refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [controlCfg]
    · funext i
      refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [controlCfg]
  have hrun : (condTM D M₁ M₂).tm.runFrom ((condTM D M₁ M₂).tm.initCfg x) t =
      controlCfg D M₁ M₂ cf := by
    rw [hi]
    exact controlCfg_run D M₁ M₂ (D.tm.initCfg x) t (fun s hs => Nat.find_min hh hs)
  obtain ⟨r, hr⟩ := rewind_from_any (condTM D M₁ M₂).tm
    (.inl (none, some b)) (.inr (.inl (some b)))
    (some (.inr (.inr (branchTM M₁ M₂ b).tm.q₀)))
    (fun _ _ => rfl) (fun inp _ => by cases inp <;> rfl)
    (controlCfg D M₁ M₂ cf) (by simp [controlCfg, hstop, hout])
  refine ⟨t + r, cf.workTapes, cf.workTapePos, ?_⟩
  rw [MultiTapeTM.runFrom_add, hrun, hr]
  rfl

/-- **Branching on a decided predicate** — the second phase-4 combinator (phase-3
audit, round 2, Argument F, step 2 of the `HALT → UC` reduction): given a total
decider `D` for `p` and two branch machines, some machine behaves on every input
exactly as the branch selected by `p` does *on that same input*. The input tape is
read-only, so both branches see the original input.

**Proof sketch.** `D` computes the singleton output `[p x]` on every input, and
output is append-only, so along any run `D` emits exactly one symbol; simulate `D`
with that single emission recorded in a state register instead of emitted (no buffer
tape needed). On `D`'s halting transition, rewind the true input head to its initial
position: one step left, then left while reading a symbol, then one step right —
from any position this ends at input position `1`, the initial position, the clamp
at position `0` making the walk safe (including on empty input). Then transfer
control to a disjoint copy of `M₁` or `M₂` according to the register. The branches'
work tapes are fresh tapes `D` never touched, the output tape is untouched by phase
one, and the input head is back at its initial position, so the selected branch's
run is reproduced verbatim; determinism (`Turing.FinTM.ComputesInTime.output_unique`)
identifies `D`'s completed output with `[p x]`, so the selected branch is
`cond (p x) M₁ M₂`.

The implementation retains the first emission, with the exact invariant that the
register is the head of the simulated output. A live administrative state follows
the simulated halt before the first left move. For the forward implication, extend
any completed composite run beyond the verified branch-start prefix using absorbing
halting, then apply branch lockstep; the reverse implication concatenates that
prefix with the selected branch run. -/
theorem exists_cond (D M₁ M₂ : FinTM Bool) (p : List Bool → Bool)
    (hD : D.Computes fun x => [p x]) :
    ∃ M : FinTM Bool, ∀ x w : List Bool,
      (∃ t, M.ComputesInTime x w t) ↔
        ∃ t, (cond (p x) M₁ M₂).ComputesInTime x w t := by
  refine ⟨condTM D M₁ M₂, fun x w => ?_⟩
  obtain ⟨a, tapes, heads, ha⟩ := condTM_start D M₁ M₂ x (p x) (hD x)
  have hr (t : ℕ) :
      (condTM D M₁ M₂).tm.runFrom ((condTM D M₁ M₂).tm.initCfg x) (a + t) =
        rightCfg (fun q => .inr (.inr q))
          ((branchTM M₁ M₂ (p x)).tm.runFrom ((branchTM M₁ M₂ (p x)).tm.initCfg x) t)
          tapes heads := by
    rw [MultiTapeTM.runFrom_add, ha]
    exact rightCfg_run (branchTM M₁ M₂ (p x)).tm (condTM D M₁ M₂).tm
      (fun q => .inr (.inr q)) (fun _ _ _ => rfl) _ tapes heads t
  constructor
  · rintro ⟨t, ht⟩
    have hc := (computesInTime_iff (condTM D M₁ M₂) x w (a + t)).mp
      (ht.mono (by omega))
    rw [hr t] at hc
    have hb : (branchTM M₁ M₂ (p x)).ComputesInTime x w t :=
      (computesInTime_iff _ x w t).mpr
        ⟨by simpa only [rightCfg, Option.map_eq_none_iff] using hc.1, hc.2⟩
    exact ⟨t, (branchTM_computes M₁ M₂ (p x) x w t).mp hb⟩
  · rintro ⟨t, ht⟩
    have hb := (computesInTime_iff (branchTM M₁ M₂ (p x)) x w t).mp
      ((branchTM_computes M₁ M₂ (p x) x w t).mpr ht)
    refine ⟨a + t, (computesInTime_iff _ x w (a + t)).mpr ?_⟩
    rw [hr t]
    exact ⟨by simpa only [rightCfg, Option.map_eq_none_iff] using hb.1, hb.2⟩

end Turing.FinTM


## ===== TCSlib/Complexity/TuringMachine/Encoding.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Bits
import TCSlib.Complexity.TuringMachine.StateRenaming
import TCSlib.Complexity.TuringMachine.Robustness.SingleTape

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machines as strings

[AB09, §1.4]: machines can be represented as binary strings, in such a way that
**(1)** every string represents some machine, and **(2)** every machine is represented
by infinitely many strings. This file provides the *code normal form* (`CodeTM`: one
work tape, binary alphabet, `Fin`-states — encodability requires fixing concrete
parameters, and by `Turing.FinTM.one_work_tape_binary` this normal form loses only a
quadratic factor), a fixed canonical serialization `CodeTM.serialize`, the
specification `MachineCode`/`EffectiveMachineCode` of a representation scheme, and the
self-delimiting pairing used by the universal machine.

## Design and deviations from [AB09]

* [AB09] fixes one concrete representation and standing conventions. We specify the
  representation *abstractly*, state the universal machine relative to it
  (`TCSlib.Complexity.TuringMachine.Universal`), and record the existence of a
  concrete scheme as a separate obligation.
* **The algebraic laws alone are not enough** (phase-3 audit, finding 1 and
  Argument A): a scheme satisfying only totality and padded round-trips may assign
  *noncomputable* meanings to codes — permuting the meanings of an honest scheme
  along an undecidable set preserves every law — and no universal machine can exist
  relative to such a scheme. Moreover requiring the scheme to canonize into *its own*
  encoding does not help (the pathological scheme's canonizer is computable). The
  effectivity contract must target a **fixed, scheme-independent** format: an
  `EffectiveMachineCode` carries a machine of this development computing
  `fun α => (decode α).serialize`, where `CodeTM.serialize` is the concrete
  serialization defined below. All universal-machine statements are relative to
  `EffectiveMachineCode`.
* Property (2) is stated as recovery under **`true`-padding of valid codes**
  (`decode_encode_pad`), the formal content of [AB09]'s "trailing 1s are ignored"
  convention; padding of *arbitrary* strings is deliberately not constrained.
  Property (1), totality, is enforced by `decode`'s type — this is a totality
  guarantee, not by itself a computability guarantee (audit finding 9).
* `CodeTM.serialize` records the state count, **the initial state** (audit finding 5:
  omitting it makes distinct machines collide), and the full transition table in a
  fixed enumeration order.

## Main definitions

* `Turing.CodeTM` — the code normal form; `Turing.CodeTM.toFinTM`;
  `Turing.CodeTM.serialize` — the fixed canonical serialization.
* `Turing.pairEncode` — self-delimiting pairing (first component doubled bitwise,
  separator `[false, true]`, second component verbatim).
* `Turing.MachineCode` — the algebraic representation-scheme laws [AB09, §1.4].
* `Turing.EffectiveMachineCode` — a scheme together with an in-model machine
  computing `serialize ∘ decode`; the standing hypothesis of the universal machine.

## Main results

* `Turing.MachineCode.decode_encode` — decoding a code recovers the machine.
* `Turing.pairEncode_injective` — the pairing is injective (aligned-pair parsing).
* `Turing.computesFunInTime_pairEncode_diag` — the diagonal pairing `α ↦ ⟨α, α⟩` is
  computable in linear time (the only code computation the `HALT` reduction needs).
* `Turing.exists_codeTM` — every one-work-tape binary machine is equivalent to a
  coded machine (state relabeling).

The concrete parser/decoder realizing a scheme lives in
`TCSlib.Complexity.TuringMachine.CodeParser`, and the existence of an effective
scheme (`Turing.exists_effectiveMachineCode`) is proved in
`TCSlib.Complexity.TuringMachine.MathlibBridge`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4, pp. 19-20.)
-/

namespace Turing

/-- A machine in *code normal form*: one work tape, binary alphabet, and states drawn
from a canonical nonempty finite type `Fin (numStates + 1)`. [AB09, §1.4] -/
structure CodeTM where
  /-- one less than the number of states (so the state space is never empty) -/
  numStates : ℕ
  /-- the underlying machine -/
  tm : MultiTapeTM 1 Bool (Fin (numStates + 1))

/-- The bundled machine of a coded machine. -/
def CodeTM.toFinTM (M : CodeTM) : FinTM Bool where
  k := 1
  State := Fin (M.numStates + 1)
  tm := M.tm

/-- The bundled form of a coded machine has exactly one work tape. -/
@[simp]
lemma CodeTM.toFinTM_k (M : CodeTM) : M.toFinTM.k = 1 := rfl

/-- Self-delimiting pairing of two binary strings: the **first** string with every bit
doubled, then the separator `[false, true]`, then the second string verbatim. Parsing
reads aligned two-bit blocks: `00`/`11` are data, the first aligned `01` is the
separator (a `01` can only occur unaligned inside doubled data), and the suffix is the
second component. The universal machine's input convention is `pairEncode α x` —
**code first, input second**, deviating from [AB09]'s `⟨x, α⟩` order so that the
simulation's startup cost is independent of the input (phase-3 audit, finding 2 and
Argument B: with the input first, no bound `C · (t + 1)` with `C` independent of `x`
can hold). -/
def pairEncode (x α : List Bool) : List Bool :=
  (x.flatMap fun b => [b, b]) ++ [false, true] ++ α

/-- Parse aligned doubled bits until the separator, leaving its suffix untouched. -/
def pairDecode : List Bool → Option (List Bool × List Bool)
  | false :: false :: rest => (pairDecode rest).map fun p => (false :: p.1, p.2)
  | true :: true :: rest => (pairDecode rest).map fun p => (true :: p.1, p.2)
  | false :: true :: rest => some ([], rest)
  | _ => none

/-- The aligned parser recovers both components, by induction on the first word. -/
lemma pairDecode_pairEncode (x α : List Bool) :
    pairDecode (pairEncode x α) = some (x, α) := by
  induction x with
  | nil => rfl
  | cons b x ih =>
    have h := congrArg (Option.map fun p : List Bool × List Bool => (b :: p.1, p.2)) ih
    cases b <;> simpa [pairEncode, pairDecode] using h

/-- The pairing is injective.

**Proof sketch** (phase-3 audit, Argument D). The aligned two-bit parser recovers the
components: read blocks of two from the left; `00` yields `false`, `11` yields `true`,
and the first aligned `01` is the separator — no doubled bit produces an aligned `01`.
The remaining suffix is the second component verbatim. This parser is a left inverse
of the pairing, and a function with a left inverse is injective. Empty components are
unproblematic (`pairEncode [] α = [false, true] ++ α`). -/
theorem pairEncode_injective :
    Function.Injective fun p : List Bool × List Bool => pairEncode p.1 p.2 := by
  intro p q h
  have := congrArg pairDecode h
  simpa only [pairDecode_pairEncode, Prod.mk.eta, Option.some.injEq] using this

/-- Six-state pairing controller: double-stay, double-move, emit-true,
first-left, rewind, and copy. The double-stay state's blank branch emits `false`. -/
private def pairDiagTM : FinTM Bool where
  k := 0
  State := Fin 6
  tm :=
    { q₀ := 0
      tr := fun q inp _ =>
        match q with
        | 0 => match inp with
          | some b => ⟨.zero, fun i => i.elim0, some b, some 1⟩
          | none => ⟨.zero, fun i => i.elim0, some false, some 2⟩
        | 1 => ⟨.pos, fun i => i.elim0, inp, some 0⟩
        | 2 => ⟨.zero, fun i => i.elim0, some true, some 3⟩
        | 3 => ⟨.neg, fun i => i.elim0, none, some 4⟩
        | 4 => match inp with
          | some _ => ⟨.neg, fun i => i.elim0, none, some 4⟩
          | none => ⟨.pos, fun i => i.elim0, none, some 5⟩
        | _ => match inp with
          | some b => ⟨.pos, fun i => i.elim0, some b, some 5⟩
          | none => ⟨.zero, fun i => i.elim0, none, none⟩ }

/-- A pairing-machine configuration, with its vacuous work-tape fields suppressed. -/
private def pairDiagCfg (x : List Bool) (q : Option (Fin 6))
    (p : Fin (x.length + 2)) (out : List Bool) : Cfg 0 Bool (Fin 6) x :=
  ⟨q, p, fun i => i.elim0, fun i => i.elim0, out⟩

/-- One live transition of the pairing controller, given its scanned input symbol. -/
private lemma pairDiag_step (x : List Bool) (q : Fin 6)
    (p : Fin (x.length + 2)) (out : List Bool) (b : Option Bool)
    (hb : (pairDiagCfg x (some q) p out).inputSymbol = b) :
    pairDiagTM.tm.step (pairDiagCfg x (some q) p out) =
      let a := pairDiagTM.tm.tr q b (fun i => i.elim0)
      pairDiagCfg x a.state (moveInputPos p a.inputTape) (out ++ a.output.toList) := by
  change (pairDiagTM.tm.tr q (pairDiagCfg x (some q) p out).inputSymbol
    (pairDiagCfg x (some q) p out).workTapeSymbols).apply _ = _
  rw [hb]
  exact Cfg.ext_zero_tapes rfl rfl rfl

/-- At position `j + 1`, the pairing machine reads the `j`-th input bit. -/
private lemma pairDiag_inner (x : List Bool) (q : Option (Fin 6)) (out : List Bool)
    (j : ℕ) (hj : j < x.length) :
    (pairDiagCfg x q ⟨j + 1, by omega⟩ out).inputSymbol = some x[j] :=
  inputSymbolInner j (by simp only [pairDiagCfg]; omega) hj

/-- At the right boundary the pairing machine reads blank, also on empty input. -/
private lemma pairDiag_right (x : List Bool) (q : Option (Fin 6)) (out : List Bool) :
    (pairDiagCfg x q ⟨x.length + 1, by omega⟩ out).inputSymbol = none := by
  simp [pairDiagCfg, Cfg.inputSymbol, Fin.ext_iff]

/-- After `2t` transitions, the first pass has doubled exactly the first `t` bits.

**Proof sketch.** Induct on `t`. Each bit is first emitted without moving and then
emitted again while moving right. The two emissions extend the doubled prefix. -/
private lemma pairDiag_double (x : List Bool) : ∀ t, (ht : t ≤ x.length) →
    pairDiagTM.tm.runFrom (pairDiagTM.tm.initCfg x) (2 * t) =
      pairDiagCfg x (some 0) ⟨t + 1, by omega⟩ ((x.take t).flatMap fun b => [b, b]) := by
  intro t
  induction t with
  | zero =>
    intro _
    apply Cfg.ext_zero_tapes <;> simp [pairDiagTM, pairDiagCfg, MultiTapeTM.runFrom]
  | succ t ih =>
    intro ht
    rw [show 2 * (t + 1) = 2 * t + 1 + 1 by omega,
      MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    rw [pairDiag_step _ _ _ _ _ (pairDiag_inner x (some 0) _ t (by omega))]
    simp only [pairDiagTM, SignType.zero_eq_zero, moveInputPos_zero, Option.toList_some]
    rw [pairDiag_step _ _ _ _ _ (pairDiag_inner x (some 1) _ t (by omega))]
    simp only [pairDiagTM, Option.toList_some]
    rw [moveInputPos_pos_of_ne_right _ (by change t + 1 ≠ x.length + 1; omega)]
    apply Cfg.ext_zero_tapes
    · rfl
    · rfl
    · change (((x.take t).flatMap fun b => [b, b]) ++ [x[t]]) ++ [x[t]] =
        (x.take (t + 1)).flatMap fun b => [b, b]
      rw [List.take_succ, List.getElem?_eq_getElem (by omega)]
      simp only [Option.toList_some, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.append_assoc, List.cons_append, List.nil_append]

/-- Rewinding from position `j ≤ n` takes `j + 1` steps and preserves the output.

**Proof sketch.** At position zero, move right and enter the copy state. At a
positive position at most `n`, the read is a symbol, so move left and apply the
induction hypothesis. The preceding unconditional left step reaches this range. -/
private lemma pairDiag_rewind (x out : List Bool) : ∀ j, (hj : j ≤ x.length) →
    pairDiagTM.tm.runFrom (pairDiagCfg x (some 4) ⟨j, by omega⟩ out) (j + 1) =
      pairDiagCfg x (some 5) 1 out := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero,
      pairDiag_step _ _ _ _ none (by simp [pairDiagCfg, Cfg.inputSymbol])]
    simp only [pairDiagTM, Option.toList_none, List.append_nil]
    rw [moveInputPos_pos_of_ne_right _ (by simp)]
    apply Cfg.ext_zero_tapes
    · rfl
    · apply Fin.ext; simp [pairDiagCfg]
    · rfl
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step,
      pairDiag_step _ _ _ _ _ (pairDiag_inner x (some 4) out j (by omega))]
    simp only [pairDiagTM, Option.toList_none, List.append_nil]
    rw [moveInputPos_neg_of_ne_left _ (by simp [Fin.ext_iff])]
    simpa using ih (by omega)

/-- The second pass appends the first `t` input bits in `t` transitions.

**Proof sketch.** Induct on `t`, reading at position `t + 1`, appending that bit,
and moving right. The previously emitted doubled word and separator are preserved. -/
private lemma pairDiag_copy (x out : List Bool) : ∀ t, (ht : t ≤ x.length) →
    pairDiagTM.tm.runFrom (pairDiagCfg x (some 5) 1 out) t =
      pairDiagCfg x (some 5) ⟨t + 1, by omega⟩ (out ++ x.take t) := by
  intro t
  induction t with
  | zero =>
    intro _
    apply Cfg.ext_zero_tapes <;> simp [pairDiagCfg]
  | succ t ih =>
    intro ht
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega),
      pairDiag_step _ _ _ _ _ (pairDiag_inner x (some 5) _ t (by omega))]
    simp only [pairDiagTM, Option.toList_some]
    rw [moveInputPos_pos_of_ne_right _ (by change t + 1 ≠ x.length + 1; omega)]
    apply Cfg.ext_zero_tapes
    · rfl
    · rfl
    · change (out ++ x.take t) ++ [x[t]] = out ++ x.take (t + 1)
      rw [List.take_succ, List.getElem?_eq_getElem (by omega)]
      simp only [Option.toList_some, List.append_assoc]

/-- Two stationary separator emissions followed by the unconditional first left move.

**Proof sketch.** At the right blank, states 0 and 2 emit `false` and `true`.
State 3 then moves from position `n + 1` to `n`, without emitting a bit. -/
private lemma pairDiag_separator (x out : List Bool) :
    pairDiagTM.tm.runFrom
      (pairDiagCfg x (some 0) ⟨x.length + 1, by omega⟩ out) 3 =
      pairDiagCfg x (some 4) ⟨x.length, by omega⟩ (out ++ [false, true]) := by
  rw [show 3 = (0 + 1) + 1 + 1 from rfl,
    MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step',
    MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero]
  rw [pairDiag_step _ _ _ _ _ (pairDiag_right x (some 0) out)]
  simp only [pairDiagTM, SignType.zero_eq_zero, moveInputPos_zero, Option.toList_some]
  rw [pairDiag_step _ _ _ _ _ (pairDiag_right x (some 2) _)]
  simp only [pairDiagTM, SignType.zero_eq_zero, moveInputPos_zero, Option.toList_some]
  rw [pairDiag_step _ _ _ _ _ (pairDiag_right x (some 3) _)]
  simp only [pairDiagTM, Option.toList_none, List.append_nil]
  rw [moveInputPos_neg_of_ne_left _ (by simp [Fin.ext_iff])]
  apply Cfg.ext_zero_tapes <;> simp [pairDiagCfg, List.append_assoc]

/-- The complete pairing run is halted with the required output by step `4n + 5`.

**Proof sketch.** Chain the doubled pass (`2n`), the two separator steps and first
left move (`3`), the rewind from position `n` (`n + 1`), the copy (`n`), and the
halting transition (`1`). Each equality records the whole configuration. -/
private lemma pairDiag_run (x : List Bool) :
    pairDiagTM.tm.runFrom (pairDiagTM.tm.initCfg x) (4 * x.length + 5) =
      pairDiagCfg x none ⟨x.length + 1, by omega⟩ (pairEncode x x) := by
  have hd := pairDiag_double x x.length (le_refl _)
  simp only [List.take_length] at hd
  have hr : pairDiagTM.tm.runFrom (pairDiagTM.tm.initCfg x) (3 * x.length + 4) =
      pairDiagCfg x (some 5) 1 ((x.flatMap fun b => [b, b]) ++ [false, true]) := by
    rw [show 3 * x.length + 4 = 2 * x.length + (3 + (x.length + 1)) by omega,
      MultiTapeTM.runFrom_add, hd, MultiTapeTM.runFrom_add, pairDiag_separator,
      pairDiag_rewind x _ x.length (le_refl _)]
  have hc : pairDiagTM.tm.runFrom (pairDiagTM.tm.initCfg x) (4 * x.length + 4) =
      pairDiagCfg x (some 5) ⟨x.length + 1, by omega⟩ (pairEncode x x) := by
    rw [show 4 * x.length + 4 = (3 * x.length + 4) + x.length by omega,
      MultiTapeTM.runFrom_add, hr, pairDiag_copy x _ x.length (le_refl _)]
    simp only [List.take_length, pairEncode]
  rw [show 4 * x.length + 5 = (4 * x.length + 4) + 1 by omega,
    MultiTapeTM.runFrom_succ_eq_step', hc,
    pairDiag_step _ _ _ _ _ (pairDiag_right x (some 5) _)]
  simp only [pairDiagTM, SignType.zero_eq_zero, moveInputPos_zero, Option.toList_none, List.append_nil]

/-- The diagonal pairing `α ↦ pairEncode α α` — the self-application input of the
`HALT` reduction [AB09, proof of Theorem 1.11] — is computable in linear time. This
is the *only* computation on codes that reduction needs (phase-3 audit, round 2,
Argument F): `encode` itself is never computed by any machine of this development.

**Proof sketch.** Two sweeps of the input with a constant number of states. Pass one
walks the input left to right emitting each bit twice — one emitted symbol per
transition, so two steps per bit: emit staying put, emit moving right; on reading the
right boundary blank it emits the separator `false`, `true` (two steps) and rewinds
the input head to the start (one step left, then left while reading a symbol, then
one step right — the clamp at position `0` makes this safe, including on empty
input). Pass two walks the input again emitting each bit once, and halts on the
boundary blank. Total on inputs of length `n`: `2n` (doubled pass) `+ 2` (separator)
`+ (n + 2)` (rewind) `+ n` (second pass) `+ 1` (halt) `= 4n + 5 ≤ 6 · (n + 1)`
(phase-4 audit, finding 1: an earlier `3n + 6` figure undercounted the doubled
pass), absorbed as `c * (n + 1)`. -/
theorem computesFunInTime_pairEncode_diag :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun α => pairEncode α α) fun n => c * (n + 1) := by
  refine ⟨pairDiagTM, 6, fun x => ?_⟩
  have h : pairDiagTM.ComputesInTime x (pairEncode x x) (4 * x.length + 5) := by
    refine ⟨_, ?_, ?_, rfl⟩
    · rw [pairDiag_run]; rfl
    · rw [pairDiag_run]; rfl
  exact h.mono (by change 4 * x.length + 5 ≤ 6 * (x.length + 1); omega)

section Serialize

/-- Fixed two-bit serialization of a head move. -/
def signBits : SignType → List Bool
  | .neg => [true, true]
  | .zero => [false, false]
  | .pos => [true, false]

/-- Fixed two-bit serialization of an optional bit. -/
def optBoolBits : Option Bool → List Bool
  | none => [false, false]
  | some false => [true, false]
  | some true => [true, true]

/-- Fixed two-bit serialization of an optional write (which may itself write blank). -/
def optOptBoolBits : Option (Option Bool) → List Bool
  | none => [false, false]
  | some none => [false, true]
  | some (some false) => [true, false]
  | some (some true) => [true, true]

/-- Self-delimiting unary serialization of a state index. -/
def unaryFin {n : ℕ} (s : Fin n) : List Bool :=
  List.replicate (s : ℕ) true ++ [false]

/-- Serialization of an optional successor state (`none` = halt). -/
def optStateBits {n : ℕ} : Option (Fin n) → List Bool
  | none => [false]
  | some s => true :: unaryFin s

/-- Serialization of one transition record. -/
def actionBits {n : ℕ} (a : Action 1 Bool (Fin (n + 1))) : List Bool :=
  signBits a.inputTape ++ optOptBoolBits (a.workTapes 0).1 ++
    signBits (a.workTapes 0).2 ++ optBoolBits a.output ++ optStateBits a.state

/-- The **fixed, scheme-independent** canonical serialization of a coded machine: the
state count (self-delimiting via `pairEncode`'s doubled-bit region), then the initial
state (audit finding 5: it must be recorded — machines with equal tables and
different initial states differ), then the full transition table in the fixed
enumeration order (states in `Fin` order; input read and work read each ranging over
`none`, `some false`, `some true`). This is the target format of
`EffectiveMachineCode.canonizer`, which is what ties a scheme's `decode` to effective
semantics (audit finding 1). -/
def CodeTM.serialize (M : CodeTM) : List Bool :=
  pairEncode (Nat.bits M.numStates)
    (unaryFin M.tm.q₀ ++
      (List.finRange (M.numStates + 1)).flatMap fun q =>
        ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
          ([none, some false, some true] : List (Option Bool)).flatMap fun w =>
            actionBits (M.tm.tr q inp fun _ => w))

end Serialize

/-- The algebraic laws of a representation scheme for coded machines [AB09, §1.4]: a
total decoding (every string represents some machine — property 1), an encoding, and
recovery of the machine from its code under arbitrary `true`-padding (hence every
machine has infinitely many representations — property 2).

These laws alone do **not** support universal simulation — see the module docstring
and `Turing.EffectiveMachineCode`. -/
structure MachineCode where
  /-- encode a machine as a binary string, `⌞M⌟` -/
  encode : CodeTM → List Bool
  /-- decode any binary string to a machine (total by type: property 1) -/
  decode : List Bool → CodeTM
  /-- a code followed by any amount of `true`-padding decodes to the machine
  (property 2: infinitely many representations) -/
  decode_encode_pad : ∀ M m, decode (encode M ++ List.replicate m true) = M

/-- Decoding a code recovers the machine ([AB09, §1.4]; padding by zero symbols). -/
theorem MachineCode.decode_encode (c : MachineCode) (M : CodeTM) :
    c.decode (c.encode M) = M := by
  simpa using c.decode_encode_pad M 0

/-- An *effective* representation scheme: the algebraic laws together with a machine
of this development that computes the fixed serialization of the decoded machine,
within some time bound depending only on the code's length.

The target `CodeTM.serialize` is scheme-independent, which is essential: requiring
only a canonizer into the scheme's *own* `encode` is still satisfied by the
noncomputable-meaning pathology of audit Argument A, whereas computing
`serialize ∘ decode` for that pathology would decide an undecidable set, so no such
machine exists and the pathology is excluded. -/
structure EffectiveMachineCode extends MachineCode where
  /-- a machine computing the fixed serialization of the decoded machine -/
  canonizer : FinTM Bool
  /-- the canonizer's time bound (arbitrary here; universal-machine constants absorb
  its value at each fixed code) -/
  canonizerTime : ℕ → ℕ
  /-- the canonizer computes `serialize ∘ decode` -/
  canonizer_computes :
    canonizer.ComputesFunInTime (fun α => (decode α).serialize) canonizerTime

/-- Every one-work-tape binary machine is equivalent, input by input and step for
step, to a coded machine.

**Proof sketch.** `State` carries `Fintype`/`DecidableEq` instances and is inhabited
by `q₀`, so `Fintype.equivFin` gives `e : State ≃ Fin n` with `n = numStates + 1` for
some `numStates`. Transport the transition function along `e` (renaming states with
`Turing.Action.mapState` and reading them back through `e.symm`); the induced map on
configurations is a bijection commuting with `step` (the tapes and heads are
untouched), so runs, halting, and outputs correspond at every step. The tape-count
cast uses `hk : M.k = 1`.

The implementation uses `Turing.MultiTapeTM.relabelState` (the shared state-renaming
module, `TCSlib.Complexity.TuringMachine.StateRenaming`), eliminates `hk` after
destructuring the bundle, and concludes with
`Turing.MultiTapeTM.relabelState_runFrom_init`. -/
theorem exists_codeTM (M : FinTM Bool) (hk : M.k = 1) :
    ∃ M' : CodeTM, ∀ (x output : List Bool) (t : ℕ),
      M'.toFinTM.ComputesInTime x output t ↔ M.ComputesInTime x output t := by
  classical
  rcases M with @⟨k, Q, hQ, dQ, tm⟩
  dsimp only at hk
  subst k
  letI : Fintype Q := hQ
  letI : DecidableEq Q := dQ
  have hcard : Fintype.card Q = (Fintype.card Q - 1) + 1 := by
    have : 0 < Fintype.card Q := Fintype.card_pos_iff.mpr ⟨tm.q₀⟩
    omega
  let e := Fintype.equivFinOfCardEq hcard
  refine ⟨⟨Fintype.card Q - 1, tm.relabelState e⟩, ?_⟩
  intro x output t
  simp only [CodeTM.toFinTM, FinTM.ComputesInTime, MultiTapeTM.ComputesInTimeAndSpace,
    MultiTapeTM.relabelState_runFrom_init, Cfg.mapState, Option.map_eq_none_iff]
  constructor
  · rintro ⟨s, hhalt, hout, -⟩
    exact ⟨_, hhalt, hout, rfl⟩
  · rintro ⟨s, hhalt, hout, -⟩
    exact ⟨_, hhalt, hout, rfl⟩

end Turing


## ===== TCSlib/Complexity/ClassP/TimeConstructible.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Nat.Bits
import TCSlib.Complexity.TuringMachine.Finite

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Time-constructible functions

A function `T : ℕ → ℕ` is *time constructible* if `T n ≥ n` and some machine computes,
on every input `x`, the binary representation of `T |x|` within at most
`c · (T |x| + 1)` steps for a positive constant `c`. [AB09, §1.3, with the audit-mandated
budget repair below.] Time constructibility rules out pathological time bounds. It is
needed when a machine must *generate* a step budget from its input length, as in the
hierarchy theorems; note that the timed universal machine of [AB09, p. 21] receives its
budget as an explicit extra input and needs no constructibility hypothesis.

## Design and deviations from [AB09]

* Binary representation is `Nat.bits` (least-significant-bit first, with no redundant
  most-significant zeros; `Nat.bits 0 = []`), where [AB09] writes `⌞T(|x|)⌟` without
  fixing endianness. Nothing in Chapter 1 depends on the choice.
* **Deviation (audit-mandated).** [AB09] demands the computation run within exactly
  `T n` steps and then asserts that `n`, `n log n`, `n²`, `2ⁿ` are time constructible.
  The phase-1 external audit (`audits/phase1-findings.md`, finding 1, adversarial cases
  5-6) *proved the literal reading false in this model*: under the exact bound, the
  identity function — [AB09]'s own first example — is not time constructible (on the
  budget `T n = n`, the first transition on `[false]` and `[false, false]` is the same
  function call, and the length-1 budget forces it to halt with output `[true]`, which
  absorption then freezes at length 2), and even `T n = n + 1` fails by an append-only
  prefix argument. We therefore allow a positive constant factor on `T n + 1`, which
  suffices for every downstream use and restores the book's examples *after small-input
  normalization*: the literal `n · ⌈log₂ n⌉`, for instance, still violates `T n ≥ n` at
  `n = 1`, so such examples are stated with a `max`-with-`n` or `+ 1` normalization.
  Exact constants in downstream results must be derived from this form, not inherited
  from the strict reading.

## Main definitions

* `Complexity.TimeConstructible` — [AB09, §1.3], with the constant-slack repair above.

## Main results

* `Complexity.timeConstructible_id` — the identity function is time constructible,
  restoring [AB09]'s example under the repaired definition.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.3, "Time-constructible functions".)
-/

namespace Complexity

open Turing

/-- `T` is time constructible: `T n ≥ n`, and some finite binary machine computes
`x ↦ ⌞T |x|⌟` (binary via `Nat.bits`) within `c · (T |x| + 1)` steps for a positive
constant `c`. [AB09, §1.3], with the constant-slack deviation documented in the module
docstring (the literal exact-`T n` bound is refuted in this model by
`audits/phase1-findings.md`, finding 1). -/
def TimeConstructible (T : ℕ → ℕ) : Prop :=
  (∀ n, n ≤ T n) ∧
  ∃ c : ℕ, 0 < c ∧ ∃ M : FinTM Bool, ∀ x : List Bool,
    M.ComputesInTime x (T x.length).bits (c * (T x.length + 1))

/-- Increment a little-endian binary word, extending it on overflow. -/
private def counterInc : List Bool → List Bool
  | [] => [true]
  | false :: bs => true :: bs
  | true :: bs => false :: counterInc bs

/-- The number of initial true bits cleared by an increment. -/
private def counterCarry : List Bool → ℕ
  | true :: bs => counterCarry bs + 1
  | _ => 0

/-- Each cleared true bit decreases the potential by one; the final write adds one.
This is the local accounting identity behind the amortized bound. -/
private lemma counterInc_potential (bs : List Bool) :
    (counterInc bs).count true + counterCarry bs = bs.count true + 1 := by
  induction bs with
  | nil => simp [counterInc, counterCarry]
  | cons b bs ih =>
    cases b with
    | false => simp [counterInc, counterCarry]
    | true => simp [counterInc, counterCarry]; omega

/-- The list increment is exactly successor in `Nat.bits`, including overflow.
**Proof sketch.** Binary induction: a low zero becomes one without a carry; a
low one becomes zero and applies the induction hypothesis to the high part. -/
private lemma counterInc_bits (n : ℕ) : counterInc n.bits = (n + 1).bits := by
  induction n using Nat.binaryRec' with
  | zero => simp [counterInc]
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn]
    cases b with
    | false =>
      change true :: n.bits = (2 * n + 1).bits
      exact (Nat.bit1_bits n).symm
    | true =>
      simp only [counterInc, ih]
      have he : Nat.bit true n + 1 = 2 * (n + 1) := by simp [Nat.bit_val]; omega
      rw [he, Nat.bit0_bits _ (by omega)]

/-- An increment grows the word by at most one cell, and all cleared cells lie
within the incremented word. -/
private lemma counterInc_length (bs : List Bool) :
    (counterInc bs).length ≤ bs.length + 1 ∧
      counterCarry bs ≤ (counterInc bs).length := by
  induction bs with
  | nil => simp [counterInc, counterCarry]
  | cons b bs ih =>
    cases b <;> simp only [counterInc, counterCarry, List.length_cons] <;> omega

/-- The final emission uses at most `n` symbol-writing steps. -/
private lemma counter_bits_length (n : ℕ) : n.bits.length ≤ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← counterInc_bits]
    have := (counterInc_length n.bits).1
    omega

/-- One carry transition, with the first transition also advancing the input. -/
private def counterBump (d : SignType) (w : Option Bool) : Action 1 Bool (Fin 4) :=
  if w = some true then
    ⟨d, fun _ => (some (some false), .pos), none, some 1⟩
  else ⟨d, fun _ => (some (some true), .neg), none, some 2⟩

/-- The audit's four-state counter: count = 0, carry = 1, rewind = 2, emit = 3.
[AB09, §1.3 examples], implemented by the phase-1 reaudit's transition table. -/
private def counterTM : FinTM Bool where
  k := 1
  State := Fin 4
  tm :=
    { q₀ := 0
      tr := fun q inp work =>
        if q = 0 then
          match inp with
          | none => ⟨.zero, fun _ => (none, .zero), none, some 3⟩
          | some _ => counterBump .pos (work 0)
        else if q = 1 then counterBump .zero (work 0)
        else if q = 2 then
          match work 0 with
          | none => ⟨.zero, fun _ => (none, .pos), none, some 0⟩
          | some _ => ⟨.zero, fun _ => (none, .neg), none, some 2⟩
        else
          match work 0 with
          | none => ⟨.zero, fun _ => (none, .zero), none, none⟩
          | some b => ⟨.zero, fun _ => (none, .pos), some b, some 3⟩ }

/-- A finite word on nonnegative cells, with a blank at every other cell. -/
private def counterTape (bs : List Bool) (z : ℤ) : Option Bool :=
  if z < 0 then none else bs[z.toNat]?

/-- Canonical configurations for carry, rewind, count, and emission invariants. -/
private def counterCfg (x : List Bool) (q : Fin 4) (p : Fin (x.length + 2))
    (z : ℤ) (bs out : List Bool) : Cfg 1 Bool (Fin 4) x :=
  ⟨some q, p, fun _ => counterTape bs, fun _ => z, out⟩

/-- Reading after a prefix gives the head of the remaining word (blank if empty). -/
private lemma counterTape_read (pre bs : List Bool) :
    counterTape (pre ++ bs) pre.length = bs.head? := by
  simp only [counterTape, if_neg (by omega : ¬(pre.length : ℤ) < 0), Int.toNat_natCast,
    List.getElem?_append_right (le_refl _), Nat.sub_self]
  cases bs <;> rfl

/-- Replace the first suffix bit, or extend the word if the suffix is empty.
**Proof sketch.** At the write position use the updated value. Before that
position both tapes read the unchanged prefix; afterwards both read the old tail.
Negative cells remain blank. -/
private lemma counterTape_write (pre bs : List Bool) (b : Bool) :
    Function.update (counterTape (pre ++ bs)) (pre.length : ℤ) (some b) =
      counterTape (pre ++ b :: bs.tail) := by
  funext z
  by_cases hz : z = (pre.length : ℤ)
  · subst z
    simp [counterTape_read]
  · rw [Function.update_of_ne hz]
    unfold counterTape
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
private lemma counter_carry_step (x : List Bool) (p : Fin (x.length + 2))
    (pre bs : List Bool) :
    counterTM.tm.step (counterCfg x 1 p pre.length (pre ++ bs) []) =
      if bs.head? = some true then
        counterCfg x 1 p (pre.length + 1) (pre ++ false :: bs.tail) []
      else counterCfg x 2 p (pre.length - 1) (pre ++ true :: bs.tail) [] := by
  unfold MultiTapeTM.step
  change (counterTM.tm.tr (1 : Fin 4) _ _).apply _ = _
  simp only [counterTM, show (1 : Fin 4) ≠ 0 from by decide, ↓reduceIte]
  change (counterBump .zero (counterTape (pre ++ bs) pre.length)).apply _ = _
  rw [counterTape_read]
  unfold counterBump
  by_cases h : bs.head? = some true <;> simp only [h, ↓reduceIte]
  all_goals
    apply Cfg.ext
    · rfl
    · exact moveInputPos_zero p
    · funext j; exact counterTape_write pre bs _
    · funext j; simp [Action.apply, counterCfg, sub_eq_add_neg]
    · rfl

/-- A carry flips precisely the initial true bits, then writes the final true bit.
**Proof sketch.** Induct on the suffix. The empty suffix and a leading false bit
finish in one step. A leading true bit is replaced by false and included in the
prefix before invoking the induction hypothesis on the tail. -/
private lemma counter_carry (x : List Bool) (p : Fin (x.length + 2))
    (bs : List Bool) : ∀ pre : List Bool,
    counterTM.tm.runFrom (counterCfg x 1 p pre.length (pre ++ bs) [])
        (counterCarry bs + 1) =
      counterCfg x 2 p ((pre.length : ℤ) + counterCarry bs - 1)
        (pre ++ counterInc bs) [] := by
  induction bs with
  | nil =>
    intro pre
    simp only [counterCarry, MultiTapeTM.runFrom_succ_eq_step,
      MultiTapeTM.runFrom_zero, counter_carry_step]
    simp [counterInc]
  | cons b bs ih =>
    intro pre
    cases b with
    | false =>
      simp only [counterCarry, MultiTapeTM.runFrom_succ_eq_step,
        MultiTapeTM.runFrom_zero, counter_carry_step]
      simp [counterInc]
    | true =>
      simp only [counterCarry, MultiTapeTM.runFrom_succ_eq_step, counter_carry_step,
        List.head?_cons, List.tail_cons, ↓reduceIte]
      have h := ih (pre ++ [false])
      rw [MultiTapeTM.runFrom_succ_eq_step] at h
      simpa [counterInc, List.append_assoc, Nat.cast_add, Nat.cast_one,
        add_assoc, add_comm, add_left_comm] using h

/-- Rewind crosses the written prefix, detects the untouched blank at `-1`, and
returns to cell zero in the count state.
**Proof sketch.** Induct on the number of written cells still to cross.
Each bit causes one left move; at `-1` one right move ends the rewind. -/
private lemma counter_rewind (x : List Bool) (p : Fin (x.length + 2))
    (bs : List Bool) : ∀ j (_hj : j ≤ bs.length),
    counterTM.tm.runFrom (counterCfg x 2 p ((j : ℤ) - 1) bs []) (j + 1) =
      counterCfg x 0 p 0 bs [] := by
  intro j
  induction j with
  | zero =>
    intro hj
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    apply Cfg.ext <;>
      simp [MultiTapeTM.step, counterTM, counterCfg, Cfg.workTapeSymbols,
        counterTape, Action.apply]
  | succ j ih =>
    intro hj
    have hw : (counterCfg x 2 p (j : ℤ) bs []).workTapeSymbols 0 = some bs[j] := by
      simp only [counterCfg, Cfg.workTapeSymbols, counterTape,
        if_neg (by omega : ¬(j : ℤ) < 0), Int.toNat_natCast]
      exact List.getElem?_eq_getElem (by omega)
    have hs : counterTM.tm.step (counterCfg x 2 p (j : ℤ) bs []) =
        counterCfg x 2 p ((j : ℤ) - 1) bs [] := by
      unfold MultiTapeTM.step
      change (counterTM.tm.tr (2 : Fin 4) _ _).apply _ = _
      simp only [counterTM, show (2 : Fin 4) ≠ 0 from by decide,
        show (2 : Fin 4) ≠ 1 from by decide, ↓reduceIte, hw]
      apply Cfg.ext
      · rfl
      · exact moveInputPos_zero p
      · rfl
      · funext k; simp [Action.apply, counterCfg, sub_eq_add_neg]
      · rfl
    have he : ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) := by omega
    rw [he, MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- The first carry transition also consumes exactly one input symbol. -/
private lemma counter_start (x : List Bool) (i : ℕ) (hi : i < x.length) (bs : List Bool) :
    counterTM.tm.step (counterCfg x 0 ⟨i + 1, by omega⟩ 0 bs []) =
      counterTM.tm.step (counterCfg x 1 ⟨i + 2, by omega⟩ 0 bs []) := by
  have hs : (counterCfg x 0 ⟨i + 1, by omega⟩ 0 bs []).inputSymbol = some x[i] :=
    inputSymbolInner i (by simp only [counterCfg]; omega) hi
  unfold MultiTapeTM.step
  change (counterTM.tm.tr (0 : Fin 4) _ _).apply _ =
    (counterTM.tm.tr (1 : Fin 4) _ _).apply _
  rw [hs]
  simp only [counterTM, show (1 : Fin 4) ≠ 0 from by decide, ↓reduceIte]
  change (counterBump .pos (counterTape bs 0)).apply _ =
    (counterBump .zero (counterTape bs 0)).apply _
  unfold counterBump
  by_cases h : counterTape bs 0 = some true <;> simp only [h, ↓reduceIte]
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
private lemma counter_increment (x : List Bool) (i : ℕ) (hi : i < x.length)
    (bs : List Bool) :
    counterTM.tm.runFrom (counterCfg x 0 ⟨i + 1, by omega⟩ 0 bs [])
        (2 * counterCarry bs + 2) =
      counterCfg x 0 ⟨i + 2, by omega⟩ 0 (counterInc bs) [] := by
  have hc : counterTM.tm.runFrom (counterCfg x 0 ⟨i + 1, by omega⟩ 0 bs [])
      (counterCarry bs + 1) =
      counterCfg x 2 ⟨i + 2, by omega⟩ ((counterCarry bs : ℤ) - 1) (counterInc bs) [] := by
    rw [MultiTapeTM.runFrom_succ_eq_step, counter_start x i hi,
      ← MultiTapeTM.runFrom_succ_eq_step]
    simpa only [List.length_nil, Nat.cast_zero, zero_add, List.nil_append] using
      counter_carry x ⟨i + 2, by omega⟩ bs []
  rw [show 2 * counterCarry bs + 2 = (counterCarry bs + 1) + (counterCarry bs + 1) by omega,
    MultiTapeTM.runFrom_add, hc]
  exact counter_rewind x ⟨i + 2, by omega⟩ (counterInc bs) (counterCarry bs)
    (counterInc_length bs).2

/-- The counting invariant carries a nonnegative potential of twice the popcount.
**Proof sketch.** Initially both elapsed time and potential are zero. An increment
with `r` cleared bits costs `2r + 2` steps and changes the potential by `2 - 2r`.
Thus elapsed time plus potential increases by exactly four per input symbol.
The semantic invariant records the exact canonical binary word and head positions. -/
private lemma counter_count (x : List Bool) : ∀ i (hi : i ≤ x.length),
    ∃ t, t + 2 * i.bits.count true ≤ 4 * i ∧
      counterTM.tm.runFrom (counterTM.tm.initCfg x) t =
        counterCfg x 0 ⟨i + 1, by omega⟩ 0 i.bits [] := by
  intro i
  induction i with
  | zero =>
    intro hi
    refine ⟨0, by simp, ?_⟩
    apply Cfg.ext
    · rfl
    · rfl
    · funext j z
      simp [MultiTapeTM.initCfg, counterCfg, counterTape]
    · rfl
    · rfl
  | succ i ih =>
    intro hi
    obtain ⟨t, ht, hc⟩ := ih (by omega)
    refine ⟨t + 2 * counterCarry i.bits + 2, ?_, ?_⟩
    · have hp := counterInc_potential i.bits
      rw [counterInc_bits] at hp
      omega
    · rw [show t + 2 * counterCarry i.bits + 2 = t + (2 * counterCarry i.bits + 2) by omega,
        MultiTapeTM.runFrom_add, hc, counter_increment x i (by omega), counterInc_bits]

/-- The emit phase appends exactly the stored prefix, one bit per step.
**Proof sketch.** Induct on the emitted length, using the nonblank cell at each
index below the word length; the tape contents and input position never change. -/
private lemma counter_emit_run (x : List Bool) (p : Fin (x.length + 2))
    (bs : List Bool) : ∀ i (_hi : i ≤ bs.length),
    counterTM.tm.runFrom (counterCfg x 3 p 0 bs []) i =
      counterCfg x 3 p i bs (bs.take i) := by
  intro i
  induction i with
  | zero => intro hi; rfl
  | succ i ih =>
    intro hi
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hw : (counterCfg x 3 p i bs (bs.take i)).workTapeSymbols 0 = some bs[i] := by
      simp only [counterCfg, Cfg.workTapeSymbols, counterTape,
        if_neg (by omega : ¬(i : ℤ) < 0), Int.toNat_natCast]
      exact List.getElem?_eq_getElem (by omega)
    unfold MultiTapeTM.step
    change (counterTM.tm.tr (3 : Fin 4) _ _).apply _ = _
    simp only [counterTM, show (3 : Fin 4) ≠ 0 from by decide,
      show (3 : Fin 4) ≠ 1 from by decide, show (3 : Fin 4) ≠ 2 from by decide,
      ↓reduceIte, hw]
    apply Cfg.ext
    · rfl
    · exact moveInputPos_zero p
    · rfl
    · funext j; simp [Action.apply, counterCfg]
    · simp only [Action.apply, counterCfg]
      rw [List.take_succ, List.getElem?_eq_getElem (by omega)]

/-- At the first blank after the stored word, emission halts without extra output. -/
private lemma counter_emit (x : List Bool) (p : Fin (x.length + 2)) (bs : List Bool) :
    let c := counterTM.tm.runFrom (counterCfg x 3 p 0 bs []) (bs.length + 1)
    c.state = none ∧ c.output = bs := by
  have hw : (counterCfg x 3 p bs.length bs (bs.take bs.length)).workTapeSymbols 0 =
      none := by
    simp only [counterCfg, Cfg.workTapeSymbols, counterTape,
      if_neg (by omega : ¬(bs.length : ℤ) < 0), Int.toNat_natCast]
    exact List.getElem?_eq_none (le_refl _)
  dsimp only
  rw [MultiTapeTM.runFrom_succ_eq_step', counter_emit_run x p bs bs.length (le_refl _)]
  unfold MultiTapeTM.step
  change ((counterTM.tm.tr (3 : Fin 4) _ _).apply _).state = none ∧ _
  simp only [counterTM, show (3 : Fin 4) ≠ 0 from by decide,
    show (3 : Fin 4) ≠ 1 from by decide, show (3 : Fin 4) ≠ 2 from by decide,
    ↓reduceIte, hw]
  simp [Action.apply, counterCfg]

/-- The identity function is time constructible. [AB09, §1.3 examples]

**Proof sketch.** A one-work-tape machine maintains a little-endian binary counter on
its work tape while scanning the input left to right: for each input symbol it
increments the counter (walking right over `true` cells turning them `false` until the
first `false`/blank cell, which becomes `true`, then returning to cell 0). Incrementing
`n` times costs amortized `O(1)` per increment, `O(n)` in total. When the input head
reads the blank past the input, the machine walks the counter left to right emitting
each bit to the output tape (`O(log n)` steps) and halts. The total is at most
`c · (n + 1)` steps for an absolute constant `c`, and the emitted string is `n.bits`
(for `n = 0` the counter region is empty and nothing is emitted, matching
`Nat.bits 0 = []`). The formal proof uses twice the number of true counter bits as
potential: elapsed time plus potential is at most `4n` after `n` increments.
Entering emission and its final halting transition add two steps; the output length
is at most `n`, so `c = 5` suffices. -/
theorem timeConstructible_id : TimeConstructible id := by
  refine ⟨fun n => le_refl n, 5, by decide, counterTM, fun x => ?_⟩
  obtain ⟨t, ht, hc⟩ := counter_count x x.length (le_refl _)
  have hs : counterTM.tm.step
      (counterCfg x 0 ⟨x.length + 1, by omega⟩ 0 x.length.bits []) =
      counterCfg x 3 ⟨x.length + 1, by omega⟩ 0 x.length.bits [] := by
    have hin : (counterCfg x 0 ⟨x.length + 1, by omega⟩ 0 x.length.bits []).inputSymbol =
        none := by simp [Cfg.inputSymbol, counterCfg]
    unfold MultiTapeTM.step
    change (counterTM.tm.tr (0 : Fin 4) _ _).apply _ = _
    rw [hin]
    apply Cfg.ext <;> simp [counterTM, Action.apply, counterCfg]
  have hstart : counterTM.tm.runFrom (counterTM.tm.initCfg x) (t + 1) =
      counterCfg x 3 ⟨x.length + 1, by omega⟩ 0 x.length.bits [] := by
    rw [MultiTapeTM.runFrom_succ_eq_step', hc, hs]
  have he := counter_emit x ⟨x.length + 1, by omega⟩ x.length.bits
  have hbase : counterTM.ComputesInTime x x.length.bits
      ((t + 1) + (x.length.bits.length + 1)) := by
    refine ⟨_, ?_, ?_, rfl⟩
    · rw [MultiTapeTM.runFrom_add, hstart]; exact he.1
    · rw [MultiTapeTM.runFrom_add, hstart]; exact he.2
  apply hbase.mono
  have hl := counter_bits_length x.length
  change (t + 1) + (x.length.bits.length + 1) ≤ 5 * (x.length + 1)
  omega

end Complexity


## ===== TCSlib/Complexity/ClassNP/TMSAT.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Encoding
import TCSlib.Complexity.ClassP.TimeConstructible
import TCSlib.Complexity.ClassNP.PolyTime
import TCSlib.Complexity.ClassNP.Reductions
import TCSlib.Complexity.TuringMachine.Universal
import Mathlib.Tactic.Ring
import Mathlib.Tactic.DeriveFintype

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# TMSAT: the first NP-complete language

[AB09, Theorem 2.9]: the language
`TMSAT = {⟨α, x, 1^n, 1^t⟩ : ∃ u ∈ {0,1}^n, M_α outputs 1 on ⟨x, u⟩ within t
steps}` is `NP`-complete — the "generic" `NP`-complete problem, read off the
definition of `NP` itself. This module defines `TMSAT` over the audited
Chapter-1 machine-code layer and states Theorem 2.9, together with the
polynomial time-constructibility statement the hardness reduction's unary
components rely on.

## Design and deviations from [AB09]

* **The tuple is right-nested `Turing.pairEncode`**:
  `⟨α, x, 1^n, 1^t⟩` is rendered
  `pairEncode α (pairEncode x (pairEncode 1^n 1^t))`, with `1^k` the string
  `List.replicate k true`. The pairing is self-delimiting and injective
  (`Turing.pairEncode_injective`), so the four components are recoverable and
  unique — strings not of this shape are simply not members.
* **"`M_α` outputs `1` on input `⟨x, u⟩` within `t` steps"** is rendered
  `(c.decode α).toFinTM.ComputesInTime (pairEncode x u) [true] t` — completed
  output exactly `[true]` by step `t` (halting is absorbing), the audited
  output-convention of the whole development, against the total decoding of a
  `Turing.MachineCode`. The unary components make `n` and `t` at most the
  input length — [AB09]'s footnote 2: padding the input is what entitles the
  verifier and the reduction to run in time polynomial in `n` and `t`.
* **The generality split refines the audited `HALT` treatment**
  (`Complexity.HALT_NPHard` at `Turing.MachineCode`,
  `Complexity.HALT_not_mem_NP` at `Turing.EffectiveMachineCode`): the language
  and its `NP`-hardness need only a lawful code (`decode` totality and
  `decode_encode`; the reduction writes a *fixed* code string), while
  membership in `NP` runs the universal machine over an input-supplied `α` and
  therefore takes an effective scheme **with a polynomially bounded canonizer**
  — the hypothesis `Complexity.PolyBound c.canonizerTime` on the membership
  and completeness statements. Effectivity alone is **not** enough (round-1
  audit, finding 1, Argument A): `Turing.EffectiveMachineCode` bounds the
  canonizer's computability, not its cost, and a lawful effective scheme can
  plant arbitrarily expensive decidable information behind short codes,
  pushing its `TMSAT` outside `EXP ⊇ NP`. `NP`-completeness carries the same
  hypothesis.
* **`Complexity.timeConstructible_poly` is a new statement about a Chapter-1
  notion** (`Complexity.TimeConstructible`, `ClassP/TimeConstructible.lean`) —
  stated here rather than by editing the frozen audited file, and **flagged for
  this phase's audit** exactly as `Complexity.compl_mem_P` was in phase 1. The
  exponent is `c + 1` because time-constructibility requires `T n ≥ n`, which
  degree `0` would violate.

## Main definitions

* `Complexity.TMSAT` — [AB09, Theorem 2.9's language].

## Main results

* `Complexity.timeConstructible_poly` — `n ↦ C·(n+1)^(c+1)` is
  time-constructible (`C > 0`); the plan's supporting obligation for the
  reduction's unary components. [AB09, §1.3]
* `Complexity.timed_universal_quantitative` — the phase-3-mandated new public
  bridge with an explicit code-length coefficient; its proof is escalated
  under the epoch-2 brief's private-API protocol.
* `Complexity.TMSAT_mem_NP` — for schemes with polynomially bounded
  canonizers, the certificate is `u` itself; verification is timed universal
  simulation. [AB09, Theorem 2.9]
* `Complexity.TMSAT_NPHard` — the generic reduction: send `x` to
  `⟨⌞M⌟, x, 1^{p(|x|)}, 1^{q(m)}⟩`. [AB09, Theorem 2.9]
* `Complexity.TMSAT_NPComplete` — [AB09, Theorem 2.9], under the same
  polynomial-canonizer hypothesis as membership.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Theorem 2.9 with footnote 2, pp. 43-44;
  §1.3 for time constructibility.)
-/

namespace Complexity

open Turing

/-- **The language `TMSAT`** [AB09, Theorem 2.9]: quadruples
`⟨α, x, 1^n, 1^t⟩` — right-nested `Turing.pairEncode`, unary third and fourth
components — such that some certificate `u` of length exactly `n` makes the
machine denoted by `α` (total decoding of the scheme `c`) halt on the paired
input `⟨x, u⟩` within `t` steps with completed output exactly `[true]`. -/
def TMSAT (c : MachineCode) : Language Bool :=
  {y | ∃ (α x u : List Bool) (n t : ℕ),
    y = pairEncode α
          (pairEncode x (pairEncode (List.replicate n true) (List.replicate t true))) ∧
    u.length = n ∧
    (c.decode α).toFinTM.ComputesInTime (pairEncode x u) [true] t}

/-! ### Exact unary polynomial generation

The following private machine enumerates a fixed-dimensional box of side
`|x| + 1`. Its output is a unary polynomial, so composing it with the public
linear-time binary length counter gives an exact binary polynomial value.
No private declaration from the Chapter-1 counter is used.
-/

/-- Control for copying the side length, nested unary loops, and constant emission. -/
private inductive PolyControl (c C : ℕ) where
  | copy | setup
  | loop (i : Fin (c + 1))
  | rewind (i : Fin (c + 1))
  | advance (i : Fin (c + 2))
  | emit (j : Fin (C + 1))

/-- Enumerate the control through a finite sum representation, privately. -/
private instance polyControlFintype (c C : ℕ) : Fintype (PolyControl c C) :=
  derive_fintype% _

/-- Compare control states through the same finite sum representation, privately. -/
private instance polyControlDecidableEq (c C : ℕ) : DecidableEq (PolyControl c C) :=
  (proxy_equiv% (PolyControl c C)).symm.decidableEq

/-- A unary word of length `q`, surrounded by blanks. -/
private def polyTape (q : ℕ) (z : ℤ) : Option Bool :=
  if 0 ≤ z ∧ z < q then some true else none

/-- Move just the selected work head, preserving every tape. -/
private def polyMove {c C : ℕ} (i : Fin (c + 1)) (d : SignType)
    (s : PolyControl c C) : Action (c + 1) Bool (PolyControl c C) :=
  ⟨0, fun j => (none, if j = i then d else 0), none, some s⟩

/-- Finite machine emitting `C` symbols at each point of a `(c+1)`-dimensional
box. The unary loop tapes are copied in parallel; rewinding a completed inner
loop costs its side length, charged to the iterations that just completed. -/
private def polyUnaryTM (c C : ℕ) : FinTM Bool where
  k := c + 1
  State := PolyControl c C
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
        if w i = none then polyMove i .neg (.rewind i)
        else ⟨0, fun _ => (none, 0), none,
          some (if h : i.val = 0 then .emit ⟨C, Nat.lt_succ_self C⟩
            else .loop ⟨i.val - 1, by omega⟩)⟩
      | .rewind i =>
        if w i = none then polyMove i .pos (.advance ⟨i.val + 1, by omega⟩)
        else polyMove i .neg (.rewind i)
      | .advance i =>
        if h : i.val < c + 1 then polyMove ⟨i.val, h⟩ .pos (.loop ⟨i.val, h⟩)
        else ⟨0, fun _ => (none, 0), none, none⟩
      | .emit j =>
        if h : j.val = 0 then ⟨0, fun _ => (none, 0), none, some (.advance 0)⟩
        else ⟨0, fun _ => (none, 0), some true,
          some (.emit ⟨j.val - 1, by omega⟩)⟩ }

/-- A loop configuration, with all unary tapes installed and arbitrary head positions. -/
private def polyCfg {c C : ℕ} (x : List Bool) (q : ℕ)
    (s : PolyControl c C) (h : Fin (c + 1) → ℤ) (o : List Bool) :
    Cfg (c + 1) Bool (PolyControl c C) x :=
  ⟨some s, ⟨x.length + 1, by omega⟩, fun _ => polyTape q, h, o⟩

/-- Applying a head-only action updates exactly the selected head. -/
private lemma polyMove_apply {c C : ℕ} (x : List Bool) (q : ℕ)
    (s s' : PolyControl c C) (h : Fin (c + 1) → ℤ) (o : List Bool)
    (i : Fin (c + 1)) (d : SignType) :
    (polyMove i d s').apply (polyCfg x q s h o) =
      polyCfg x q s' (Function.update h i (h i + d.cast)) o := by
  apply Cfg.ext
  · rfl
  · exact moveInputPos_zero _
  · rfl
  · funext j
    by_cases hj : j = i <;> simp [polyMove, polyCfg, Action.apply, hj]
  · simp [polyMove, polyCfg, Action.apply]

/-- The finite emission chain appends exactly its remaining number of true bits. -/
private lemma poly_emit {c C : ℕ} (x : List Bool) (q : ℕ)
    (h : Fin (c + 1) → ℤ) : ∀ j (hj : j ≤ C) (o : List Bool),
    (polyUnaryTM c C).tm.runFrom
      (polyCfg x q (.emit ⟨j, by omega⟩) h o) (j + 1) =
      polyCfg x q (.advance 0) h (o ++ List.replicate j true) := by
  intro j
  induction j with
  | zero =>
    intro hj o
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    apply Cfg.ext <;> simp [MultiTapeTM.step, polyUnaryTM, polyCfg, Action.apply]
  | succ j ih =>
    intro hj o
    have hs : (polyUnaryTM c C).tm.step
        (polyCfg x q (.emit ⟨j + 1, by omega⟩) h o) =
        polyCfg x q (.emit ⟨j, by omega⟩) h (o ++ [true]) := by
      apply Cfg.ext <;> simp [MultiTapeTM.step, polyUnaryTM, polyCfg, Action.apply]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs, ih (by omega)]
    simp [List.replicate_succ, List.append_assoc]

/-- Rewinding crosses a unary prefix and its left boundary, restoring head zero.
The other loop heads and the accumulated output remain unchanged. -/
private lemma poly_rewind {c C : ℕ} (x : List Bool) (q : ℕ)
    (h : Fin (c + 1) → ℤ) (o : List Bool) (i : Fin (c + 1)) :
    ∀ j (_hj : j ≤ q),
    (polyUnaryTM c C).tm.runFrom
      (polyCfg x q (.rewind i) (Function.update h i ((j : ℤ) - 1)) o) (j + 1) =
      polyCfg x q (.advance ⟨i.val + 1, by omega⟩) (Function.update h i 0) o := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    change ((if _ then _ else _) : Action (c + 1) Bool (PolyControl c C)).apply _ = _
    simp only [Cfg.workTapeSymbols, polyCfg, Function.update_self,
      Nat.cast_zero, zero_sub, polyTape, show ¬(0 ≤ (-1 : ℤ) ∧ (-1 : ℤ) < q) by omega,
      ↓reduceIte]
    simpa [polyCfg] using polyMove_apply x q (.rewind i)
      (.advance ⟨i.val + 1, by omega⟩) (Function.update h i (-1)) o i .pos
  | succ j ih =>
    intro hj
    have hs : (polyUnaryTM c C).tm.step
        (polyCfg x q (.rewind i) (Function.update h i ((j + 1 : ℕ) - 1 : ℤ)) o) =
        polyCfg x q (.rewind i) (Function.update h i ((j : ℤ) - 1)) o := by
      change ((if _ then _ else _) : Action (c + 1) Bool (PolyControl c C)).apply _ = _
      simp only [Cfg.workTapeSymbols, polyCfg, Function.update_self,
        Nat.cast_add, Nat.cast_one, add_sub_cancel_right, polyTape,
        if_pos (show 0 ≤ (j : ℤ) ∧ (j : ℤ) < q by omega),
        reduceCtorEq, ↓reduceIte]
      simpa [polyCfg, sub_eq_add_neg] using polyMove_apply x q (.rewind i)
        (.rewind i) (Function.update h i (j : ℤ)) o i .neg
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Returning from an inner loop advances the next outer loop by one cell. -/
private lemma poly_advance {c C : ℕ} (x : List Bool) (q : ℕ)
    (h : Fin (c + 1) → ℤ) (o : List Bool) (i : Fin (c + 1)) :
    (polyUnaryTM c C).tm.step
      (polyCfg x q (.advance ⟨i.val, by omega⟩) h o) =
      polyCfg x q (.loop i) (Function.update h i (h i + 1)) o := by
  simp only [MultiTapeTM.step, polyUnaryTM, polyCfg, i.isLt, ↓reduceDIte]
  simpa [polyCfg] using polyMove_apply x q
    (.advance ⟨i.val, by omega⟩) (.loop i) h o i .pos

/-- Exact time for a full nest of unary loops, with `r` loop levels. -/
private def polyCost (q C : ℕ) : ℕ → ℕ
  | 0 => C + 1
  | r + 1 => q * (polyCost q C r + 2) + q + 2

/-- A loop at level `i` executes its remaining iterations, resets its head,
and returns to its parent with exactly `C*q^i` new symbols per iteration.

**Proof sketch.** Induct on the nesting level, then on the number of remaining
iterations. At level zero the body is the finite emission chain. At higher
levels it is a complete inner loop. Each body has one dispatch and one parent
advance; after the final iteration the unary rewind restores the head to zero.
The invariant leaves all outer heads arbitrary, making recursive calls composable. -/
private lemma poly_loop {c C : ℕ} (x : List Bool) (q : ℕ) (_hq : 0 < q) :
    ∀ i (hi : i < c + 1) (h : Fin (c + 1) → ℤ)
      (_hh : ∀ k, k.val ≤ i → h k = 0) (o : List Bool) (r j : ℕ), j + r = q →
    (polyUnaryTM c C).tm.runFrom
      (polyCfg x q (.loop ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ (j : ℤ)) o)
      (r * (polyCost q C i + 2) + q + 2) =
      polyCfg x q (.advance ⟨i + 1, by omega⟩) h
        (o ++ List.replicate (r * (C * q ^ i)) true) := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi h hh o r
    have hbody (j : ℕ) (hj : j < q) (o : List Bool) :
        (polyUnaryTM c C).tm.runFrom
          (polyCfg x q (.loop ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ (j : ℤ)) o)
          (polyCost q C i + 2) =
        polyCfg x q (.loop ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ ((j : ℤ) + 1))
          (o ++ List.replicate (C * q ^ i) true) := by
      let h' := Function.update h ⟨i, hi⟩ (j : ℤ)
      have hread : (polyCfg (C := C) x q (.loop ⟨i, hi⟩) h' o).workTapeSymbols ⟨i, hi⟩ =
          some true := by simp [h', polyCfg, Cfg.workTapeSymbols, polyTape, hj]
      have hs : (polyUnaryTM c C).tm.step (polyCfg x q (.loop ⟨i, hi⟩) h' o) =
          polyCfg x q (if hz : i = 0 then .emit ⟨C, by omega⟩
            else .loop ⟨i - 1, by omega⟩) h' o := by
        unfold MultiTapeTM.step
        change ((polyUnaryTM c C).tm.tr (.loop ⟨i, hi⟩) _ _).apply _ = _
        simp only [polyUnaryTM, hread, reduceCtorEq, ↓reduceIte]
        apply Cfg.ext <;> simp [polyCfg, Action.apply]
      by_cases hz : i = 0
      · subst i
        simp only [↓reduceDIte] at hs
        change (polyUnaryTM c C).tm.runFrom (polyCfg x q (.loop 0) h' o) _ = _
        rw [show polyCost q C 0 + 2 = 1 + (C + 1) + 1 by simp [polyCost]; omega,
          MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add,
          show (polyUnaryTM c C).tm.runFrom (polyCfg x q (.loop 0) h' o) 1 =
            polyCfg x q (.emit ⟨C, by omega⟩) h' o by simpa using hs,
          poly_emit x q h' C (le_refl C),
          MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
        simpa [h'] using poly_advance (C := C) x q h'
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
        have hinner' : (polyUnaryTM c C).tm.runFrom
            (polyCfg x q (.loop ⟨i - 1, by omega⟩) h' o) (polyCost q C i) =
            polyCfg x q (.advance ⟨i, by omega⟩) h'
              (o ++ List.replicate (C * q ^ i) true) := by
          have hcost : q * (polyCost q C (i - 1) + 2) + q + 2 =
              polyCost q C i := by
            calc
              _ = polyCost q C (i - 1 + 1) := rfl
              _ = polyCost q C i := by rw [hi']
          simpa only [hcost, hi', hout] using hinner
        change (polyUnaryTM c C).tm.runFrom (polyCfg x q (.loop ⟨i, hi⟩) h' o) _ = _
        rw [show polyCost q C i + 2 = 1 + polyCost q C i + 1 by omega,
          MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add,
          show (polyUnaryTM c C).tm.runFrom (polyCfg x q (.loop ⟨i, hi⟩) h' o) 1 =
            polyCfg x q (.loop ⟨i - 1, by omega⟩) h' o by simpa using hs,
          hinner', MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
        simpa [h'] using poly_advance (C := C) x q h'
          (o ++ List.replicate (C * q ^ i) true) (⟨i, hi⟩ : Fin (c + 1))
    induction r generalizing o with
    | zero =>
      intro j hj
      have hj' : j = q := by omega
      subst j
      have hs : (polyUnaryTM c C).tm.step
          (polyCfg x q (.loop ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ (q : ℤ)) o) =
          polyCfg x q (.rewind ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ ((q : ℤ) - 1)) o := by
        unfold MultiTapeTM.step
        change ((polyUnaryTM c C).tm.tr (.loop ⟨i, hi⟩) _ _).apply _ = _
        simp only [polyUnaryTM, Cfg.workTapeSymbols, polyCfg, Function.update_self,
          polyTape, lt_self_iff_false, and_false, ↓reduceIte]
        simpa [polyCfg, sub_eq_add_neg] using polyMove_apply x q (.loop ⟨i, hi⟩)
          (.rewind ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ (q : ℤ)) o ⟨i, hi⟩ .neg
      simp only [Nat.zero_mul, Nat.zero_add, List.replicate_zero, List.append_nil]
      rw [MultiTapeTM.runFrom_succ_eq_step, hs, poly_rewind x q h o ⟨i, hi⟩ q (le_refl q)]
      rw [← hh ⟨i, hi⟩ (le_refl _), Function.update_eq_self]
    | succ r ihr =>
      intro j hj
      have hjq : j < q := by omega
      rw [show (r + 1) * (polyCost q C i + 2) + q + 2 =
          (polyCost q C i + 2) + (r * (polyCost q C i + 2) + q + 2) by ring,
        MultiTapeTM.runFrom_add, hbody j hjq]
      have hr := ihr (o ++ List.replicate (C * q ^ i) true) (j + 1) (by omega)
      simp only [Nat.cast_add, Nat.cast_one] at hr
      rw [hr, List.append_assoc, ← List.replicate_add]
      congr 3
      ring

/-- Writing at the first blank extends a unary tape by exactly one cell. -/
private lemma polyTape_write (q : ℕ) :
    Function.update (polyTape q) (q : ℤ) (some true) = polyTape (q + 1) := by
  funext z
  by_cases hz : z = (q : ℤ)
  · subst z
    simp [polyTape]
  · rw [Function.update_of_ne hz]
    unfold polyTape
    have he : (0 ≤ z ∧ z < (q : ℤ)) ↔ (0 ≤ z ∧ z < ((q + 1 : ℕ) : ℤ)) := by omega
    simp only [he]

/-- The full loop costs at most a constant times the number of box points.
Each level's rewinds are charged to its `q` completed body iterations. -/
private lemma polyCost_le (q C : ℕ) (hq : 0 < q) : ∀ r,
    polyCost q C r ≤ (C + 1 + 5 * r) * q ^ r := by
  intro r
  induction r with
  | zero => simp [polyCost]
  | succ r ih =>
    have hqpow : q ≤ q ^ (r + 1) := by
      simpa only [Nat.pow_one] using Nat.pow_le_pow_right hq (show 1 ≤ r + 1 by omega)
    have hpos : 1 ≤ q ^ (r + 1) := Nat.one_le_pow _ _ hq
    calc
      polyCost q C (r + 1) = q * (polyCost q C r + 2) + q + 2 := rfl
      _ ≤ q * ((C + 1 + 5 * r) * q ^ r + 2) + q + 2 :=
        Nat.add_le_add_right (Nat.add_le_add_right
          (Nat.mul_le_mul_left q (Nat.add_le_add_right ih 2)) q) 2
      _ = (C + 1 + 5 * r) * q ^ (r + 1) + 3 * q + 2 := by rw [Nat.pow_succ]; ring
      _ ≤ (C + 1 + 5 * r) * q ^ (r + 1) + 5 * q ^ (r + 1) := by omega
      _ = (C + 1 + 5 * (r + 1)) * q ^ (r + 1) := by ring

/-- Configurations while copying the input length to every unary loop tape. -/
private def polyCopyCfg (c C : ℕ) (x : List Bool) (i : ℕ) (hi : i ≤ x.length) :
    Cfg (c + 1) Bool (PolyControl c C) x :=
  ⟨some .copy, ⟨i + 1, by omega⟩, fun _ => polyTape i, fun _ => i, []⟩

/-- One input scan copies its length, in unary, onto every loop tape at once. -/
private lemma poly_copy (c C : ℕ) (x : List Bool) : ∀ i (hi : i ≤ x.length),
    (polyUnaryTM c C).tm.runFrom ((polyUnaryTM c C).tm.initCfg x) i =
      polyCopyCfg c C x i hi := by
  intro i
  induction i with
  | zero =>
    intro hi
    apply Cfg.ext
    · rfl
    · rfl
    · funext k z
      simp [MultiTapeTM.initCfg, Cfg.init, polyCopyCfg, polyTape,
        show ¬(0 ≤ z ∧ z < (0 : ℤ)) by omega]
    · rfl
    · rfl
  | succ i ih =>
    intro hi
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hin : (polyCopyCfg c C x i (by omega)).inputSymbol = some x[i] :=
      inputSymbolInner i (by simp [polyCopyCfg, Nat.add_comm]) (by omega)
    unfold MultiTapeTM.step
    change ((polyUnaryTM c C).tm.tr .copy _ _).apply _ = _
    rw [hin]
    apply Cfg.ext
    · rfl
    · apply Fin.ext
      change (moveInputPos (⟨i + 1, by omega⟩ : Fin (x.length + 2)) .pos).val = i + 1 + 1
      rw [moveInputPos_pos_of_ne_right _ (by simp; omega)]
    · funext k
      exact polyTape_write i
    · funext k
      simp [polyUnaryTM, polyCopyCfg, Action.apply, Nat.add_comm]
    · rfl

/-- The startup rewind moves all synchronized heads left, then enters the outermost loop. -/
private lemma poly_setup (c C : ℕ) (x : List Bool) (q : ℕ) : ∀ j (_hj : j ≤ q),
    (polyUnaryTM c C).tm.runFrom
      (polyCfg x q .setup (fun _ => (j : ℤ) - 1) []) (j + 1) =
      polyCfg x q (.loop (Fin.last c)) (fun _ => 0) [] := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    apply Cfg.ext <;>
      simp [MultiTapeTM.step, polyUnaryTM, polyCfg, Cfg.workTapeSymbols, polyTape, Action.apply]
  | succ j ih =>
    intro hj
    have hs : (polyUnaryTM c C).tm.step
        (polyCfg x q .setup (fun _ => ((j + 1 : ℕ) : ℤ) - 1) []) =
        polyCfg x q .setup (fun _ => (j : ℤ) - 1) [] := by
      apply Cfg.ext <;>
        simp [MultiTapeTM.step, polyUnaryTM, polyCfg, Cfg.workTapeSymbols, polyTape,
          show (j : ℤ) < q by omega, Action.apply, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Startup installs side length `|x|+1` and puts every loop head at zero.
The final extra unary cell handles empty input without a special case. -/
private lemma poly_start (c C : ℕ) (x : List Bool) :
    (polyUnaryTM c C).tm.runFrom ((polyUnaryTM c C).tm.initCfg x)
      (2 * (x.length + 1)) =
      polyCfg x (x.length + 1) (.loop (Fin.last c)) (fun _ => 0) [] := by
  have hs : (polyUnaryTM c C).tm.step
      (polyCopyCfg c C x x.length (le_refl _)) =
      polyCfg x (x.length + 1) .setup (fun _ => (x.length : ℤ) - 1) [] := by
    have hin : (polyCopyCfg c C x x.length (le_refl _)).inputSymbol = none := by
      simp [polyCopyCfg, Cfg.inputSymbol]
    unfold MultiTapeTM.step
    change ((polyUnaryTM c C).tm.tr .copy _ _).apply _ = _
    rw [hin]
    apply Cfg.ext
    · rfl
    · exact moveInputPos_zero _
    · funext k
      exact polyTape_write x.length
    · funext k
      simp [polyUnaryTM, polyCopyCfg, polyCfg, Action.apply, sub_eq_add_neg]
    · rfl
  have hpre : (polyUnaryTM c C).tm.runFrom ((polyUnaryTM c C).tm.initCfg x)
      (x.length + 1) =
      polyCfg x (x.length + 1) .setup (fun _ => (x.length : ℤ) - 1) [] := by
    rw [MultiTapeTM.runFrom_succ_eq_step', poly_copy c C x x.length (le_refl _), hs]
  rw [show 2 * (x.length + 1) = (x.length + 1) + (x.length + 1) by omega,
    MultiTapeTM.runFrom_add, hpre]
  exact poly_setup c C x (x.length + 1) x.length (by omega)

/-- The explicit generator computes the exact unary polynomial in linear time
in its number of box points. This includes coefficient zero and empty input.

**Proof sketch.** Startup costs `2(n+1)`. The full outer loop emits
`C(n+1)^(c+1)` symbols and costs at most `(C+1+5(c+1))(n+1)^(c+1)`.
One final transition halts; `n+1 ≤ (n+1)^(c+1)` absorbs startup. -/
private lemma poly_unary_computes (c C : ℕ) :
    (polyUnaryTM c C).ComputesFunInTime
      (fun x => List.replicate (C * (x.length + 1) ^ (c + 1)) true)
      (fun n => (C + 5 * (c + 1) + 4) * (n + 1) ^ (c + 1)) := by
  intro x
  have hl := poly_loop (c := c) (C := C) x (x.length + 1) (Nat.succ_pos _) c (by omega)
    (fun _ => 0) (by simp) [] (x.length + 1) 0 (by omega)
  have hout : (x.length + 1) * (C * (x.length + 1) ^ c) =
      C * (x.length + 1) ^ (c + 1) := by rw [Nat.pow_succ]; ring
  have hloop : (polyUnaryTM c C).tm.runFrom
      (polyCfg x (x.length + 1) (.loop (Fin.last c)) (fun _ => 0) [])
      (polyCost (x.length + 1) C (c + 1)) =
      polyCfg x (x.length + 1) (.advance (Fin.last (c + 1))) (fun _ => 0)
        (List.replicate (C * (x.length + 1) ^ (c + 1)) true) := by
    simpa [polyCost, hout] using hl
  have hbase : (polyUnaryTM c C).ComputesInTime x
      (List.replicate (C * (x.length + 1) ^ (c + 1)) true)
      (2 * (x.length + 1) + polyCost (x.length + 1) C (c + 1) + 1) := by
    apply (FinTM.computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_add, poly_start, hloop]
    simp [MultiTapeTM.step, polyUnaryTM, polyCfg, Action.apply]
  apply hbase.mono
  have hp : x.length + 1 ≤ (x.length + 1) ^ (c + 1) := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right (Nat.succ_pos x.length)
      (show 1 ≤ c + 1 by omega)
  have hpos : 1 ≤ (x.length + 1) ^ (c + 1) := Nat.one_le_pow _ _ (Nat.succ_pos _)
  calc
    _ ≤ 2 * (x.length + 1) +
        (C + 1 + 5 * (c + 1)) * (x.length + 1) ^ (c + 1) + 1 :=
      Nat.add_le_add_right (Nat.add_le_add_left
        (polyCost_le (x.length + 1) C (Nat.succ_pos _) (c + 1)) _) 1
    _ ≤ (C + 1 + 5 * (c + 1)) * (x.length + 1) ^ (c + 1) +
        3 * (x.length + 1) ^ (c + 1) := by omega
    _ = _ := by ring

/-- **Polynomial bounds are time constructible**: for `C > 0`, the function
`n ↦ C·(n+1)^(c+1)` is `Complexity.TimeConstructible`. (A **new statement about
the Chapter-1 notion**, flagged for this phase's audit — see the deviations
list; the exponent `c + 1` keeps `T n ≥ n`, which degree `0` would violate.)
This is the plan's supporting obligation for the `TMSAT` reduction's unary
components.

**Proof sketch.** The bound `n ≤ n + 1 ≤ C·(n+1)^(c+1)` holds since `C ≥ 1`.
The machine: scan the input once, incrementing a little-endian binary counter
per cell to obtain `n` (the audited `Complexity.timeConstructible_id` fill is
the in-repo precedent; its private counter layer is a template, not a citable
API — phase-1 audit, finding 5); then compute `(n+1)^(c+1)` by `c + 1`
successive schoolbook binary multiplications and multiply by the constant `C`
(a fixed number of multiplications on operands of `O((c+1)·log(n+2) + log(C+1))`
bits, each polynomial in the bit length); emit the result as
`(T |x|).bits` (little-endian, the `Complexity.TimeConstructible` output
convention). Budget: the scan is `n` steps and the arithmetic polylogarithmic,
against the constant-slack budget `c'·(C·(n+1)^(c+1) + 1)` — ample.

**Implementation note (epoch 2).** The formal proof uses an exact unary
box-enumeration machine followed by the public linear-time binary length
counter, rather than formalizing schoolbook multiplication. Each of `c+1`
unary loop tapes has length `n+1`; each box point emits exactly `C` bits.
The generator costs at most `(C+5(c+1)+4)(n+1)^(c+1)`; timed composition with
`timeConstructible_id` preserves linear time in the polynomial's value.
This is a proof-route deviation only; the frozen statement is unchanged. -/
theorem timeConstructible_poly (C c : ℕ) (hC : 0 < C) :
    TimeConstructible fun n => C * (n + 1) ^ (c + 1) := by
  have hdom (n : ℕ) : (n + 1) ^ (c + 1) ≤ C * (n + 1) ^ (c + 1) := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right ((n + 1) ^ (c + 1)) hC
  refine ⟨fun n => ?_, ?_⟩
  · have hp : n + 1 ≤ (n + 1) ^ (c + 1) := by
      simpa only [Nat.pow_one] using Nat.pow_le_pow_right (Nat.succ_pos n)
        (show 1 ≤ c + 1 by omega)
    exact (Nat.le_succ n).trans (hp.trans (hdom n))
  · obtain ⟨_, a, ha, M, hM⟩ := timeConstructible_id
    have hcounter : M.ComputesFunInTime (fun x => x.length.bits) (fun n => a * (n + 1)) :=
      hM
    obtain ⟨N, b, hN⟩ := FinTM.computesFunInTime_comp (poly_unary_computes c C) hcounter
      (by intro m n h; exact Nat.mul_le_mul_left a (Nat.add_le_add_right h 1))
    let A := C + 5 * (c + 1) + 4
    refine ⟨(b + 1) * (a + 1) * (A + 1),
      Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)) (Nat.succ_pos _), N, ?_⟩
    intro x
    have hb := hN x
    simp only [Function.comp_apply, List.length_replicate] at hb
    apply hb.mono
    have hmajor : A * (x.length + 1) ^ (c + 1) + 1 ≤
        (A + 1) * (C * (x.length + 1) ^ (c + 1) + 1) := by
      have hm := Nat.mul_le_mul_left A (hdom x.length)
      simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
      omega
    change b * (A * (x.length + 1) ^ (c + 1) +
        a * (A * (x.length + 1) ^ (c + 1) + 1) + 1) ≤ _
    calc
      _ = b * (a + 1) * (A * (x.length + 1) ^ (c + 1) + 1) := by ring
      _ ≤ (b + 1) * (a + 1) *
          ((A + 1) * (C * (x.length + 1) ^ (c + 1) + 1)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_right (a + 1) (Nat.le_succ b)) hmajor
      _ = _ := by ring

/-! ### Quantitative timed-universal bridge -/

/-- The canonizer's completed serialization cannot be longer than its run. -/
private lemma tmsat_serialization_length (c : EffectiveMachineCode) (α : List Bool) :
    (c.decode α).serialize.length ≤ c.canonizerTime α.length := by
  have hout := ((FinTM.computesInTime_iff _ _ _ _).mp (c.canonizer_computes α)).2
  simpa only [hout] using c.canonizer.tm.output_length_le α (c.canonizerTime α.length)

/-- Flattening a nonempty word for each element cannot shorten a list. -/
private lemma tmsat_flatMap_length {A B : Type} (f : A → List B)
    (hf : ∀ a, 1 ≤ (f a).length) (l : List A) : l.length ≤ (l.flatMap f).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.length_cons, List.flatMap_cons, List.length_append]
    have := hf a
    omega

/-- Every transition record contains at least its two-bit input-head action. -/
private lemma tmsat_action_nonempty {n : ℕ} (a : Action 1 Bool (Fin (n + 1))) :
    1 ≤ (actionBits a).length := by
  have hs : 2 ≤ (signBits a.inputTape).length := by
    cases a.inputTape <;> exact Nat.le_refl 2
  change 1 ≤ (signBits a.inputTape ++ optOptBoolBits (a.workTapes 0).1 ++
    signBits (a.workTapes 0).2 ++ optBoolBits a.output ++ optStateBits a.state).length
  simp only [List.length_append]
  omega

/-- The canonical serialization bounds the bit-header length, initial-state
index, and total number of states.

**Proof sketch.** The header contains the first two fields. Each state has a
nonempty transition record in the serialized table, so its number of records
also bounds the state count. This uses the public serialization definition. -/
private lemma tmsat_serialization_parameters (M : CodeTM) :
    (Nat.bits M.numStates).length ≤ M.serialize.length ∧
      M.tm.q₀.val ≤ M.serialize.length ∧ M.numStates + 1 ≤ M.serialize.length := by
  let f := fun q : Fin (M.numStates + 1) =>
    ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
      ([none, some false, some true] : List (Option Bool)).flatMap fun w =>
        actionBits (M.tm.tr q inp fun _ => w)
  have hf (q : Fin (M.numStates + 1)) : 1 ≤ (f q).length := by
    dsimp only [f]
    simp only [List.flatMap_cons, List.flatMap_nil, List.length_append, List.length_nil]
    have := tmsat_action_nonempty (M.tm.tr q none (fun _ => none))
    omega
  have htable : M.numStates + 1 ≤ ((List.finRange (M.numStates + 1)).flatMap f).length := by
    simpa only [List.length_finRange] using tmsat_flatMap_length f hf
      (List.finRange (M.numStates + 1))
  have hlen : M.serialize.length = 2 * (Nat.bits M.numStates).length + 2 +
      (M.tm.q₀.val + 1 + ((List.finRange (M.numStates + 1)).flatMap f).length) := by
    change (pairEncode (Nat.bits M.numStates)
      ((List.replicate M.tm.q₀.val true ++ [false]) ++
        (List.finRange (M.numStates + 1)).flatMap f)).length = _
    simp only [universal_pair_length, List.length_append,
      List.length_replicate, List.length_cons, List.length_nil]
  rw [hlen]
  omega

/-- The concrete coefficient displayed in the private timed-simulator proof
is bounded by the mandated public bridge's closed coefficient.

**Proof sketch.** The serialization, header length, initial index, and state
count are each bounded by the canonizer time. Expanding the concrete startup
and block coefficients gives one canonizer term plus thirteen such bounded
terms and constant fifty. This is solely an arithmetic bound on the displayed
expression, not a bound on `timed_universal`'s arbitrary existential witness. -/
private lemma tmsat_concrete_coefficient (c : EffectiveMachineCode) (α : List Bool) :
    3 * α.length + c.canonizerTime α.length + (c.decode α).serialize.length +
      2 * (Nat.bits (c.decode α).numStates).length + 2 * (c.decode α).tm.q₀.val + 16 +
      universalBlockBound c α + 14 ≤ 3 * α.length + 14 * c.canonizerTime α.length + 50 := by
  have hlen := tmsat_serialization_length c α
  obtain ⟨hbits, hstart, hstates⟩ := tmsat_serialization_parameters (c.decode α)
  unfold universalBlockBound
  omega

/-- A single timed simulator, selected before the code and input, preserves
both successful completion and timeout with the explicit budget
`(3|α| + 14*canonizerTime(|α|) + 50)*(t+1)^2`.
[AB09, §1.4.1, time-bounded universal simulation], with explicit constants.

**The phase-3-mandated bridge statement: new public surface for the epoch-2
audit.** Its coefficient is the displayed function of the code length; no
bound on an arbitrary existential witness of `Turing.timed_universal` is asserted.

**Proof sketch and escalation (bridge protocol, step 3).** Reuse the concrete
timed simulator's construction, bound the decoded serialization length by the
canonizer's output-time bound, and bound the state/header sizes by that
serialization. The existing proof's coefficient is then at most the displayed
coefficient. At this pin, the concrete simulator `timedUniversalTM`, its
`timedStartupBound`, and its exact bounded-answer lemma `timed_computes` in
`Universal.lean` are private. The public API exposes only the existential
coefficient, so the construction cannot be reused through that API. This single
bridge declaration is intentionally admitted under the brief's escalation
protocol: the maintainer must export a quantitative concrete bounded-answer
lemma from Chapter 1 (including its timeout branch) and discharge this proof.
Chapter-1 sources are unchanged.

**Discharged (2026-10-03, maintainer serial merge).** Chapter 1 now exports
`Turing.timed_universal_concrete`: the concrete simulator's bounded-answer
theorem with the private startup expression expanded into public vocabulary
and both clauses preserved. This proof is that export, the arithmetic bound
`tmsat_concrete_coefficient` on its displayed coefficient, and
`Turing.FinTM.ComputesInTime.mono`. The escalation paragraph above is
retained as audit history; its final sentence described the pre-export
state, and the export is flagged for the shared infrastructure audit
round. -/
theorem timed_universal_quantitative (c : EffectiveMachineCode) :
    ∃ U : FinTM Bool, ∀ (α x : List Bool) (t : ℕ),
      (∀ output : List Bool,
        (c.decode α).toFinTM.ComputesInTime x output t →
        U.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x)
          (true :: output)
          ((3 * α.length + 14 * c.canonizerTime α.length + 50) * (t + 1) ^ 2)) ∧
      ((∀ output : List Bool, ¬(c.decode α).toFinTM.ComputesInTime x output t) →
        U.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x)
          [false]
          ((3 * α.length + 14 * c.canonizerTime α.length + 50) * (t + 1) ^ 2)) := by
  obtain ⟨U, hU⟩ := timed_universal_concrete c
  refine ⟨U, fun α x t => ?_⟩
  obtain ⟨hsucc, htimeout⟩ := hU α x t
  have hle : (3 * α.length + c.canonizerTime α.length +
      (c.decode α).serialize.length +
      2 * (Nat.bits (c.decode α).numStates).length +
      2 * (c.decode α).tm.q₀.val + 16 +
      universalBlockBound c α + 14) * (t + 1) ^ 2 ≤
      (3 * α.length + 14 * c.canonizerTime α.length + 50) * (t + 1) ^ 2 :=
    Nat.mul_le_mul_right _ (tmsat_concrete_coefficient c α)
  exact ⟨fun output hout => (hsucc output hout).mono hle,
    fun hnone => (htimeout hnone).mono hle⟩

/-- The exact success-tagged output or timeout answer of a bounded source run. -/
private def tmsatAnswer (c : MachineCode) (α x : List Bool) (t : ℕ) : List Bool :=
  let cfg := (c.decode α).tm.runFrom ((c.decode α).tm.initCfg x) t
  if cfg.state = none then true :: cfg.output else [false]

/-- Both clauses of the quantitative bridge yield a completed answer for every
well-formed timed request, including divergent source computations.

**Proof sketch.** Inspect the source configuration at the deadline. A halted
configuration witnesses completed computation with its full output. A live
configuration rules out every completed output, activating the timeout clause. -/
private lemma tmsat_simulator_total (c : EffectiveMachineCode) (U : FinTM Bool)
    (hU : ∀ (α x : List Bool) (t : ℕ),
      (∀ output : List Bool, (c.decode α).toFinTM.ComputesInTime x output t →
        U.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x) (true :: output)
          ((3 * α.length + 14 * c.canonizerTime α.length + 50) * (t + 1) ^ 2)) ∧
      ((∀ output : List Bool, ¬(c.decode α).toFinTM.ComputesInTime x output t) →
        U.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x) [false]
          ((3 * α.length + 14 * c.canonizerTime α.length + 50) * (t + 1) ^ 2)))
    (α x : List Bool) (t : ℕ) :
    U.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x)
      (tmsatAnswer c.toMachineCode α x t)
      ((3 * α.length + 14 * c.canonizerTime α.length + 50) * (t + 1) ^ 2) := by
  by_cases hh : ((c.decode α).tm.runFrom ((c.decode α).tm.initCfg x) t).state = none
  · have hs := (FinTM.computesInTime_iff (c.decode α).toFinTM x
      (((c.decode α).tm.runFrom ((c.decode α).tm.initCfg x) t).output) t).mpr ⟨hh, rfl⟩
    simpa only [tmsatAnswer, if_pos hh] using (hU α x t).1 _ hs
  · have hs : ∀ output : List Bool, ¬(c.decode α).toFinTM.ComputesInTime x output t := by
      intro output ho
      exact hh ((FinTM.computesInTime_iff _ _ _ _).mp ho).1
    simpa only [tmsatAnswer, if_neg hh] using (hU α x t).2 hs

/-- Acceptance compares the entire captured answer with `[true,true]`;
timeouts and successful runs with any other completed output are rejected. -/
private lemma tmsatAnswer_accept (c : MachineCode) (α x : List Bool) (t : ℕ) :
    tmsatAnswer c α x t = [true, true] ↔
      (c.decode α).toFinTM.ComputesInTime x [true] t := by
  rw [FinTM.computesInTime_iff]
  dsimp only [tmsatAnswer]
  split <;> simp_all [CodeTM.toFinTM]

/-- The polynomial canonizer hypothesis gives one polynomial budget, uniform
over every code length and unary deadline bounded by the instance length.

**Proof sketch.** Bound both the linear code-length term and the canonizer
majorant by a power of degree `max 1 e`. Absorb the constant term into the
same positive power and multiply by the deadline's quadratic bound. No
monotonicity of the canonizer time itself is assumed. -/
private lemma tmsat_simulation_budget (c : EffectiveMachineCode)
    (hc : PolyBound c.canonizerTime) :
    ∃ A d : ℕ, ∀ m r t : ℕ, r ≤ m → t ≤ m →
      (3 * r + 14 * c.canonizerTime r + 50) * (t + 1) ^ 2 ≤ A * (m + 1) ^ d := by
  obtain ⟨C, e, he⟩ := hc
  refine ⟨3 + 14 * C + 50, max 1 e + 2, ?_⟩
  intro m r t hr ht
  have hp : 1 ≤ (m + 1) ^ max 1 e := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hrp : r ≤ (m + 1) ^ max 1 e := by
    calc r ≤ m + 1 := by omega
      _ = (m + 1) ^ 1 := by simp
      _ ≤ (m + 1) ^ max 1 e := Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_max_left _ _)
  have hH : c.canonizerTime r ≤ C * (m + 1) ^ max 1 e := by
    calc c.canonizerTime r ≤ C * (r + 1) ^ e := he r
      _ ≤ C * (m + 1) ^ e :=
        Nat.mul_le_mul_left C (Nat.pow_le_pow_left (by omega) e)
      _ ≤ C * (m + 1) ^ max 1 e :=
        Nat.mul_le_mul_left C (Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_max_right _ _))
  have hcoef : 3 * r + 14 * c.canonizerTime r + 50 ≤
      (3 + 14 * C + 50) * (m + 1) ^ max 1 e := by
    simp only [Nat.add_mul, Nat.mul_assoc]
    omega
  calc
    _ ≤ ((3 + 14 * C + 50) * (m + 1) ^ max 1 e) * (m + 1) ^ 2 :=
      Nat.mul_le_mul hcoef (Nat.pow_le_pow_left (by omega) 2)
    _ = _ := by rw [Nat.mul_assoc, ← Nat.pow_add]

/-- The right-nested quadruple used by `TMSAT`, with exact unary fields. -/
private def tmsatQuad (α x : List Bool) (n t : ℕ) : List Bool :=
  pairEncode α (pairEncode x (pairEncode (List.replicate n true) (List.replicate t true)))

/-- All four tuple components fit inside the full encoded instance. -/
private lemma tmsat_quad_bounds (α x : List Bool) (n t : ℕ) :
    α.length ≤ (tmsatQuad α x n t).length ∧ x.length ≤ (tmsatQuad α x n t).length ∧
      n ≤ (tmsatQuad α x n t).length ∧ t ≤ (tmsatQuad α x n t).length := by
  simp only [tmsatQuad, universal_pair_length, List.length_replicate]
  omega

/-- The verifier specification uses an exact odd-length split, parses the
quadruple, and tests only the requested prefix of the padded certificate. -/
private def tmsatVerifier (c : MachineCode) : Language Bool :=
  {z | ∃ (y w α x : List Bool) (n t : ℕ),
    z = y ++ w ∧ w.length = y.length + 1 ∧ y = tmsatQuad α x n t ∧
      (c.decode α).toFinTM.ComputesInTime (pairEncode x (w.take n)) [true] t}

/-- Exact certificates force odd total length and recover the split position uniquely. -/
private lemma tmsat_split_length (y w : List Bool) (hw : w.length = y.length + 1) :
    (y ++ w).length % 2 = 1 ∧ ((y ++ w).length - 1) / 2 = y.length := by
  simp only [List.length_append, hw]
  omega

/-- The exact `m+1`-bit certificate convention is equivalent to the language's
original `n`-bit witness. No certificate-length majorization changes the source run.

**Proof sketch.** Pad the original witness with false bits and recover it by
taking its first `n` bits. Conversely, equality of the two concatenations and
their exact certificate lengths forces equal split positions, so the accepted
prefix has length exactly `n`. The tuple's unary field bounds `n` by `m`. -/
private lemma tmsat_certificate_equiv (c : MachineCode) (y : List Bool) :
    y ∈ TMSAT c ↔ ∃ w : List Bool, w.length = y.length + 1 ∧ y ++ w ∈ tmsatVerifier c := by
  constructor
  · rintro ⟨α, x, u, n, t, hy, hu, hs⟩
    have hn : n ≤ y.length := by
      rw [hy]
      exact (tmsat_quad_bounds α x n t).2.2.1
    let w := u ++ List.replicate (y.length + 1 - n) false
    have hw : w.length = y.length + 1 := by
      simp only [w, List.length_append, List.length_replicate, hu]
      omega
    refine ⟨w, hw, y, w, α, x, n, t, rfl, hw, hy, ?_⟩
    have htake : w.take n = u := List.take_left' hu
    rw [htake]
    exact hs
  · rintro ⟨w, hw, y', w', α, x, n, t, he, hw', hy, hs⟩
    have hlen := congrArg List.length he
    simp only [List.length_append, hw, hw'] at hlen
    obtain ⟨rfl, rfl⟩ := List.append_inj he (by omega)
    refine ⟨α, x, w.take n, n, t, hy, ?_, hs⟩
    have hn : n ≤ y.length := by
      rw [hy]
      exact (tmsat_quad_bounds α x n t).2.2.1
    rw [List.length_take, Nat.min_eq_left (by omega : n ≤ w.length)]

/-- Timed buffered composition needs the second machine to terminate only on
the first machine's image. Its bound is measured against the original input.

**Proof sketch.** Capture the preprocessing output on the composition buffer,
rewind and dispatch through the public `bufferedComp_start` theorem, then
relocate the second run through `bufferedSecondCfg_run`. Output length is at
most preprocessing time, so capture and rewind cost at most twice that time
plus two. This also permits a timed universal machine that is partial on
malformed requests, provided preprocessing always constructs a valid request. -/
private lemma tmsat_comp_on_image (M U : FinTM Bool) (f g : List Bool → List Bool)
    (T₁ T₂ : ℕ → ℕ) (hM : M.ComputesFunInTime f T₁)
    (hU : ∀ x, U.ComputesInTime (f x) (g x) (T₂ x.length)) :
    ∃ N : FinTM Bool, N.ComputesFunInTime g (fun n => 2 * T₁ n + T₂ n + 2) := by
  refine ⟨FinTM.bufferedCompTM M U, ?_⟩
  intro x
  obtain ⟨a, p, tapes, heads, ha, hstart⟩ :=
    FinTM.bufferedComp_start M U x (f x) (T₁ x.length) (hM x)
  have hlen : (f x).length ≤ T₁ x.length := by
    have ho := ((FinTM.computesInTime_iff _ _ _ _).mp (hM x)).2
    simpa only [ho] using M.tm.output_length_le x (T₁ x.length)
  obtain ⟨b, _, hr⟩ := FinTM.bufferedSecondCfg_run M U (U.tm.initCfg (f x)) true
    (by simp [FinTM.VirtualTag, MultiTapeTM.initCfg, Cfg.init]) p tapes heads (T₂ x.length)
  have hu := (FinTM.computesInTime_iff _ _ _ _).mp (hU x)
  have hbase : (FinTM.bufferedCompTM M U).ComputesInTime x (g x) (a + T₂ x.length) := by
    apply (FinTM.computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_add, hstart, hr]
    exact ⟨by simpa only [FinTM.bufferedSecondCfg, Option.map_eq_none_iff] using hu.1, hu.2⟩
  exact hbase.mono (by dsimp only; omega)

/-- **`TMSAT ∈ NP` for polynomially canonizable schemes** [AB09, Theorem 2.9,
membership]: the certificate is `u` itself, and verification is timed
universal simulation. The hypothesis `Complexity.PolyBound c.canonizerTime`
is **load-bearing and cannot be dropped** (round-1 audit, finding 1,
Argument A): `Turing.EffectiveMachineCode` constrains the canonizer's
*computability*, not its cost, and there is a lawful effective scheme — the
base scheme behind a one-bit tag, with the tagged branch decoding `[1] ++ z`
to a one-step machine that outputs the bit `A z` of a decidable language
`A ∉ EXP` — whose `TMSAT` decides `A` on the trivial instances
`⟨[1] ++ z, [], 1^0, 1^1⟩`; membership in `NP ⊆ EXP` would contradict
`A ∉ EXP`. The polynomial canonizer bound is what restores a uniform
simulation budget.

**Proof sketch.** Certificate parameters `(1, 1)`: length exactly `m + 1` on
inputs of length `m` (the declared `n` satisfies `n ≤ m`, since `1^n` sits
inside `y`; the certificate is `u` padded to `m + 1` bits, `u` recovered as the
first `n` bits — no marker needed, `n` is read off `y`). The verifier language:
`V = {y ++ w : |w| = |y| + 1`, `y` parses as a quadruple
`⟨α, x, 1^n, 1^t⟩`, and the machine `α` denotes accepts `⟨x, w.take n⟩` within
`t` steps`}`. `V ∈ P` by a machine with the named fill obligations: (i)
unique-split recovery — a well-formed input has length `m + (m + 1) = 2m + 1`,
**odd**, so the machine **rejects even lengths** and splits an odd length `N`
at `(N − 1) / 2` (round-1 audit, finding 4, correcting the drafted parity);
(ii) the **quadruple parser** — three nested `pairDecode` passes (the aligned
two-bit grammar; the `UniversalStartup` parsing layer is the in-repo
precedent) plus all-`true` shape checks on the third and fourth components,
rejecting any failure; (iii) **unary-to-binary clock conversion**:
`Turing.timed_universal`'s clock input is `Nat.bits t`, so the verifier
converts the unary `1^t` by counter increments (`Nat.bits 0 = []` at the
`t = 0` edge, where every instance is negative —
`Turing.FinTM.not_computesInTime_zero`); (iv) **assembly and relocated
simulation**: build `pairEncode (pairEncode (Nat.bits t) α) (pairEncode x
(w.take n))` on a work tape and run the timed universal machine `U` of
`Turing.timed_universal c` relocated-and-captured (the standing obligations);
`U` answers `true :: output` or `[false]` by design and its branches are
exhaustive, so acceptance is exactly the complete captured answer
`[true, true]` — a timeout, or any completed output other than `[true]`,
rejects; (v) the verdict with buffered output. **Budget** — where the
hypothesis enters: `U` completes within `C_α·(t+1)^2` steps, and the round-1
audit's inspection of the `Universal` module's bound definitions gives, with
`r = |α|` and `H = c.canonizerTime r`, the chain `C_α ≤ 3r + 14·H + 50` (the
decoded serialization's length `L` bounds the header/state parameters and is
itself at most `H`, the canonizer writing it within its time budget —
`Turing.MultiTapeTM.output_length_le`); `PolyBound c.canonizerTime` then
bounds `C_α` by a polynomial in `r ≤ m` uniformly, and with `t ≤ m` the whole
simulation is polynomial in `m`: `V ∈ P` via `Complexity.mem_P_of_dtime_le`.
**Named fill obligation (new public bridge)**: the public
`Turing.timed_universal` exposes its constant only existentially per code, so
the fill needs a quantitative public form of the bound (an addition to the
audited `Universal` surface, to be requested through the standing shared-file
mechanism and flagged for its audit round — the round-1 finding's repair
guidance; a prose obligation alone cannot discharge the budget). Membership
equivalence: forward, a `TMSAT` witness `u` pads to `m + 1` bits (absorbing
halting keeps the accepting run); backward, a certificate's first `n` bits are
a witness — `Turing.timed_universal`'s two branches convert between `U`'s
answers and `(c.decode α).toFinTM.ComputesInTime (pairEncode x u) [true] t`
exactly, and `Turing.pairEncode_injective` pins the parsed components to the
defining existential's. -/
theorem TMSAT_mem_NP (c : EffectiveMachineCode) (hc : PolyBound c.canonizerTime) :
    TMSAT c.toMachineCode ∈ NP := by
  obtain ⟨U, hU⟩ := timed_universal_quantitative c
  obtain ⟨A, d, hbudget⟩ := tmsat_simulation_budget c hc
  have htotal := tmsat_simulator_total c U hU
  have hV : tmsatVerifier c.toMachineCode ∈ P := by
    -- CONTINUATION D-MEM: construct the odd-split/quadruple parser and unary
    -- clock converter, returning a well-formed zero-deadline request on failure.
    -- Compose its output with `htotal` through `tmsat_comp_on_image`, use
    -- `hbudget` and `tmsat_quad_bounds`, and compare the entire captured answer
    -- with `[true,true]` using `tmsatAnswer_accept`. No totality of U on malformed
    -- strings may be assumed. This is a partial-delivery admission, not a
    -- discharge of the verifier-machine obligation.
    sorry
  refine ⟨1, 1, tmsatVerifier c.toMachineCode, hV, ?_⟩
  intro y
  simpa only [Nat.pow_one, Nat.one_mul] using tmsat_certificate_equiv c.toMachineCode y

/-- The audited deadline formula majorizes the normalized wrapper runtime.
The certificate length remains exactly `C*(n+1)^c` throughout this inequality.

**Proof sketch.** The paired input plus one cell is bounded by
`(C+3)(n+1)^max(1,c)`. Raise to the wrapper degree, absorb its additive one
into the positive power, and square for the one-work-tape normalization.
Only the deadline is enlarged. -/
private lemma tmsat_deadline_bound (K B e C c n : ℕ) :
    K * (B * (2 * n + 2 + C * (n + 1) ^ c + 1) ^ e + 1) ^ 2 ≤
      ((K + 1) * (B + 1) ^ 2 * (C + 3) ^ (2 * e)) *
        (n + 1) ^ (2 * e * max 1 c) := by
  have hlin : n + 1 ≤ (n + 1) ^ max 1 c := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right (Nat.succ_pos n) (Nat.le_max_left 1 c)
  have hpow : (n + 1) ^ c ≤ (n + 1) ^ max 1 c :=
    Nat.pow_le_pow_right (Nat.succ_pos n) (Nat.le_max_right 1 c)
  have hsize : 2 * n + 2 + C * (n + 1) ^ c + 1 ≤
      (C + 3) * (n + 1) ^ max 1 c := by
    have hm := Nat.mul_le_mul_left C hpow
    rw [Nat.add_mul]
    omega
  have hepow : (2 * n + 2 + C * (n + 1) ^ c + 1) ^ e ≤
      (C + 3) ^ e * (n + 1) ^ (e * max 1 c) := by
    calc
      _ ≤ ((C + 3) * (n + 1) ^ max 1 c) ^ e := Nat.pow_le_pow_left hsize e
      _ = _ := by rw [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_comm (max 1 c) e]
  have hpos : 1 ≤ (C + 3) ^ e * (n + 1) ^ (e * max 1 c) :=
    Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (Nat.succ_pos _))
  have hinner : B * (2 * n + 2 + C * (n + 1) ^ c + 1) ^ e + 1 ≤
      (B + 1) * (C + 3) ^ e * (n + 1) ^ (e * max 1 c) := by
    calc
      _ ≤ B * ((C + 3) ^ e * (n + 1) ^ (e * max 1 c)) +
          (C + 3) ^ e * (n + 1) ^ (e * max 1 c) :=
        Nat.add_le_add (Nat.mul_le_mul_left B hepow) hpos
      _ = _ := by ring
  calc
    _ ≤ (K + 1) * ((B + 1) * (C + 3) ^ e * (n + 1) ^ (e * max 1 c)) ^ 2 :=
      Nat.mul_le_mul (Nat.le_succ K) (Nat.pow_le_pow_left hinner 2)
    _ = _ := by
      simp only [Nat.mul_pow, ← Nat.pow_mul]
      simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- Constant strings are polynomial-time computable by finite emission chains. -/
private lemma tmsat_constant_poly (w : List Bool) : PolyTimeComputable (fun _ => w) := by
  obtain ⟨M, C, hM⟩ := FinTM.computesFunInTime_const w
  exact ⟨M, C, 1, by simpa only [Nat.pow_one] using hM⟩

/-- The exact binary certificate length is polynomial-time computable,
including zero coefficients and degree zero.

**Proof sketch.** Follow the audited three-way split: coefficient zero emits
the empty word; positive coefficient and degree zero emits its fixed binary
representation from finite control; positive coefficient and positive degree
uses `timeConstructible_poly C (c-1)`. Only the runtime is enlarged. -/
private lemma tmsat_exact_certificate_bits (C c : ℕ) :
    PolyTimeComputable (fun x : List Bool => (C * (x.length + 1) ^ c).bits) := by
  by_cases hC : C = 0
  · simpa [hC] using tmsat_constant_poly []
  · by_cases hc : c = 0
    · simpa [hc] using tmsat_constant_poly C.bits
    · obtain ⟨_, a, _, M, hM⟩ := timeConstructible_poly C (c - 1) (by omega)
      have he : c - 1 + 1 = c := by omega
      simp only [he] at hM
      refine ⟨M, a * (C + 1), c, fun x => (hM x).mono ?_⟩
      have hp : 1 ≤ (x.length + 1) ^ c := Nat.one_le_pow _ _ (Nat.succ_pos _)
      calc
        _ ≤ a * ((C + 1) * (x.length + 1) ^ c) :=
          Nat.mul_le_mul_left a (by rw [Nat.add_mul, Nat.one_mul]; omega)
        _ = _ := by ring

/-- The wrapper's total output function rejects malformed pairs and otherwise
forwards the verifier's verdict on the concatenated components. -/
private noncomputable def tmsatWrapperOutput (V : Language Bool) (z : List Bool) : List Bool :=
  match pairDecode z with
  | none => [false]
  | some (x, u) => [MultiTapeTM.indicator (V : Set (List Bool)) (x ++ u)]

/-- Three applications of pairing injectivity pin every quadruple component;
unary equality pins the two natural-number fields by taking lengths. -/
private lemma tmsat_quad_injective (α x : List Bool) (n t : ℕ)
    (β y : List Bool) (m s : ℕ) (he : tmsatQuad α x n t = tmsatQuad β y m s) :
    α = β ∧ x = y ∧ n = m ∧ t = s := by
  have h₁ : (α, pairEncode x (pairEncode (List.replicate n true) (List.replicate t true))) =
      (β, pairEncode y (pairEncode (List.replicate m true) (List.replicate s true))) :=
    pairEncode_injective he
  obtain ⟨hα, hrest⟩ := Prod.mk.inj h₁
  have h₂ : (x, pairEncode (List.replicate n true) (List.replicate t true)) =
      (y, pairEncode (List.replicate m true) (List.replicate s true)) :=
    pairEncode_injective hrest
  obtain ⟨hx, hlast⟩ := Prod.mk.inj h₂
  have h₃ : (List.replicate n true, List.replicate t true) =
      (List.replicate m true, List.replicate s true) := pairEncode_injective hlast
  obtain ⟨hn, ht⟩ := Prod.mk.inj h₃
  refine ⟨hα, hx, ?_, ?_⟩
  · simpa only [List.length_replicate] using congrArg List.length hn
  · simpa only [List.length_replicate] using congrArg List.length ht

/-- Given a fixed coded wrapper with the prescribed deadline, the reduction
has exactly the original NP language as its preimage.

**Proof sketch.** Forward, use the original exact-length certificate and the
wrapper's accepting verdict. Backward, nested pairing injectivity forces the
code, input, certificate length, and deadline to be precisely the emitted ones.
Completed-output uniqueness then identifies acceptance with the verifier's
verdict, even if the chosen deadline exceeds the actual halting time. -/
private lemma tmsat_reduction_correct (c : MachineCode) (L V : Language Bool)
    (C e : ℕ) (α : List Bool) (T : ℕ → ℕ)
    (hL : ∀ x : List Bool, x ∈ L ↔
      ∃ u : List Bool, u.length = C * (x.length + 1) ^ e ∧ x ++ u ∈ V)
    (hM : ∀ x u : List Bool, u.length = C * (x.length + 1) ^ e →
      (c.decode α).toFinTM.ComputesInTime (pairEncode x u)
        [MultiTapeTM.indicator (V : Set (List Bool)) (x ++ u)] (T x.length)) :
    ∀ x : List Bool, x ∈ L ↔ tmsatQuad α x (C * (x.length + 1) ^ e) (T x.length) ∈ TMSAT c := by
  classical
  intro x
  constructor
  · intro hx
    obtain ⟨u, hu, hv⟩ := (hL x).mp hx
    refine ⟨α, x, u, C * (x.length + 1) ^ e, T x.length, rfl, hu, ?_⟩
    simpa only [MultiTapeTM.indicator, if_pos hv] using hM x u hu
  · rintro ⟨β, y, u, n, t, he, hu, hs⟩
    obtain ⟨rfl, rfl, hn, ht⟩ := tmsat_quad_injective α x
      (C * (x.length + 1) ^ e) (T x.length) β y n t he
    rw [← hn] at hu
    rw [← ht] at hs
    refine (hL _).mpr ⟨u, hu, ?_⟩
    have ho := hs.output_unique (hM _ u hu)
    by_contra hv
    simp [MultiTapeTM.indicator, hv] at ho

/-- **`TMSAT` is `NP`-hard** [AB09, Theorem 2.9, hardness]: the generic
reduction — for `L ∈ NP`, send `x` to `⟨⌞M⌟, x, 1^{p(|x|)}, 1^{q(m)}⟩`.

**Proof sketch.** Let `L ∈ NP` with parameters `(C₀, c₀, V)` and certificate
length `Q n = C₀·(n+1)^(c₀)`, and, via `Complexity.mem_P_iff`, a machine `M_V`
deciding `V` within `A·(m+1)^d`. **The encoded machine**: a wrapper `M'` that,
on input `z`, parses `z` as `Turing.pairEncode x u` (the pairing parser
obligation; on non-pairs, output `[false]` — `M'` is total), assembles
`x ++ u`, and runs `M_V` relocated-and-captured, forwarding the verdict. `M'`
computes a total function within an explicit polynomial; normalize by the
audited chain `Turing.FinTM.one_work_tape_binary` (its total-function
hypothesis holds) and `Turing.exists_codeTM`, and let `α₀ := c.encode M''` be
the resulting **fixed code string** (this is why plain `Turing.MachineCode`
suffices — the audited `Complexity.HALT_NPHard` recipe). Let
`T' n` the **explicit** deadline formula below. **The reduction map**
`f x := pairEncode α₀ (pairEncode x (pairEncode 1^{Q |x|} 1^{T' |x|}))`.
`Complexity.PolyTimeComputable f` by the named obligations: emit the doubled
fixed string `α₀` from finite control (emission chains), double-and-copy `x`,
and write the two unary runs by binary countdown, under the **exact-value
discipline** of the round-1 audit (finding 3): the certificate length `Q` must
be emitted **exactly** — majorizing it changes the language (at
`C₀ = c₀ = 0` and `L = V = {[true]}`, replacing `Q = 0` by `n + 1` flips the
empty input's membership) — by cases: `C₀ = 0` emits the empty run;
`C₀ > 0, c₀ = 0` emits the fixed constant `C₀` from finite control;
`C₀ > 0, c₀ > 0` computes the exact binary value by
`Complexity.timeConstructible_poly C₀ (c₀ - 1)`. The **deadline may be
majorized** (enlarging `t` only relaxes the budget of a total machine whose
verdict is fixed): with a wrapper bound `B·(s+1)^e` (`B, e ≥ 1`) on inputs of
length `s`, normalization multiplier `K`, and `s = 2n + 2 + Q n` on the
relevant inputs, take the audit's formula — `r := max 1 c₀`,
`D := (K+1)·(B+1)^2·(C₀+3)^(2e)`, `T' n := D·(n+1)^(2er)`; then
`s + 1 ≤ (C₀+3)·(n+1)^r` gives `K·(B·(s+1)^e + 1)^2 ≤ T' n` at every `n`, and
`Complexity.timeConstructible_poly D (2er - 1)` computes `T'`'s exact binary
value (`2er ≥ 1`). Output length: `|f x| = 2|α₀| + 2|x| + 2·Q |x| + T' |x| +
6`, an explicit polynomial. **Correctness**: `f x ∈ TMSAT c` iff — by
`Turing.pairEncode_injective`, which pins the quadruple's components — some
`u` with `|u| = Q n` has `M''.toFinTM.ComputesInTime (pairEncode x u) [true]
(T' n)`; by `M''`'s semantics and budget this holds iff `x ++ u ∈ V` (the
wrapper's verdict is the `V`-indicator, completed outputs are unique —
`Turing.FinTM.ComputesInTime.output_unique`), and the `NP` membership
equivalence for `L` turns "some such `u`" into `x ∈ L`. Conclude
`Complexity.NPHard` by the definition, one reduction per `L ∈ NP`. -/
theorem TMSAT_NPHard (c : MachineCode) : NPHard (TMSAT c) := by
  classical
  intro L hL
  obtain ⟨C₀, c₀, V, hV, hL⟩ := hL
  obtain ⟨A, d, M_V, hM_V⟩ := mem_P_iff.mp hV
  have hwrap : ∃ (W : FinTM Bool) (B e : ℕ), 0 < B ∧ 0 < e ∧
      W.ComputesFunInTime (tmsatWrapperOutput V) (fun s => B * (s + 1) ^ e) := by
    -- CONTINUATION D-WRAP: implement the total aligned pairing parser;
    -- reject non-pairs, assemble x ++ u on a buffer, and relocate/capture M_V.
    -- `tmsat_comp_on_image` supplies the timed simulation composition.
    -- The remaining obligation is a concrete polynomial-time pair-to-concat
    -- preprocessing machine and its malformed-input branch.
    sorry
  obtain ⟨W, B, e, hB, he, hW⟩ := hwrap
  obtain ⟨M₁, K, hk, h₁⟩ := FinTM.one_work_tape_binary W (tmsatWrapperOutput V)
    (fun s => B * (s + 1) ^ e) hW
  obtain ⟨M'', hcode⟩ := exists_codeTM M₁ hk
  let α₀ := c.encode M''
  let r := max 1 c₀
  let D := (K + 1) * (B + 1) ^ 2 * (C₀ + 3) ^ (2 * e)
  let T' := fun n => D * (n + 1) ^ (2 * e * r)
  have hD : 0 < D :=
    Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) (Nat.pow_pos (Nat.succ_pos _)))
      (Nat.pow_pos (by omega))
  have hexp : 1 ≤ 2 * e * r := by
    have hr : 0 < r := Nat.le_max_left 1 c₀
    have her := Nat.mul_pos he hr
    rw [Nat.mul_assoc]
    omega
  have hdeadline : TimeConstructible T' := by
    have h := timeConstructible_poly D (2 * e * r - 1) hD
    have heq : 2 * e * r - 1 + 1 = 2 * e * r := by omega
    simpa only [heq] using h
  have hcertificate := tmsat_exact_certificate_bits C₀ c₀
  have hnormalized (x u : List Bool) (hu : u.length = C₀ * (x.length + 1) ^ c₀) :
      (c.decode α₀).toFinTM.ComputesInTime (pairEncode x u)
        [MultiTapeTM.indicator (V : Set (List Bool)) (x ++ u)] (T' x.length) := by
    have hrun := (hcode (pairEncode x u) (tmsatWrapperOutput V (pairEncode x u)) _).2
      (h₁ (pairEncode x u))
    simp only [tmsatWrapperOutput, pairDecode_pairEncode] at hrun
    rw [show c.decode α₀ = M'' from c.decode_encode M'']
    apply hrun.mono
    simpa only [universal_pair_length, hu] using tmsat_deadline_bound K B e C₀ c₀ x.length
  have hemit : PolyTimeComputable
      (fun x => tmsatQuad α₀ x (C₀ * (x.length + 1) ^ c₀) (T' x.length)) := by
    -- CONTINUATION D-EMIT: emit the fixed code and doubled input, then the
    -- exact unary certificate and deadline via binary countdown. The exact
    -- binary certificate is supplied by `hcertificate` (all three edge cases)
    -- and the exact binary deadline by `hdeadline`. Compose these submachines
    -- while retaining x, and prove the stated right-nested pairing layout.
    sorry
  exact ⟨_, hemit, tmsat_reduction_correct c L V C₀ c₀ α₀ T' hL hnormalized⟩

/-- **Theorem 2.9** [AB09]: `TMSAT` is `NP`-complete — over an effective
scheme with a polynomially bounded canonizer, the hypothesis its membership
half requires and cannot drop (round-1 audit, findings 1-2: without it, the
Argument-A scheme's `TMSAT` is `NP`-hard yet outside `NP`, so the completeness
conjunction fails).

**Proof sketch.** `Complexity.TMSAT_mem_NP` (with the same hypothesis `hc`)
and `Complexity.TMSAT_NPHard` at `c.toMachineCode`, assembled by the
definition of `Complexity.NPComplete`. -/
theorem TMSAT_NPComplete (c : EffectiveMachineCode) (hc : PolyBound c.canonizerTime) :
    NPComplete (TMSAT c.toMachineCode) := by
  exact ⟨TMSAT_mem_NP c hc, TMSAT_NPHard c.toMachineCode⟩

end Complexity


## ===== TCSlib/Complexity/ClassNP/EXP.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassNP.NP

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# EXP and NEXP

[AB09, Claim 2.4 and §2.6.2]: the exponential-time classes. `EXP` is
`⋃ c, DTIME (2^(n^c))` verbatim from Claim 2.4. `NEXP` is defined here in the
certificate form of [AB09, Exercise 2.27] — exponential-length certificates with
a polynomial-time verifier language — mirroring `Complexity.NP`; its equivalence
with the `NTIME` form of §2.6.2 is a phase-2 obligation, once nondeterministic
machines exist.

## Design and deviations from [AB09]

* `NEXP`'s verifier is a language `V ∈ P`: "polynomial time" is measured in the
  length of the padded string `x ++ u`, which is exponential in `|x|` — this is
  the standard certificate rendering and exactly Exercise 2.27's intent.
* **The certificate length is the explicit formula `C · 2^((|x|+1)^c)`** — the
  same phase-1 audit repair as `Complexity.NP` (finding 1, Argument A: an
  abstract `ExpBound` length function admits undecidable classes). `ExpBound`
  survives as a numerical helper only.
* The chain `P ⊆ NP ⊆ EXP ⊆ NEXP` [AB09, Claim 2.4 and §2.6.2] is stated as the
  three individual inclusions below (`P ⊆ NP` lives in `ClassNP/NP.lean`).

## Main definitions

* `Complexity.EXP` — [AB09, Claim 2.4].
* `Complexity.ExpBound`, `Complexity.NEXP` — [AB09, §2.6.2, in the form of
  Exercise 2.27].

## Main results

* `Complexity.P_subset_EXP` — [AB09, Claim 2.4].
* `Complexity.NP_subset_EXP` — certificate enumeration [AB09, Claim 2.4].
* `Complexity.EXP_subset_NEXP` — [AB09, §2.6.2].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Claim 2.4, p. 41; §2.6.2, pp. 56-57;
  Exercise 2.27.)
-/

namespace Complexity

/-- **The class EXP** [AB09, Claim 2.4]: languages decidable in time `2^(n^c)`
for some constant `c` (up to `DTIME`'s constant-factor slack). -/
def EXP : Set (Language Bool) :=
  ⋃ c : ℕ, DTIME fun n => 2 ^ n ^ c

/-- The bound `p : ℕ → ℕ` is *exponentially bounded*: `p n ≤ C · 2^((n+1)^c)` for
some constants — the certificate-length regime of `NEXP`. -/
def ExpBound (p : ℕ → ℕ) : Prop :=
  ∃ C c : ℕ, ∀ n, p n ≤ C * 2 ^ (n + 1) ^ c

/-- **The class NEXP**, in the certificate form of [AB09, Exercise 2.27]:
certificates of length exactly `C · 2^((|x|+1)^c)` — an explicit formula, per
the phase-1 audit repair — with a verifier language decidable in time
polynomial in the padded string `x ++ u`. The `NTIME` form of [AB09, §2.6.2] and
its equivalence with this one are phase-2 obligations. -/
def NEXP : Set (Language Bool) :=
  {L | ∃ (C c : ℕ) (V : Language Bool), V ∈ P ∧
    ∀ x : List Bool, x ∈ L ↔
      ∃ u : List Bool, u.length = C * 2 ^ (x.length + 1) ^ c ∧ x ++ u ∈ V}

/-- **`P ⊆ EXP`** [AB09, Claim 2.4].

**Proof sketch.** `n^c + 1 ≤ 2 · 2^(n^c)` for every `n` (as `n^c < 2^(n^c)`), so
each `DTIME (n^c + 1)` sits inside `DTIME (2 · 2^(n^c)) ⊆ EXP` by
`Complexity.DTIME.mono` and the constant-absorbing `Complexity.DTIME`
definition. -/
theorem P_subset_EXP : P ⊆ EXP := by
  intro L hL
  obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hL
  have hbound : ∀ n : ℕ, n ^ c + 1 ≤ 2 * 2 ^ n ^ c := by
    intro n
    have hn := Nat.lt_two_pow_self (n := n ^ c)
    omega
  obtain ⟨a, M, hM⟩ := DTIME.mono hbound hc
  refine Set.mem_iUnion.mpr ⟨c, a * 2, M, fun x => ?_⟩
  simpa only [Nat.mul_assoc] using hM x

open Turing Turing.FinTM

/-! ### Private certificate enumeration infrastructure -/

/-- Little-endian value, including leading zeroes at the high end. -/
private def enumValue : List Bool → ℕ
  | [] => 0
  | b :: bs => 2 * enumValue bs + if b then 1 else 0

/-- Increment without extending the width; `none` means exhaustion.
The empty word overflows, so its caller must test it before incrementing. -/
private def enumInc : List Bool → Option (List Bool)
  | [] => none
  | false :: bs => some (true :: bs)
  | true :: bs => (enumInc bs).map (false :: ·)

/-- A width-`w` little-endian representation of the low `w` bits of `i`. -/
private def enumWord : ℕ → ℕ → List Bool
  | 0, _ => []
  | w + 1, i => decide (i % 2 = 1) :: enumWord w (i / 2)

/-- Every width-`w` word has value strictly below `2^w`. -/
private lemma enumValue_lt (u : List Bool) : enumValue u < 2 ^ u.length := by
  induction u with
  | nil => simp [enumValue]
  | cons b u ih =>
    cases b <;> simp only [enumValue, Bool.false_eq_true, ↓reduceIte,
      List.length_cons, Nat.pow_succ] <;> omega

/-- The representation retains exactly the requested width, even at zero. -/
private lemma enumWord_length (w i : ℕ) : (enumWord w i).length = w := by
  induction w generalizing i with
  | zero => rfl
  | succ w ih => simp only [enumWord, List.length_cons, ih]

/-- The initial rank is represented by precisely the all-false word. -/
private lemma enumWord_zero (w : ℕ) : enumWord w 0 = List.replicate w false := by
  induction w with
  | zero => rfl
  | succ w ih => simp [enumWord, ih, List.replicate_succ]

/-- In range, the representation has the specified value.
**Proof sketch.** Remove the low bit by division by two. The quotient is
in range for the remaining width, and the remainder is either zero or one. -/
private lemma enumWord_value (w i : ℕ) (hi : i < 2 ^ w) :
    enumValue (enumWord w i) = i := by
  induction w generalizing i with
  | zero => simp only [Nat.pow_zero] at hi; simp [enumWord, enumValue, show i = 0 by omega]
  | succ w ih =>
    have hdiv : i / 2 < 2 ^ w := by rw [Nat.pow_succ] at hi; omega
    simp only [enumWord, enumValue, ih (i / 2) hdiv]
    have hmod := Nat.mod_lt i (by omega : 0 < 2)
    split <;> simp_all <;> omega

/-- Equal-length words with the same value are equal, including trailing
false bits. The parity determines the first bit; divide the remainder by two. -/
private lemma enumValue_injective (u v : List Bool) (hlen : u.length = v.length)
    (hval : enumValue u = enumValue v) : u = v := by
  induction u generalizing v with
  | nil => simpa using hlen.symm
  | cons b u ih =>
    cases v with
    | nil => simp at hlen
    | cons b' v =>
      have hlen' : u.length = v.length := by simpa using hlen
      cases b <;> cases b' <;> simp only [enumValue, Bool.false_eq_true, ↓reduceIte] at hval
      all_goals first | omega | exact congrArg (_ :: ·) (ih v hlen' (by omega))

/-- Every word is the unique representative of its rank at its own width. -/
private lemma enumWord_complete (u : List Bool) :
    enumWord u.length (enumValue u) = u := by
  exact enumValue_injective _ _ (enumWord_length _ _)
    (enumWord_value _ _ (enumValue_lt u))

/-- One fixed-width increment either preserves width and adds one to the
value, or reports overflow exactly at the last rank.
**Proof sketch.** A low false bit changes to true. A low true bit is cleared
and passes the carry to the suffix; suffix overflow is total overflow. -/
private lemma enumInc_spec (u : List Bool) :
    match enumInc u with
    | some v => v.length = u.length ∧ enumValue v = enumValue u + 1
    | none => enumValue u + 1 = 2 ^ u.length := by
  induction u with
  | nil => simp [enumInc, enumValue]
  | cons b u ih =>
    cases b with
    | false => simp [enumInc, enumValue]
    | true =>
      cases he : enumInc u with
      | none =>
        simp only [he] at ih
        simp only [enumInc, he, Option.map_none, enumValue, ↓reduceIte,
          List.length_cons, Nat.pow_succ]
        omega
      | some v =>
        simp only [he] at ih
        simp only [enumInc, he, Option.map_some, enumValue, Bool.false_eq_true,
          ↓reduceIte, List.length_cons]
        exact ⟨by omega, by omega⟩

/-- On canonical candidates, increment advances exactly one rank and reports
overflow only after the last rank. This includes width zero. -/
private lemma enumInc_word (w i : ℕ) (hi : i < 2 ^ w) :
    enumInc (enumWord w i) =
      if i + 1 < 2 ^ w then some (enumWord w (i + 1)) else none := by
  have hs := enumInc_spec (enumWord w i)
  rw [enumWord_length, enumWord_value w i hi] at hs
  cases he : enumInc (enumWord w i) with
  | none => simp only [he] at hs; simp [show ¬i + 1 < 2 ^ w by omega]
  | some v =>
    simp only [he] at hs
    have hv := enumValue_lt v
    rw [hs.1, hs.2] at hv
    rw [if_pos hv]
    congr 1
    exact enumValue_injective v _ (hs.1.trans (enumWord_length _ _).symm)
      (hs.2.trans (enumWord_value w (i + 1) hv).symm)

/-- No candidate repeats among the `2^w` in-range ranks. -/
private lemma enumWord_no_repeat (w i j : ℕ) (hi : i < 2 ^ w) (hj : j < 2 ^ w)
    (h : enumWord w i = enumWord w j) : i = j := by
  have := congrArg enumValue h
  simpa only [enumWord_value w i hi, enumWord_value w j hj] using this

/-- Exact-width existential certificates are exactly the in-range candidates. -/
private lemma enumCandidates_iff (w : ℕ) (p : List Bool → Prop) :
    (∃ u, u.length = w ∧ p u) ↔ ∃ i, i < 2 ^ w ∧ p (enumWord w i) := by
  constructor
  · rintro ⟨u, rfl, hu⟩
    exact ⟨enumValue u, enumValue_lt u, by simpa only [enumWord_complete] using hu⟩
  · rintro ⟨i, hi, hp⟩
    exact ⟨enumWord w i, enumWord_length w i, hp⟩

/-- Resulting tape contents and success flag of a fixed-width carry. Overflow
clears the entire word and returns false; it never writes an extra bit. -/
private def enumBump : List Bool → List Bool × Bool
  | [] => ([], false)
  | false :: bs => (true :: bs, true)
  | true :: bs => (false :: (enumBump bs).1, (enumBump bs).2)

/-- The number of leading true bits crossed by the carry. -/
private def enumCarryPos : List Bool → ℕ
  | true :: bs => enumCarryPos bs + 1
  | _ => 0

/-- The carry visits at most the candidate width before detecting overflow. -/
private lemma enumCarryPos_le (u : List Bool) : enumCarryPos u ≤ u.length := by
  induction u with
  | nil => rfl
  | cons b u ih => cases b <;> simp only [enumCarryPos, List.length_cons] <;> omega

/-- The physical carry's tape contents always retain the original width. -/
private lemma enumBump_length (u : List Bool) : (enumBump u).1.length = u.length := by
  induction u with
  | nil => rfl
  | cons b u ih => cases b <;> simp [enumBump, ih]

/-- The carry's success flag and tape contents implement `enumInc` exactly. -/
private lemma enumBump_inc (u : List Bool) :
    enumInc u = if (enumBump u).2 then some (enumBump u).1 else none := by
  induction u with
  | nil => rfl
  | cons b u ih =>
    cases b with
    | false => rfl
    | true => simp only [enumInc, enumBump, ih]; split <;> rfl

/-- Read the first bit of a suffix, with the empty suffix represented by blank. -/
private lemma enumBuffer_read (pre bs : List Bool) :
    bufferTape (pre ++ bs) pre.length = bs.head? := by
  simp only [bufferTape_nat, List.getElem?_append_right (le_refl _), Nat.sub_self]
  cases bs <;> rfl

/-- Writing at the start of a nonempty suffix preserves the prefix and width.
**Proof sketch.** At the write position use the new bit. Before and after
that position both tapes read the same unchanged entries. -/
private lemma enumBuffer_write (pre bs : List Bool) (old new : Bool) :
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

/-- One-tape fixed-width increment, followed by a rewind. The live states are
carry (`inl none`), rewind with success flag (`inl (some b)`), and return
(`inr b`). No transition emits physical output. Return states wait for a
surrounding controller. This privately re-derives the counter template. -/
private def enumCarryTM : FinTM Bool where
  k := 1
  State := Option Bool ⊕ Bool
  tm :=
    { q₀ := .inl none
      tr := fun q _ work => match q with
        | .inl none => match work 0 with
          | some true => ⟨0, fun _ => (some (some false), .pos), none, some (.inl none)⟩
          | some false => ⟨0, fun _ => (some (some true), .neg), none, some (.inl (some true))⟩
          | none => ⟨0, fun _ => (none, .neg), none, some (.inl (some false))⟩
        | .inl (some b) => match work 0 with
          | some _ => ⟨0, fun _ => (none, .neg), none, some (.inl (some b))⟩
          | none => ⟨0, fun _ => (none, .pos), none, some (.inr b)⟩
        | .inr b => controlAction 0 (some (.inr b)) }

/-- A candidate on the carry tape, with arbitrary native input-head position. -/
private def enumCarryCfg (x : List Bool) (p : Fin (x.length + 2))
    (q : Option Bool ⊕ Bool) (z : ℤ) (u : List Bool) :
    Cfg enumCarryTM.k Bool enumCarryTM.State x :=
  ⟨some q, p, fun _ => bufferTape u, fun _ => z, []⟩

/-- One carry transition writes only inside the fixed-width word, or detects
the right blank without writing to it. -/
private lemma enumCarry_step (x : List Bool) (p : Fin (x.length + 2))
    (pre bs : List Bool) :
    enumCarryTM.tm.step (enumCarryCfg x p (.inl none) pre.length (pre ++ bs)) =
      match bs with
      | [] => enumCarryCfg x p (.inl (some false)) (pre.length - 1) pre
      | false :: us => enumCarryCfg x p (.inl (some true)) (pre.length - 1) (pre ++ true :: us)
      | true :: us => enumCarryCfg x p (.inl none) (pre.length + 1) (pre ++ false :: us) := by
  unfold MultiTapeTM.step
  change (enumCarryTM.tm.tr (.inl none) _ _).apply _ = _
  simp only [enumCarryTM, enumCarryCfg, Cfg.workTapeSymbols, enumBuffer_read]
  cases bs with
  | nil =>
    refine Cfg.ext rfl (moveInputPos_zero p) ?_ ?_ rfl
    · simp
    · funext i; simp [Action.apply, sub_eq_add_neg]
  | cons b bs =>
    cases b <;> refine Cfg.ext rfl (moveInputPos_zero p) ?_ ?_ rfl
    all_goals first
      | (funext i; exact enumBuffer_write pre bs _ _)
      | (funext i; simp [Action.apply, sub_eq_add_neg])

/-- The carry phase takes one step beyond the leading true prefix, including
one blank test on overflow.
**Proof sketch.** Induct on the remaining candidate. Each true bit is cleared
and added to the processed prefix. A false bit or the right blank starts
rewind without changing the width. -/
private lemma enumCarry_run (x : List Bool) (p : Fin (x.length + 2))
    (u : List Bool) : ∀ pre : List Bool,
    enumCarryTM.tm.runFrom (enumCarryCfg x p (.inl none) pre.length (pre ++ u))
        (enumCarryPos u + 1) =
      enumCarryCfg x p (.inl (some (enumBump u).2))
        ((pre.length : ℤ) + enumCarryPos u - 1) (pre ++ (enumBump u).1) := by
  induction u with
  | nil =>
    intro pre
    simpa [enumCarryPos, enumBump, MultiTapeTM.runFrom_succ_eq_step] using
      enumCarry_step x p pre []
  | cons b u ih =>
    intro pre
    cases b with
    | false =>
      simpa [enumCarryPos, enumBump, MultiTapeTM.runFrom_succ_eq_step] using
        enumCarry_step x p pre (false :: u)
    | true =>
      simp only [enumCarryPos]
      rw [MultiTapeTM.runFrom_succ_eq_step, enumCarry_step]
      simpa [enumBump, List.append_assoc, Nat.cast_add, Nat.cast_one,
        add_assoc, add_comm, add_left_comm] using ih (pre ++ [false])

/-- Rewind over `j` known candidate cells to the left blank, then return at
cell zero in exactly `j+1` steps, retaining the candidate and success flag. -/
private lemma enumCarry_rewind (x : List Bool) (p : Fin (x.length + 2))
    (u : List Bool) (b : Bool) : ∀ j, j ≤ u.length →
    enumCarryTM.tm.runFrom (enumCarryCfg x p (.inl (some b)) ((j : ℤ) - 1) u)
        (j + 1) = enumCarryCfg x p (.inr b) 0 u := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    simp only [Nat.cast_zero, zero_sub]
    unfold MultiTapeTM.step
    simp only [enumCarryTM, enumCarryCfg, Cfg.workTapeSymbols, bufferTape_left]
    refine Cfg.ext rfl (moveInputPos_zero p) rfl ?_ rfl
    funext i; simp [Action.apply]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hstep : enumCarryTM.tm.step
        (enumCarryCfg x p (.inl (some b)) ((j + 1 : ℕ) - 1) u) =
          enumCarryCfg x p (.inl (some b)) ((j : ℤ) - 1) u := by
      have hz : ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) := by omega
      rw [hz]
      unfold MultiTapeTM.step
      simp only [enumCarryTM, enumCarryCfg, Cfg.workTapeSymbols, bufferTape_nat,
        List.getElem?_eq_getElem (by omega : j < u.length)]
      refine Cfg.ext rfl (moveInputPos_zero p) rfl ?_ rfl
      funext i; simp [Action.apply, sub_eq_add_neg]
    rw [hstep]
    exact ih (by omega)

/-- A complete fixed-width increment and rewind costs `2j+2 ≤ 2|u|+2`,
where `j` is the leading true-prefix length. It returns live at cell zero,
retains the input head, and emits nothing. Width zero returns overflow only
when this subroutine is called, so enumeration can process `[]` first. -/
private lemma enumCarry_correct (x : List Bool) (p : Fin (x.length + 2))
    (u : List Bool) :
    2 * enumCarryPos u + 2 ≤ 2 * u.length + 2 ∧
      enumCarryTM.tm.runFrom (enumCarryCfg x p (.inl none) 0 u)
          (2 * enumCarryPos u + 2) =
        enumCarryCfg x p (.inr (enumBump u).2) 0 (enumBump u).1 := by
  refine ⟨by have := enumCarryPos_le u; omega, ?_⟩
  have hr := enumCarry_run x p u []
  simp only [List.length_nil, Nat.cast_zero, List.nil_append, zero_add] at hr
  rw [show 2 * enumCarryPos u + 2 = (enumCarryPos u + 1) + (enumCarryPos u + 1) by omega,
    MultiTapeTM.runFrom_add, hr]
  exact enumCarry_rewind x p (enumBump u).1 (enumBump u).2 _
    (by rw [enumBump_length]; exact enumCarryPos_le u)

section EnumCapture

variable {S : Type} [Fintype S] [DecidableEq S]
variable (M : FinTM Bool) (r : ℕ) (next : Option Bool → S)
variable (control : S → Option Bool → (Fin (M.k + (1 + r)) → Option Bool) →
  Action (M.k + (1 + r)) Bool (((Option M.State × Option Bool) × Bool) ⊕ S))

/-- Run a verifier on a work-tape input buffer, capture its first output bit
in finite control, and return live to a controller with access to all tapes.
The tape blocks are verifier work, input buffer, and `r` retained tapes.
The boundary tag supplies the verifier's native clamping behavior. The real
input head and retained tapes do not move during a call. -/
private def enumCaptureTM : FinTM Bool where
  k := M.k + (1 + r)
  State := ((Option M.State × Option Bool) × Bool) ⊕ S
  tm :=
    { q₀ := .inl ((some M.tm.q₀, none), true)
      tr := fun q inp work => match q with
        | .inl ((some q, reg), tag) =>
          let v := work (Fin.natAdd M.k (Fin.castAdd r (0 : Fin 1)))
          let a := M.tm.tr q v (fun i => work (Fin.castAdd (1 + r) i))
          let m := virtualMove tag v a.inputTape
          ⟨0, tapeBlocks a.workTapes (none, m) (fun _ => (none, 0)), none,
            some (.inl ((a.state, reg.or a.output), virtualNextTag tag m))⟩
        | .inl ((none, reg), _) => controlAction 0 (some (.inr (next reg)))
        | .inr q => control q inp work }

/-- A complete call invariant: exact source work tapes, an unchanged virtual
input buffer, arbitrary retained tapes, source output captured in finite
control, and empty physical output. The native input `x` can differ from
the verifier input `y`. -/
private def enumCaptureCfg {x y : List Bool} (cfg : Cfg M.k Bool M.State y)
    (tag : Bool) (p : Fin (x.length + 2))
    (tapes : Fin r → ℤ → Option Bool) (heads : Fin r → ℤ) :
    Cfg (enumCaptureTM M r next control).k Bool
      (enumCaptureTM M r next control).State x where
  state := some (.inl ((cfg.state, cfg.output.head?), tag))
  inputPos := p
  workTapes := tapeBlocks cfg.workTapes (bufferTape y) tapes
  workTapePos := tapeBlocks cfg.workTapePos ((cfg.inputPos.val : ℤ) - 1) heads
  output := []

/-- One live source transition is simulated in one physical step, updating
the captured bit before recording a possible halt.
**Proof sketch.** Buffer reads equal native source reads. The virtual movement
lemma proves both clamping and preservation of the boundary tag. The verifier
work block changes in lockstep; the other tape contents are unchanged. The
head-of-append identity gives the captured bit, even on the halting action. -/
private lemma enumCapture_step {x y : List Bool} (cfg : Cfg M.k Bool M.State y)
    (tag : Bool) (htag : VirtualTag cfg.inputPos tag) (p : Fin (x.length + 2))
    (tapes : Fin r → ℤ → Option Bool) (heads : Fin r → ℤ)
    (hs : cfg.state ≠ none) :
    ∃ tag', VirtualTag (M.tm.step cfg).inputPos tag' ∧
      (enumCaptureTM M r next control).tm.step
          (enumCaptureCfg M r next control cfg tag p tapes heads) =
        enumCaptureCfg M r next control (M.tm.step cfg) tag' p tapes heads := by
  cases hq : cfg.state with
  | none => exact False.elim (hs hq)
  | some q =>
    let a := M.tm.tr q cfg.inputSymbol cfg.workTapeSymbols
    let m := virtualMove tag cfg.inputSymbol a.inputTape
    have hm := virtualMove_correct cfg tag htag a.inputTape
    have hc : M.tm.step cfg = a.apply cfg := by simp only [MultiTapeTM.step, hq, a]
    refine ⟨virtualNextTag tag m, ?_, ?_⟩
    · simpa only [hc, Action.apply] using hm.2
    · have hs' : (enumCaptureCfg M r next control cfg tag p tapes heads).state =
          some (.inl ((some q, cfg.output.head?), tag)) := by simp [enumCaptureCfg, hq]
      have hv : (enumCaptureCfg M r next control cfg tag p tapes heads).workTapeSymbols
          (Fin.natAdd M.k (Fin.castAdd r (0 : Fin 1))) = cfg.inputSymbol := by
        simp [enumCaptureCfg, Cfg.workTapeSymbols, bufferTape_inputSymbol]
      have hr : (fun i => (enumCaptureCfg M r next control cfg tag p tapes heads).workTapeSymbols
          (Fin.castAdd (1 + r) i)) = cfg.workTapeSymbols := by
        funext i
        simp [enumCaptureCfg, Cfg.workTapeSymbols]
      unfold MultiTapeTM.step
      rw [hs']
      dsimp only [enumCaptureTM]
      rw [hv, hr, hq]
      change (⟨0, tapeBlocks a.workTapes (none, m) (fun _ => (none, 0)), none,
        some (.inl ((a.state, cfg.output.head?.or a.output), virtualNextTag tag m))⟩ :
        Action (M.k + (1 + r)) Bool _).apply _ =
          enumCaptureCfg M r next control (a.apply cfg) _ p tapes heads
      refine Cfg.ext ?_ (moveInputPos_zero p) ?_ ?_ ?_
      · simp [enumCaptureCfg, Action.apply, List.head?_append, Option.head?_toList]
      · funext i
        refine Fin.addCases ?_ ?_ i
        · intro j; simp [enumCaptureCfg, tapeBlocks, Action.apply]
        · intro j
          refine Fin.addCases ?_ ?_ j <;> intro j <;>
            simp [enumCaptureCfg, tapeBlocks, Action.apply]
      · funext i
        refine Fin.addCases ?_ ?_ i
        · intro j; simp [enumCaptureCfg, tapeBlocks, Action.apply]
        · intro j
          refine Fin.addCases ?_ ?_ j
          · intro j
            simpa only [enumCaptureCfg, Action.apply, tapeBlocks_buffer] using hm.1
          · intro j; simp [enumCaptureCfg, tapeBlocks, Action.apply]
      · simp [enumCaptureCfg, Action.apply]

/-- Lockstep through the first source halt, with an exact virtual-input
simulation, no physical emissions, and all retained tapes intact. -/
private lemma enumCapture_run {x y : List Bool} (cfg : Cfg M.k Bool M.State y)
    (tag : Bool) (htag : VirtualTag cfg.inputPos tag) (p : Fin (x.length + 2))
    (tapes : Fin r → ℤ → Option Bool) (heads : Fin r → ℤ) (t : ℕ)
    (h : ∀ s, s < t → (M.tm.runFrom cfg s).state ≠ none) :
    ∃ tag', VirtualTag (M.tm.runFrom cfg t).inputPos tag' ∧
      (enumCaptureTM M r next control).tm.runFrom
          (enumCaptureCfg M r next control cfg tag p tapes heads) t =
        enumCaptureCfg M r next control (M.tm.runFrom cfg t) tag' p tapes heads := by
  induction t with
  | zero => exact ⟨tag, htag, rfl⟩
  | succ t ih =>
    obtain ⟨tag', htag', he⟩ := ih (fun s hs => h s (by omega))
    obtain ⟨tag'', htag'', he'⟩ :=
      enumCapture_step M r next control _ tag' htag' p tapes heads (h t (by omega))
    refine ⟨tag'', ?_, ?_⟩
    · simpa only [MultiTapeTM.runFrom_succ_eq_step'] using htag''
    · rw [MultiTapeTM.runFrom_succ_eq_step', he, he', MultiTapeTM.runFrom_succ_eq_step']

/-- The administrative return step dispatches on the updated register and
preserves every tape, head, and the empty physical output. -/
private lemma enumCapture_transfer {x y : List Bool} (cfg : Cfg M.k Bool M.State y)
    (tag : Bool) (p : Fin (x.length + 2))
    (tapes : Fin r → ℤ → Option Bool) (heads : Fin r → ℤ) (h : cfg.state = none) :
    (enumCaptureTM M r next control).tm.step
        (enumCaptureCfg M r next control cfg tag p tapes heads) =
      { enumCaptureCfg M r next control cfg tag p tapes heads with
        state := some (.inr (next cfg.output.head?)) } := by
  unfold MultiTapeTM.step
  simp only [enumCaptureCfg, h]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ ?_
  · rfl
  · funext i; exact add_zero _
  · rfl

/-- Given a prepared buffer and fresh source tapes, a singleton-output call
returns its bit to the live controller within the source budget plus one.
This holds for any native input and parked head, including empty verifier
input. The complete returned configuration certifies retention and silence.
**Proof sketch.** Take the first source halting time. Start its virtual head
at cell zero with the right-boundary-compatible tag `true`. Apply lockstep
through the halt, then transfer. Absorbing source halting identifies its full
configuration with the one at the supplied budget. -/
private lemma enumCapture_returns (x y : List Bool) (b : Bool) (T : ℕ)
    (p : Fin (x.length + 2)) (tapes : Fin r → ℤ → Option Bool) (heads : Fin r → ℤ)
    (hM : M.ComputesInTime y [b] T) :
    ∃ t, t ≤ T + 1 ∧ ∃ tag,
      VirtualTag (M.tm.runFrom (M.tm.initCfg y) T).inputPos tag ∧
      (enumCaptureTM M r next control).tm.runFrom
          (enumCaptureCfg M r next control (M.tm.initCfg y) true p tapes heads) t =
        { enumCaptureCfg M r next control (M.tm.runFrom (M.tm.initCfg y) T)
            tag p tapes heads with state := some (.inr (next (some b))) } := by
  classical
  obtain ⟨hh, hout⟩ := (computesInTime_iff M y [b] T).mp hM
  have hex : ∃ t, (M.tm.runFrom (M.tm.initCfg y) t).state = none := ⟨T, hh⟩
  let t := Nat.find hex
  have ht : t ≤ T := Nat.find_min' hex hh
  have hs : (M.tm.runFrom (M.tm.initCfg y) t).state = none := Nat.find_spec hex
  have he : M.tm.runFrom (M.tm.initCfg y) T = M.tm.runFrom (M.tm.initCfg y) t := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le ht
    rw [hd, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hs]
  obtain ⟨tag, htag, hr⟩ := enumCapture_run M r next control (M.tm.initCfg y) true
    (by simp [VirtualTag, MultiTapeTM.initCfg, Cfg.init]) p tapes heads t
    (fun s hs => Nat.find_min hex hs)
  refine ⟨t + 1, by omega, tag, by rwa [he], ?_⟩
  rw [MultiTapeTM.runFrom_succ_eq_step', hr,
    enumCapture_transfer M r next control _ tag p tapes heads hs, ← he, hout]
  rfl

end EnumCapture

/-- Boolean result of testing `count` consecutive candidate ranks, starting
with `i`. The recursive branch represents one rejected call. -/
private def enumAny (accept : ℕ → Bool) (i : ℕ) : ℕ → Bool
  | 0 => false
  | count + 1 => if accept i then true else enumAny accept (i + 1) count

/-- The abstract loop accepts exactly when an in-range candidate accepts.
**Proof sketch.** Separate the first rank from the remaining interval. -/
private lemma enumAny_iff (accept : ℕ → Bool) (i count : ℕ) :
    enumAny accept i count = true ↔
      ∃ j, i ≤ j ∧ j < i + count ∧ accept j = true := by
  induction count generalizing i with
  | zero =>
    simp only [enumAny, Bool.false_eq_true, false_iff]
    rintro ⟨j, hj, hj', _⟩
    omega
  | succ count ih =>
    change (if accept i then true else enumAny accept (i + 1) count) = true ↔ _
    by_cases h : accept i = true
    · simp only [if_pos h, true_iff]
      exact ⟨i, le_refl _, by omega, h⟩
    · rw [if_neg h, ih]
      constructor
      · rintro ⟨j, hj, hj', ha⟩
        exact ⟨j, by omega, by omega, ha⟩
      · rintro ⟨j, hj, hj', ha⟩
        have hne : j ≠ i := by intro he; subst j; exact h ha
        exact ⟨j, by omega, by omega, ha⟩

/-- For the actual verifier's indicator, testing all ranks gives exactly the
definition's existential over certificates of width `w`. This is independent
of the machine implementation, and includes width zero. -/
private lemma enumAny_certificates (x : List Bool) (w : ℕ) (V : Language Bool) :
    enumAny (fun i => MultiTapeTM.indicator V (x ++ enumWord w i)) 0 (2 ^ w) = true ↔
      ∃ u, u.length = w ∧ x ++ u ∈ V := by
  classical
  rw [enumAny_iff, enumCandidates_iff]
  simp [MultiTapeTM.indicator]

/-- A timed loop invariant combines bounded accept-or-advance segments into
one bounded singleton-output computation. The terminal configuration is the
post-overflow rejection configuration, so every candidate, including the last,
is tested before exhaustion.
**Proof sketch.** Induct on the remaining number of candidates. Acceptance
terminates immediately. Rejection advances to the next canonical configuration;
compose run segments and add their bounds. This lemma does not assert that
any particular machine satisfies the required per-round contracts. -/
private lemma enumLoop_run (M : FinTM Bool) (x : List Bool)
    (cfg : ℕ → Cfg M.k Bool M.State x) (accept : ℕ → Bool) (B i count : ℕ)
    (hend : (cfg (i + count)).state = none ∧ (cfg (i + count)).output = [false])
    (hround : ∀ j, i ≤ j → j < i + count → ∃ t, t ≤ B ∧
      if accept j then
        (M.tm.runFrom (cfg j) t).state = none ∧ (M.tm.runFrom (cfg j) t).output = [true]
      else M.tm.runFrom (cfg j) t = cfg (j + 1)) :
    ∃ t, t ≤ count * B ∧ (M.tm.runFrom (cfg i) t).state = none ∧
      (M.tm.runFrom (cfg i) t).output = [enumAny accept i count] := by
  induction count generalizing i with
  | zero =>
    refine ⟨0, by simp, ?_⟩
    simpa [enumAny] using hend
  | succ count ih =>
    obtain ⟨t, ht, hc⟩ := hround i (le_refl _) (by omega)
    by_cases hb : accept i = true
    · simp only [hb, ↓reduceIte] at hc
      refine ⟨t, ht.trans ?_, hc.1, ?_⟩
      · rw [Nat.succ_mul]; omega
      · simpa [enumAny, hb] using hc.2
    · simp only [hb] at hc
      have hend' : (cfg (i + 1 + count)).state = none ∧
          (cfg (i + 1 + count)).output = [false] := by
        simpa only [show i + 1 + count = i + (count + 1) by omega] using hend
      obtain ⟨s, hs, hhalt, hout⟩ := ih (i + 1) hend'
        (fun j hj hj' => hround j (by omega) (by omega))
      refine ⟨t + s, ?_, ?_, ?_⟩
      · rw [Nat.succ_mul]; omega
      · rw [MultiTapeTM.runFrom_add, hc]; exact hhalt
      · rw [MultiTapeTM.runFrom_add, hc]
        simpa [enumAny, hb] using hout

/-- A fixed polynomial in `n+1` in the exponent is absorbed into `n^e`,
with a uniform multiplicative constant for lengths zero and one.
**Proof sketch.** For `n ≥ 2`, use `K ≤ 2^K ≤ n^K` and `n+1 ≤ n^2`.
For `n ≤ 1`, bound the exponent by `K·2^k` and absorb its exponential. -/
private lemma enumExponent_bound (K k : ℕ) :
    ∃ A e : ℕ, ∀ n : ℕ, 2 ^ (K * (n + 1) ^ k) ≤ A * 2 ^ n ^ e := by
  refine ⟨2 ^ (K * 2 ^ k), K + 2 * k, fun n => ?_⟩
  by_cases hn : 2 ≤ n
  · have hK : K ≤ n ^ K :=
      (Nat.le_of_lt (Nat.lt_two_pow_self (n := K))).trans (Nat.pow_le_pow_left hn K)
    have hn' : n + 1 ≤ n ^ 2 := by
      calc n + 1 ≤ 2 * n := by omega
           _ ≤ n * n := Nat.mul_le_mul_right n hn
           _ = n ^ 2 := by ring
    have hexp : K * (n + 1) ^ k ≤ n ^ (K + 2 * k) := by
      calc K * (n + 1) ^ k ≤ n ^ K * (n ^ 2) ^ k :=
             Nat.mul_le_mul hK (Nat.pow_le_pow_left hn' k)
           _ = n ^ (K + 2 * k) := by rw [← Nat.pow_mul, ← Nat.pow_add]
    exact (Nat.pow_le_pow_right (by omega) hexp).trans
      (Nat.le_mul_of_pos_left _ (Nat.pow_pos (by omega)))
  · have hs : (n + 1) ^ k ≤ 2 ^ k := Nat.pow_le_pow_left (by omega) k
    calc 2 ^ (K * (n + 1) ^ k) ≤ 2 ^ (K * 2 ^ k) :=
           Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left K hs)
         _ ≤ 2 ^ (K * 2 ^ k) * 2 ^ n ^ (K + 2 * k) :=
           Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))

/-- The audited round budget is pointwise bounded by an `EXP` budget, for
all coefficients and degrees, including zero.
**Proof sketch.** Set `k=max 1 c`. Both `n+1` and the width are bounded by
constant multiples of `(n+1)^k`. Replace the polynomial round overhead by
`2^(d·(n+width+1))`, add the exponents, and use `enumExponent_bound`. -/
private lemma enumBudget_bound (a C c d : ℕ) :
    ∃ A e : ℕ, ∀ n : ℕ,
      a * 2 ^ (C * (n + 1) ^ c) * (n + C * (n + 1) ^ c + 1) ^ d ≤
        A * 2 ^ n ^ e := by
  let k := max 1 c
  let K := C + d * (C + 1)
  obtain ⟨A, e, hA⟩ := enumExponent_bound K k
  refine ⟨a * A, e, fun n => ?_⟩
  have hc : (n + 1) ^ c ≤ (n + 1) ^ k :=
    Nat.pow_le_pow_right (by omega) (Nat.le_max_right 1 c)
  have hn : n + 1 ≤ (n + 1) ^ k := by
    simpa only [Nat.pow_one] using
      Nat.pow_le_pow_right (by omega : 0 < n + 1) (Nat.le_max_left 1 c)
  have hw : n + C * (n + 1) ^ c + 1 ≤ (C + 1) * (n + 1) ^ k := by
    calc n + C * (n + 1) ^ c + 1 = (n + 1) + C * (n + 1) ^ c := by omega
         _ ≤ (n + 1) ^ k + C * (n + 1) ^ k :=
           Nat.add_le_add hn (Nat.mul_le_mul_left C hc)
         _ = (C + 1) * (n + 1) ^ k := by ring
  have he : C * (n + 1) ^ c + d * (n + C * (n + 1) ^ c + 1) ≤
      K * (n + 1) ^ k := by
    calc C * (n + 1) ^ c + d * (n + C * (n + 1) ^ c + 1) ≤
        C * (n + 1) ^ k + d * ((C + 1) * (n + 1) ^ k) :=
          Nat.add_le_add (Nat.mul_le_mul_left C hc) (Nat.mul_le_mul_left d hw)
         _ = K * (n + 1) ^ k := by dsimp [K]; ring
  have hb : (n + C * (n + 1) ^ c + 1) ^ d ≤
      2 ^ (d * (n + C * (n + 1) ^ c + 1)) := by
    calc (n + C * (n + 1) ^ c + 1) ^ d ≤
        (2 ^ (n + C * (n + 1) ^ c + 1)) ^ d :=
          Nat.pow_le_pow_left (Nat.le_of_lt (Nat.lt_two_pow_self)) d
         _ = 2 ^ (d * (n + C * (n + 1) ^ c + 1)) := by
          rw [← Nat.pow_mul, Nat.mul_comm]
  calc a * 2 ^ (C * (n + 1) ^ c) * (n + C * (n + 1) ^ c + 1) ^ d ≤
      a * (2 ^ (C * (n + 1) ^ c) * 2 ^ (d * (n + C * (n + 1) ^ c + 1))) := by
        rw [← Nat.mul_assoc]
        exact Nat.mul_le_mul_left _ hb
       _ = a * 2 ^ (C * (n + 1) ^ c + d * (n + C * (n + 1) ^ c + 1)) := by
        rw [Nat.pow_add]
       _ ≤ a * 2 ^ (K * (n + 1) ^ k) :=
        Nat.mul_le_mul_left a (Nat.pow_le_pow_right (by omega) he)
       _ ≤ a * A * 2 ^ n ^ e := by
        simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left a (hA n)

/-- **Continuation frontier; admitted in this partial delivery.** There is one
uniform finite machine with a polynomial startup and a polynomially bounded
accept-or-advance segment for each exact-width candidate. The configuration
after the last rejected candidate is a halted singleton rejection.

**Proof sketch / remaining construction.** Evaluate `C(n+1)^c` and construct
the all-false candidate while retaining the instance; assemble `x ++ u` on
the virtual input buffer. Use `enumCapture_returns` for the captured call.
On rejection, clear the bounded visited work region, reset all source and
buffer heads and the captured bit, and use `enumCarry_correct` to increment.
Its `enumBump_inc`/`enumInc_word` specification supplies the next rank or the
overflow signal. Emit the single final answer only on acceptance or overflow.
Prove the startup and per-round configuration equalities below with a uniform
polynomial budget. These machine assembly and reset obligations are NOT
discharged by the counter, capture, and abstract loop lemmas alone. -/
private theorem enumMachine_contracts (C c a d : ℕ) (V : Language Bool)
    (MV : FinTM Bool) (hV : MV.DecidesInTime V (fun n => a * (n + 1) ^ d)) :
    ∃ (b e : ℕ) (E : FinTM Bool), ∀ x : List Bool,
      ∃ (cfg : ℕ → Cfg E.k Bool E.State x) (startup : ℕ),
        startup ≤ b * (x.length + C * (x.length + 1) ^ c + 1) ^ e ∧
        E.tm.runFrom (E.tm.initCfg x) startup = cfg 0 ∧
        (cfg (2 ^ (C * (x.length + 1) ^ c))).state = none ∧
        (cfg (2 ^ (C * (x.length + 1) ^ c))).output = [false] ∧
        ∀ i, i < 2 ^ (C * (x.length + 1) ^ c) → ∃ t,
          t ≤ b * (x.length + C * (x.length + 1) ^ c + 1) ^ e ∧
          if MultiTapeTM.indicator V (x ++ enumWord (C * (x.length + 1) ^ c) i) then
            (E.tm.runFrom (cfg i) t).state = none ∧
              (E.tm.runFrom (cfg i) t).output = [true]
          else E.tm.runFrom (cfg i) t = cfg (i + 1) := by
  sorry

/-- Assuming the single machine-construction frontier, the proved loop
invariant gives a decider with the audited exponential-times-polynomial
budget. This lemma inherits exactly that pending admission.
**Proof sketch.** Start the loop after initialization, apply `enumLoop_run`
for all `2^width` candidates, and identify its Boolean answer using exact
candidate coverage. Since `2^width ≥ 1`, startup is absorbed by doubling the
coefficient. The final computation has exactly one output bit. -/
private theorem enumDecider (C c a d : ℕ) (V : Language Bool)
    (MV : FinTM Bool) (hV : MV.DecidesInTime V (fun n => a * (n + 1) ^ d)) :
    ∃ (b e : ℕ) (E : FinTM Bool),
      E.DecidesInTime {x | ∃ u, u.length = C * (x.length + 1) ^ c ∧ x ++ u ∈ V}
        (fun n => b * 2 ^ (C * (n + 1) ^ c) * (n + C * (n + 1) ^ c + 1) ^ e) := by
  classical
  obtain ⟨b, e, E, hE⟩ := enumMachine_contracts C c a d V MV hV
  refine ⟨2 * b, e, E, fun x => ?_⟩
  obtain ⟨cfg, startup, hstartup, hinit, hend, hout, hround⟩ := hE x
  let w := C * (x.length + 1) ^ c
  let B := b * (x.length + w + 1) ^ e
  let accept := fun i => MultiTapeTM.indicator V (x ++ enumWord w i)
  obtain ⟨t, ht, hh, ho⟩ := enumLoop_run E x cfg accept B 0 (2 ^ w)
    (by simpa only [Nat.zero_add] using And.intro hend hout)
    (fun j _ hj => hround j (by simpa only [Nat.zero_add] using hj))
  have hb : enumAny accept 0 (2 ^ w) =
      MultiTapeTM.indicator
        {z | ∃ u, u.length = C * (z.length + 1) ^ c ∧ z ++ u ∈ V} x := by
    have ha := enumAny_certificates x w V
    change enumAny accept 0 (2 ^ w) = true ↔ _ at ha
    cases he : enumAny accept 0 (2 ^ w) with
    | false =>
      have hx : ¬∃ u, u.length = w ∧ x ++ u ∈ V := by
        intro hx
        have := ha.mpr hx
        rw [he] at this
        contradiction
      simp [MultiTapeTM.indicator, w] at hx ⊢
      exact hx
    | true =>
      have hx := ha.mp he
      simp [MultiTapeTM.indicator, w] at hx ⊢
      exact hx
  have hcomp : E.ComputesInTime x [enumAny accept 0 (2 ^ w)] (startup + t) := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_add, hinit]
    exact ⟨hh, ho⟩
  rw [hb] at hcomp
  apply hcomp.mono
  have hB : B ≤ 2 ^ w * B := Nat.le_mul_of_pos_left _ (Nat.pow_pos (by omega))
  calc startup + t ≤ B + 2 ^ w * B := Nat.add_le_add hstartup ht
       _ ≤ 2 ^ w * B + 2 ^ w * B := Nat.add_le_add_right hB _
       _ = 2 * b * 2 ^ (C * (x.length + 1) ^ c) *
           (x.length + C * (x.length + 1) ^ c + 1) ^ e := by dsimp [B, w]; ring

/-- **`NP ⊆ EXP`** [AB09, Claim 2.4]: brute-force certificate enumeration.

**Proof sketch.** Let `L ∈ NP` with certificate length exactly `Q n = C(n+1)^c`
and verifier `V ∈ P` decided by machine `MV`. The deciding machine, on input
`x` of length `n`: evaluate the explicit formula `Q n` (a polynomial-evaluation
machine — a **new obligation**; the explicit formula is what makes the width
computable at all, phase-1 audit finding 1 and question 4) and lay out a
width-`Q n` all-`false` candidate certificate; in each round, assemble
`x ++ u` on a buffer, run `MV`, accept if it accepts, else increment the
candidate as a **fixed-width** counter and repeat, rejecting on width overflow
after the `2^(Q n)`-th round. Enumeration is over certificates of exactly the
definition's length — no majorant mismatch (audit question 4). The remaining
machine obligations, named for the fill per phase-1 finding 5 and round-2
finding 2: fixed-width increment with overflow detection (the private
`counterInc` layer of `ClassP/TimeConstructible.lean` extends on overflow and
is a template, not a citable API — promotion or private re-derivation is a
fill-time decision); retention of `x` and the candidate across rounds;
**a verifier-call simulation that captures `MV`'s decision bit in finite
control, suppresses its physical emissions, and redirects its halt to the
loop controller** — the output tape is append-only, so forwarding per-round
emissions would accumulate (`[false, true]` across two rounds) and violate
`DecidesInTime`'s singleton contract; the real output stays empty until the
final answer (the capture-wrapper pattern of `Turing.universalCaptureTM` is
the in-repo precedent); reset of `MV`'s simulated state, heads, work region,
and the captured bit between rounds (a bounded region — each head moves at
most one cell per step); and a timed loop invariant covering all of the above
(the untimed `exists_cond` does not supply one; at `C = 0` the single round on
the empty certificate still executes). Budget: at most `2^(Q n)` rounds of cost polynomial in
`n + Q n + 1`, i.e. `a · 2^(Q n) (n + Q n + 1)^d ≤ 2^(n^e)` for a fixed degree
`e`, small lengths absorbed into `DTIME`'s constant (the audit's own estimate):
`L ∈ EXP`.
+
+**Partial-fill appendix.** The fixed-width carry, buffered captured-call
+simulation, abstract timed-loop invariant, and final budget normalization
+are proved below the class definitions. The machine's initialization,
+reset, and controller assembly remain the single private admission
+`enumMachine_contracts`; the present theorem still depends on `sorryAx`. -/
theorem NP_subset_EXP : NP ⊆ EXP := by
  rintro L ⟨C, c, V, hV, hL⟩
  obtain ⟨a, d, MV, hMV⟩ := mem_P_iff.mp hV
  obtain ⟨b, e, E, hE⟩ := enumDecider C c a d V MV hMV
  obtain ⟨A, f, hbound⟩ := enumBudget_bound b C c e
  have heq : {x | ∃ u, u.length = C * (x.length + 1) ^ c ∧ x ++ u ∈ V} = L :=
    Set.ext (fun x => (hL x).symm)
  rw [heq] at hE
  exact Set.mem_iUnion.mpr ⟨f, A, E, fun x => (hE x).mono (hbound x.length)⟩

/-- **`EXP ⊆ NEXP`** [AB09, §2.6.2].

**Proof sketch.** Given `L ∈ EXP` decided in time `2^(n^c)`, take `C = 1` and
certificate length `p n = 2^((n+1)^c)` — nondecreasing in `n` (constant `2` at
`c = 0`), so that `n ↦ n + p n` is **strictly increasing** (the monotonicity
belongs to the sum, not to `p` — phase-1 audit, finding 8) — and the verifier
`V = {x ++ u : x ∈ L, |u| = p |x|}`. `V ∈ P`: on a string `y` of length `m`,
recover the unique `n` with `n + p n = m` by scanning `n ≤ m` (each evaluation
writes `2^((n+1)^c)` in binary, `(n+1)^c + 1 ≤ (m+1)^c + 1` bits — polynomial
in `m`, the audit's own check), reject if no split exists (including `m = 0`),
split off `x`, and run `L`'s decider: its `a · 2^(n^c)` budget is at most
`a · m`. Fixed-degree arithmetic and the split/copy machinery are named new
machine obligations for the fill. Certificates carry no information; padding
buys the verifier its time. -/
theorem EXP_subset_NEXP : EXP ⊆ NEXP := by
  sorry

end Complexity


## ===== TCSlib/Complexity/ClassNP/Reductions.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassNP.EXP
import TCSlib.Complexity.Uncomputability.Halting

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Karp reductions, NP-hardness, and NP-completeness

[AB09, §2.2, Definition 2.7]: `L ≤ₚ L'` when a polynomial-time computable
function maps members to members and non-members to non-members; `L'` is
`NP`-hard when every `NP` language reduces to it, `NP`-complete when it is also
in `NP`. Theorem 2.8 packages the basic laws: transitivity, and the collapse
consequences of an `NP`-hard language landing in `P`.

The module closes with [AB09, Exercise 2.8], the chapter's bridge back to
Chapter 1: `HALT` is `NP`-hard but — being undecidable — not in `NP`, hence not
`NP`-complete.

## Main definitions

* `Complexity.PolyTimeReducible` (scoped notation `≤ₚ`) — [AB09, Definition 2.7].
* `Complexity.NPHard`, `Complexity.NPComplete` — [AB09, Definition 2.7].

## Main results

* `Complexity.PolyTimeReducible.refl`, `Complexity.PolyTimeReducible.trans` —
  [AB09, Theorem 2.8.1 and Exercise 2.9].
* `Complexity.mem_P_of_polyTimeReducible` — downward closure of `P` under `≤ₚ`
  [AB09, Figure 2.1].
* `Complexity.P_eq_NP_of_NPHard_mem_P` — [AB09, Theorem 2.8.2].
* `Complexity.NPComplete.mem_P_iff` — [AB09, Theorem 2.8.3].
* `Complexity.HALT_NPHard`, `Complexity.HALT_not_mem_NP` — [AB09, Exercise 2.8].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.2, Definition 2.7, Theorem 2.8,
  pp. 42-44; Exercises 2.8-2.9.)
-/

namespace Complexity

open Turing

/-- **Polynomial-time Karp reducibility** [AB09, Definition 2.7]: `L ≤ₚ L'` when
some polynomial-time computable `f` satisfies `x ∈ L ↔ f x ∈ L'` for every
string `x`. -/
def PolyTimeReducible (L L' : Language Bool) : Prop :=
  ∃ f : List Bool → List Bool, PolyTimeComputable f ∧ ∀ x, x ∈ L ↔ f x ∈ L'

@[inherit_doc] scoped infix:50 " ≤ₚ " => PolyTimeReducible

/-- Karp reducibility is reflexive [AB09, Exercise 2.9]: the identity reduces
`L` to itself.

**Proof sketch.** `Complexity.polyTimeComputable_id` with the trivial membership
equivalence. -/
theorem PolyTimeReducible.refl (L : Language Bool) : L ≤ₚ L := by
  exact ⟨id, polyTimeComputable_id, fun _ => Iff.rfl⟩

/-- **Karp reducibility is transitive** [AB09, Theorem 2.8.1].

**Proof sketch.** Compose the two reduction functions with
`Complexity.PolyTimeComputable.comp` and chain the membership equivalences —
the polynomial-composition observation of [AB09]'s proof lives inside `comp`. -/
theorem PolyTimeReducible.trans {L L' L'' : Language Bool}
    (h : L ≤ₚ L') (h' : L' ≤ₚ L'') : L ≤ₚ L'' := by
  obtain ⟨f, hf, hL⟩ := h
  obtain ⟨g, hg, hL'⟩ := h'
  exact ⟨g ∘ f, hg.comp hf, fun x => (hL x).trans (hL' (f x))⟩

/-- **`P` is closed downward under `≤ₚ`** [AB09, Figure 2.1 and the remark after
Definition 2.7]: if `L ≤ₚ L'` and `L' ∈ P` then `L ∈ P`.

**Proof sketch.** Compose the reduction machine with a polynomial-time decider of
`L'` (`Complexity.mem_P_iff`, read pointwise as computing the total
singleton-indicator function) via the **timed** total composition
`Turing.FinTM.computesFunInTime_comp` — the untimed `exists_comp_partial`
carries no time bound (phase-1 audit, finding 4). The intermediate string `f x`
has polynomially bounded length
(`Complexity.PolyTimeComputable.output_length_le`), so the decider's budget on
it is polynomial in `|x|` by monotonicity of the explicit polynomial, and the
composite decides `L` since `x ∈ L ↔ f x ∈ L'`; return through
`Complexity.mem_P_of_dtime_le`.

The implementation packages the decider as a polynomial-time computable
singleton-indicator function and applies `PolyTimeComputable.comp`, whose
proof invokes the timed interface above with its intermediate-output bound.
Finally `succ_pow_le` converts the resulting `(n+1)^d` budget to the
`n^d+1` form consumed by `mem_P_of_dtime_le`. -/
theorem mem_P_of_polyTimeReducible {L L' : Language Bool}
    (h : L ≤ₚ L') (h' : L' ∈ P) : L ∈ P := by
  classical
  obtain ⟨f, hf, hL⟩ := h
  obtain ⟨C, c, M, hM⟩ := mem_P_iff.mp h'
  have hg : PolyTimeComputable (fun y => [MultiTapeTM.indicator (L' : Set (List Bool)) y]) :=
    ⟨M, C, c, hM⟩
  obtain ⟨S, A, d, hS⟩ := hg.comp hf
  have hdec : S.DecidesInTime L (fun n => A * (n + 1) ^ d) := by
    intro x
    have hi : MultiTapeTM.indicator (L : Set (List Bool)) x =
        MultiTapeTM.indicator (L' : Set (List Bool)) (f x) := by
      simp only [MultiTapeTM.indicator, hL x]
    simpa only [Function.comp_apply, hi] using hS x
  refine mem_P_of_dtime_le (T := fun n => A * (n + 1) ^ d)
    ⟨1, S, ?_⟩ (A * 2 ^ d) d ?_
  · intro x
    simpa only [Nat.one_mul] using hdec x
  · intro n
    calc
      A * (n + 1) ^ d ≤ A * (2 ^ d * (n ^ d + 1)) :=
        Nat.mul_le_mul_left A (succ_pow_le n d)
      _ = A * 2 ^ d * (n ^ d + 1) := (Nat.mul_assoc _ _ _).symm

/-- **`NP`-hardness** [AB09, Definition 2.7]: every `NP` language Karp-reduces to
`L`. -/
def NPHard (L : Language Bool) : Prop :=
  ∀ L' ∈ NP, L' ≤ₚ L

/-- **`NP`-completeness** [AB09, Definition 2.7]: `L` is in `NP` and `NP`-hard. -/
def NPComplete (L : Language Bool) : Prop :=
  L ∈ NP ∧ NPHard L

/-- **If an `NP`-hard language is in `P`, then `P = NP`** [AB09, Theorem 2.8.2].

**Proof sketch.** `P ⊆ NP` is `Complexity.P_subset_NP`; conversely every
`L' ∈ NP` reduces to the `NP`-hard `L ∈ P`, so `L' ∈ P` by
`Complexity.mem_P_of_polyTimeReducible`. -/
theorem P_eq_NP_of_NPHard_mem_P {L : Language Bool}
    (hL : NPHard L) (h : L ∈ P) : P = NP := by
  apply Set.Subset.antisymm P_subset_NP
  intro L' hL'
  exact mem_P_of_polyTimeReducible (hL L' hL') h

/-- **An `NP`-complete language is in `P` iff `P = NP`** [AB09, Theorem 2.8.3].

**Proof sketch.** (⇒) is `Complexity.P_eq_NP_of_NPHard_mem_P` on the hardness
half; (⇐) rewrites `L ∈ NP` along `P = NP`. -/
theorem NPComplete.mem_P_iff {L : Language Bool} (hL : NPComplete L) :
    L ∈ P ↔ P = NP := by
  constructor
  · exact P_eq_NP_of_NPHard_mem_P hL.2
  · intro h
    rw [h]
    exact hL.1


/-- Encode the simulated state and remembered bit. The inner `none` is a live
loop state, distinct from the outer `none` that denotes actual halting. -/
private def acceptState {Q : Type} (q : Option Q) (b : Bool) : Option (Option (Q × Bool)) :=
  match q with
  | some q => some (some (q, b))
  | none => if b then none else some none

/-- Update the bit before redirecting the successor state. In particular a bit
emitted by a halting transition is remembered. Physical output is suppressed. -/
private def acceptAction {k : ℕ} {Q : Type} (a : Action k Bool Q) (b : Bool) :
    Action k Bool (Option (Q × Bool)) :=
  ⟨a.inputTape, a.workTapes, none, acceptState a.state (a.output.getD b)⟩

/-- The halting recognizer associated to a Boolean-output decider. It uses the
same work tapes and either simulates a source state or stays in its live loop. -/
private def acceptTM (M : FinTM Bool) : FinTM Bool where
  k := M.k
  State := Option (M.State × Bool)
  tm :=
    { q₀ := some (M.tm.q₀, false)
      tr := fun q inp work => match q with
        | none => ⟨0, fun _ => (none, 0), none, some none⟩
        | some (q, b) => acceptAction (M.tm.tr q inp work) b }

/-- Configuration correspondence: the finite register holds the last emitted
bit (initially false), while the recognizer's real output stays empty. -/
private def acceptCfg (M : FinTM Bool) {x : List Bool} (cfg : Cfg M.k Bool M.State x) :
    Cfg (acceptTM M).k Bool (acceptTM M).State x :=
  ⟨acceptState cfg.state (cfg.output.getLast?.getD false), cfg.inputPos,
    cfg.workTapes, cfg.workTapePos, []⟩

/-- A live loop configuration never changes and therefore never halts. -/
private lemma acceptTM_loop (M : FinTM Bool) {x : List Bool}
    (cfg : Cfg (acceptTM M).k Bool (acceptTM M).State x) (h : cfg.state = some none)
    (t : ℕ) : (acceptTM M).tm.runFrom cfg t = cfg := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih]
    apply Cfg.ext <;> simp [MultiTapeTM.step, h, acceptTM, Action.apply]

/-- Capturing an action agrees with capturing its resulting configuration. -/
private lemma acceptCfg_apply (M : FinTM Bool) {x : List Bool}
    (cfg : Cfg M.k Bool M.State x) (a : Action M.k Bool M.State) :
    (acceptAction a (cfg.output.getLast?.getD false)).apply (acceptCfg M cfg) =
      acceptCfg M (a.apply cfg) := by
  have hlast : (cfg.output ++ a.output.toList).getLast?.getD false =
      a.output.getD (cfg.output.getLast?.getD false) := by
    cases a.output <;> simp
  apply Cfg.ext
  · dsimp only [acceptCfg, acceptAction, Action.apply]
    rw [hlast]
  · rfl
  · rfl
  · rfl
  · rfl

/-- The control transform commutes with every step, including a halt that
emits the decision bit. Rejection maps to the stationary live loop. -/
private lemma acceptCfg_step (M : FinTM Bool) {x : List Bool}
    (cfg : Cfg M.k Bool M.State x) :
    (acceptTM M).tm.step (acceptCfg M cfg) = acceptCfg M (M.tm.step cfg) := by
  cases hs : cfg.state with
  | none =>
    rw [MultiTapeTM.step_of_halt hs]
    cases hb : cfg.output.getLast?.getD false with
    | false =>
      exact acceptTM_loop M (acceptCfg M cfg) (by simp [acceptCfg, acceptState, hs, hb]) 1
    | true =>
      exact MultiTapeTM.step_of_halt (by simp [acceptCfg, acceptState, hs, hb])
  | some q =>
    have hi : (acceptCfg M cfg).inputSymbol = cfg.inputSymbol := rfl
    have hw : (acceptCfg M cfg).workTapeSymbols = cfg.workTapeSymbols := rfl
    simp only [MultiTapeTM.step, acceptCfg, acceptState, hs]
    change (acceptAction (M.tm.tr q (acceptCfg M cfg).inputSymbol
      (acceptCfg M cfg).workTapeSymbols) (cfg.output.getLast?.getD false)).apply
        (acceptCfg M cfg) = _
    rw [hi, hw]
    exact acceptCfg_apply M cfg _

/-- Initialized runs commute with the control transformation, by the step
correspondence. This is the run invariant for the HALT reduction. -/
private lemma acceptTM_run (M : FinTM Bool) (x : List Bool) (t : ℕ) :
    (acceptTM M).tm.runFrom ((acceptTM M).tm.initCfg x) t =
      acceptCfg M (M.tm.runFrom (M.tm.initCfg x) t) := by
  have hi : (acceptTM M).tm.initCfg x = acceptCfg M (M.tm.initCfg x) := rfl
  rw [hi]
  exact MultiTapeTM.runFrom_comm_of_step (acceptCfg M) (acceptCfg_step M)
    (M.tm.initCfg x) t

/-- The transformed machine halts exactly when the total source decider's bit
is true. This lemma assumes totality only for the source decider, never for the
deliberately divergent result.

**Proof sketch.** The run invariant says a transformed run can halt only when
the source has halted and its last bit is true. Determinism identifies that
completed output with the source decider's singleton output. Conversely, at a
completed accepting run the invariant immediately gives transformed halting. -/
private lemma acceptTM_halts_iff (M : FinTM Bool) (p : List Bool → Bool)
    (hM : M.Computes fun x => [p x]) (x : List Bool) :
    (∃ w t, (acceptTM M).ComputesInTime x w t) ↔ p x = true := by
  constructor
  · rintro ⟨w, t, ht⟩
    have hhalt := ((FinTM.computesInTime_iff _ _ _ _).mp ht).1
    rw [acceptTM_run] at hhalt
    change acceptState (M.tm.runFrom (M.tm.initCfg x) t).state
      ((M.tm.runFrom (M.tm.initCfg x) t).output.getLast?.getD false) = none at hhalt
    have hs : (M.tm.runFrom (M.tm.initCfg x) t).state = none := by
      cases h : (M.tm.runFrom (M.tm.initCfg x) t).state with
      | none => rfl
      | some q => simp only [acceptState, h, reduceCtorEq] at hhalt
    have hcomp : M.ComputesInTime x (M.tm.runFrom (M.tm.initCfg x) t).output t :=
      (FinTM.computesInTime_iff _ _ _ _).mpr ⟨hs, rfl⟩
    obtain ⟨s, hMs⟩ := hM x
    have hout := hcomp.output_unique hMs
    rw [hs, hout] at hhalt
    simpa [acceptState] using hhalt
  · intro hp
    obtain ⟨t, ht⟩ := hM x
    obtain ⟨hs, hout⟩ := (FinTM.computesInTime_iff _ _ _ _).mp ht
    refine ⟨[], t, (FinTM.computesInTime_iff _ _ _ _).mpr ?_⟩
    rw [acceptTM_run]
    constructor
    · change acceptState (M.tm.runFrom (M.tm.initCfg x) t).state
        ((M.tm.runFrom (M.tm.initCfg x) t).output.getLast?.getD false) = none
      rw [hs, hout]
      simp [acceptState, hp]
    · rfl

/-- Emit the fixed prefix, then copy the input verbatim. No work tape is needed;
the last finite state is the copy state. -/
private def prefixTM (w : List Bool) : FinTM Bool where
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
private def prefixCfg (w x : List Bool) (q : Option (Fin (w.length + 1)))
    (p : Fin (x.length + 2)) (out : List Bool) : Cfg 0 Bool (Fin (w.length + 1)) x :=
  ⟨q, p, fun i => i.elim0, fun i => i.elim0, out⟩

/-- After `i` prefix steps exactly the first `i` fixed bits have been emitted,
and the input head has not moved. -/
private lemma prefixTM_emit (w x : List Bool) : ∀ i (hi : i ≤ w.length),
    (prefixTM w).tm.runFrom ((prefixTM w).tm.initCfg x) i =
      prefixCfg w x (some ⟨i, by omega⟩) 1 (w.take i) := by
  intro i
  induction i with
  | zero =>
    intro hi
    apply Cfg.ext_zero_tapes <;> simp [prefixCfg, prefixTM]
  | succ i ih =>
    intro hi
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hlt : i < w.length := by omega
    simp only [MultiTapeTM.step, prefixCfg, prefixTM, dif_pos hlt, Action.apply]
    apply Cfg.ext_zero_tapes
    · rfl
    · simp
    · rw [List.take_succ, List.getElem?_eq_getElem hlt]

/-- The copy phase emits one input bit per step and preserves the fixed prefix. -/
private lemma prefixTM_copy (w x : List Bool) : ∀ i (hi : i ≤ x.length),
    (prefixTM w).tm.runFrom
      (prefixCfg w x (some ⟨w.length, by omega⟩) 1 w) i =
      prefixCfg w x (some ⟨w.length, by omega⟩) ⟨i + 1, by omega⟩
        (w ++ x.take i) := by
  intro i
  induction i with
  | zero => intro hi; simp [prefixCfg]
  | succ i ih =>
    intro hi
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hsym : (prefixCfg w x (some ⟨w.length, by omega⟩)
        ⟨i + 1, by omega⟩ (w ++ x.take i)).inputSymbol = some (x[i]'(by omega)) :=
      inputSymbolInner i (by simp only [prefixCfg]; omega) (by omega)
    change ((prefixTM w).tm.tr ⟨w.length, by omega⟩
      (prefixCfg w x (some ⟨w.length, by omega⟩) ⟨i + 1, by omega⟩
        (w ++ x.take i)).inputSymbol _).apply _ = _
    rw [hsym]
    simp only [prefixTM, Nat.lt_irrefl, ↓reduceDIte, Action.apply, prefixCfg]
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
private lemma prefixTM_computes (w : List Bool) :
    (prefixTM w).ComputesFunInTime (fun x => w ++ x) (fun n => w.length + n + 1) := by
  intro x
  apply (FinTM.computesInTime_iff _ _ _ _).mpr
  dsimp only
  rw [show w.length + x.length + 1 = w.length + (x.length + 1) by omega,
    MultiTapeTM.runFrom_add, prefixTM_emit w x w.length (Nat.le_refl _)]
  simp only [List.take_length]
  rw [MultiTapeTM.runFrom_succ_eq_step', prefixTM_copy w x x.length (Nat.le_refl _)]
  simp [prefixTM, prefixCfg, MultiTapeTM.step, Cfg.inputSymbol, Fin.ext_iff, Action.apply]

/-- The fixed-code pairing machine has the audited budget
`2|α| + |x| + 3`: two emissions per code bit, two for the delimiter, one per
input bit, and one final blank-reading step. -/
private lemma fixedPair_computes (α : List Bool) :
    (prefixTM ((α.flatMap fun b => [b, b]) ++ [false, true])).ComputesFunInTime
      (fun x => pairEncode α x) (fun n => 2 * α.length + n + 3) := by
  have hlen : (α.flatMap fun b => [b, b]).length = 2 * α.length := by
    induction α with
    | nil => rfl
    | cons b α ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil, ih]
      omega
  intro x
  have h := prefixTM_computes ((α.flatMap fun b => [b, b]) ++ [false, true]) x
  have ht : ((α.flatMap fun b => [b, b]) ++ [false, true]).length + x.length + 1 =
      2 * α.length + x.length + 3 := by
    simp only [List.length_append, List.length_cons, List.length_nil, hlen]
    omega
  simpa only [pairEncode, ht] using h

/-- The fixed-code pairing machine is polynomial-time computable. -/
private lemma fixedPair_polyTime (α : List Bool) :
    PolyTimeComputable (fun x => pairEncode α x) := by
  refine ⟨prefixTM ((α.flatMap fun b => [b, b]) ++ [false, true]),
    2 * α.length + 3, 1, fun x => (fixedPair_computes α x).mono ?_⟩
  simp only [Nat.pow_one, Nat.add_mul, Nat.mul_add, Nat.mul_one]
  omega


/-- **`HALT` is `NP`-hard** [AB09, Exercise 2.8] — for **every** representation
scheme, effective or not: the reduction embeds one *fixed* code, so only
`Turing.MachineCode.decode_encode` is used (phase-1 audit, finding 11; compare
Chapter 1's Theorem 1.10/1.11 split, where only the evaluator direction needs
effectivity).

**Proof sketch** (the audit's repaired construction, finding 6 — the earlier
divergent-searcher route is unusable because
`Turing.FinTM.one_work_tape_binary` requires a *total* function). Fix `L ∈ NP`.
(1) Obtain a **total** exponential-time decider `D` of `L` from the repaired
`Complexity.NP_subset_EXP`. (2) Normal-form `D` with
`Turing.FinTM.one_work_tape_binary` (legal: `D` is total). (3) Modify the
one-work-tape machine's finite control with a register remembering the Boolean
emission — including a bit emitted on the halting transition — and replace its
halt: halt iff the remembered bit is `true`, otherwise enter a stationary
one-state live loop (such a deliberately divergent state exists: emit nothing,
move nothing, return the same live state). This control modification needs its
own run/halting lemma — a named fill obligation. The result `S` halts on `x`
iff `x ∈ L`. (4) Code `S` with `Turing.exists_codeTM` (no totality hypothesis)
and set `α := c.encode S`. The reduction maps `x ↦ Turing.pairEncode α x`: a
fixed doubled prefix of length `2|α| + 2` followed by the verbatim input,
computable by an emit-then-copy machine in `2|α| + |x| + 3` steps (a small new
machine or prefixing lemma — the audited `pairDiagTM` computes the diagonal
pair, not this fixed-prefix function). `Complexity.HALT_pairEncode_eq_true_iff`
and `Turing.MachineCode.decode_encode` turn membership of the image in `HALT`
into "`S` halts on `x`", which is `x ∈ L`. -/
theorem HALT_NPHard (c : MachineCode) :
    NPHard {s | HALT c s = true} := by
  classical
  intro L hL
  obtain ⟨d, a, D, hD⟩ := Set.mem_iUnion.mp (NP_subset_EXP hL)
  let p : List Bool → Bool := MultiTapeTM.indicator (L : Set (List Bool))
  have hdec : D.ComputesFunInTime (fun x => [p x]) (fun n => a * 2 ^ n ^ d) := hD
  obtain ⟨M, b, hk, hM⟩ := FinTM.one_work_tape_binary D _ _ hdec
  obtain ⟨S, hS⟩ := exists_codeTM (acceptTM M) hk
  refine ⟨fun x => pairEncode (c.encode S) x, fixedPair_polyTime _, fun x => ?_⟩
  change x ∈ L ↔ HALT c (pairEncode (c.encode S) x) = true
  rw [HALT_pairEncode_eq_true_iff, c.decode_encode]
  simp only [hS]
  rw [acceptTM_halts_iff M p hM.computes x]
  simp [p, MultiTapeTM.indicator]

/-- **`HALT` is not in `NP`** [AB09, Exercise 2.8] — so, despite being `NP`-hard,
it is not `NP`-complete: `NP` languages are decidable, `HALT` is not.

**Proof sketch.** If `HALT`'s language were in `NP`, it would be in `EXP` by
the repaired `Complexity.NP_subset_EXP`, so some machine would decide it — and
a decider's output is exactly `[HALT c s]` (off the pair image `HALT` is
`false` and the rejection bit matches, per the totalization convention), making
`fun s => [HALT c s]` computable
(`Complexity.Computable` via `Turing.FinTM.ComputesFunInTime.computes`),
contradicting `Complexity.HALT_not_computable`. The audit certified this chain
valid once `NP_subset_EXP` is repaired. The `Turing.EffectiveMachineCode`
hypothesis is a **proof-route restriction, not a mathematical necessity**
(round-2 audit, finding 3 — the pre-repair docstring's trivial-machine
"counterexample" violates `decode_encode` and is unlawful): this proof reuses
Chapter 1's `HALT_not_computable`, whose own proof runs the universal
evaluator and hence needs effectivity. The round-2 audit exhibited a direct
diagonalization (diagonal pairing, the searcher's control transform with the
halt/loop roles swapped, `Turing.exists_codeTM`, no evaluator) proving `HALT`
undecidable for **every** lawful `Turing.MachineCode`; whether to add that
diagonal lemma and generalize this statement is a recorded human-review
design question (`AroraBarakChapter2Plan.md`, open design questions). Until
decided, this statement stays at the generality its cited API supports. -/
theorem HALT_not_mem_NP (c : EffectiveMachineCode) :
    {s | HALT c.toMachineCode s = true} ∉ NP := by
  classical
  intro h
  apply HALT_not_computable c
  obtain ⟨d, a, M, hM⟩ := Set.mem_iUnion.mp (NP_subset_EXP h)
  have hi : MultiTapeTM.indicator
      ({s | HALT c.toMachineCode s = true} : Set (List Bool)) = HALT c.toMachineCode := by
    funext s
    simp only [MultiTapeTM.indicator, Set.mem_setOf_eq]
    split
    · rename_i hb; exact hb.symm
    · rename_i hb; exact (Bool.eq_false_iff.mpr hb).symm
  have hdec : M.ComputesFunInTime (fun s => [HALT c.toMachineCode s])
      (fun n => a * 2 ^ n ^ d) := by
    simpa only [FinTM.DecidesInTime, hi] using hM
  exact ⟨M, hdec.computes⟩

end Complexity


## ===== machine-library-design.md =====

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


## ===== audits/ch1-infra-resolutions.md =====

# Shared infrastructure audit — resolutions. GATE: CLOSED

Three adversarial rounds over the machine-construction library's spec
layer and the timed-universal bridge export
(`audits/ch1-infra-{pack,bundle}.md` → `…-findings.md` →
`…-r2-{pack,bundle}.md` → `…-r2-findings.md` → `…-r3-{pack,bundle}.md` →
`…-r3-findings.md`). Round 3: **0 blockers, 0 majors, 3 minors — gate
condition met**; the three minors are documentation-only and are swept in
the closing commit (ledger below). This disposition authorizes **no**
claim that any sorried contract has been filled: the library's 23
contracts are now audited-true statements awaiting their fill batches.

## Round ledger

| Round | Verdict | Substance |
|---|---|---|
| 1 | 1 blocker, 2 majors, 4 minors, 1 note | `exists_loopTM` refuted (zero-step advance; the auditor's one-state instantiation plus the input-head information bound); round domain over all state words excluded the customers; D5 rejected (no dynamic assembly, no result-bearing search). The bridge export and discharge passed the completed-proof audit with **no findings** — that verdict was carried forward unchanged through rounds 2–3. |
| 2 | 0 blockers, 1 major, 3 minors | The redesigned loops (positive duration; input-indexed invariant; input-dependent step/accept), `exists_loopFindTM`, P13/P14/C1, and the §9b instantiation tables all **passed re-attack**; both round-1 refutations formally discharged. The major: the final-answer conclusion cannot discharge the frozen configuration-level `enumMachine_contracts` (the delay-machine separation). Nearly all historical attestations verified down to git blob identity. |
| 3 | **0 blockers, 0 majors, 3 minors — CLOSED** | `exists_loopCfgTM` (the configuration-level export) passed, with the auditor supplying the worst-case segment ledger and the **exact** translation onto the unchanged `enumMachine_contracts` (terminal index `2^w = R+1`, bounded orbit bridge `s_i = enumWord w i` for `i < 2^w`, budget domination `b = K(A+1)`, `e = D`) — "no customer-statement edit or replacement decider theorem is needed". D5 v3 approved per row. Stability verified byte-exactly against the hash-matched round-2 bundle. |

## Closing sweep (round-3 minors, repaired in the closing commit)

| # | Finding | Sweep |
|---|---|---|
| R3-1 | The "`loop_run` + monotonicity" corollary description is incompatible with `loop_run`'s empty-output terminal hypothesis (the exported terminal is `[false]`), and "forms" overstated the find form | All four description sites corrected (Loop module docstring, the cfg export's docstring, the decision form's note, design doc §9c): the decision form is a corollary through an **already-halted-terminal summation lemma** (the `enumLoop_run` shape), added at fill time without touching the frozen `loop_run`; the find form shares the host construction with the payload surfaced and is not claimed as a `loop_run` corollary. |
| R3-2 | The cfg sketch read an amortized aggregate bound off individual segments | Sketch rewritten with the width-based worst case: the fuel word has length ≤ `T \|x\|` and never grows, so every debit, rewind, and the final underflow-plus-emission each cost `O(T \|x\| + 1)` — no amortization needed per segment. |
| R3-3 | "The middle one is false without the shift" pointed at `incFixed = enumInc` | §9c now names the split-search equality. |

All closing edits are **comment-only**: statement slices of all four loop
declarations byte-identical, and the comment-stripped module is
byte-identical to the round-3-audited state (checked with the corrected
stripper recipe of the phase-3 erratum); `Build/Loop` re-elaborated
clean, lint 0 FAIL / 0 WARN on `Build/`.

## Errata ledger (maintainer, acknowledged across the rounds; packs preserved unmodified per precedent)

1. Round-1 attestation 4 labeled Unicode character counts as bytes
   (4,022/625 chars vs 4,085/651 bytes); corrected attestation with
   per-slice SHA-256 supplied in round 2, independently reproduced by the
   auditor.
2. Round-1 attestation 5's "import leaves" was literally false
   (`Convention` is imported by its Build siblings); restated as the
   outside-Build boundary claim with unfiltered grep evidence.
3. Round-1's lint claim described one invocation; full totals are 0 FAIL,
   7 WARN over 38 files, all seven under recorded escalations (quoted in
   the round-3 pack, attestation 6).
4. "Standard triple" overstated the Convention lemmas' prints (proper
   subsets: `[propext, Quot.sound]`; `[propext]`).
5. The immediate pre-export `Universal.lean` baseline was 2,834 lines,
   not 2,831 (the epoch-4A figure).
6. Two round-2 attack-commentary claims (zero-tape `q₀ = anchor`
   startup; off-invariant noncomputable `acceptF`) were too broad and are
   withdrawn without replacement.
7. The round-3 pack's "`loop_run` + monotonicity" corollary wording —
   R3-1 above.
   (Round-1's pre-ship manifest miscount, 17 vs 19, was caught and fixed
   by the maintainer before sending and is recorded in the session log,
   not an auditor finding.)

## Dispositions (final)

* **D4 — approved** (round 1, carried through): 2C's
  `prefixTM`/`fixedPair` promotion requests are subsumed by P3/P6; the
  proved budgets are instances of the stated linear forms; provenance
  verified from the attached batch-C report.
* **D5 — approved as version 3** (round-3 item 7), scoped to the epoch-2
  frontiers and P10: 2A at statement/interface level via
  `exists_loopCfgTM` + the §9b/§9c instantiation; P10, `pairedVerifier`
  (both orientations of P8 via the recorded pairing assembly),
  `paddedVerifier` (P10 at `(C+1, c)`, P8 at `(C, c)` — the coefficient
  shift), D-WRAP (guarded P13), D-EMIT (the canonical `H/s/t` pairing
  derivation + exact P5 unary outputs) approved; **D-MEM approved as
  explicitly limited** (timed variable-prefix extraction, unary-shape
  checks, and complete-answer recognition are named continuation
  obligations); 2B component-level only (the NDTM reverse direction is
  outside library coverage by design); clearing accepted as an internal
  discipline with per-body restoration proofs owed at fill; **E3/E4
  deferred** to those epochs' brief audits.
* **Vocabulary equalities** (round-2 note 5): `splitAtLastTrue =
  stripCertificate`; `incFixed = enumInc`;
  `solveSplit (C+1) c = certificateSplit C c` — the shift is mandatory
  and is recorded in §9c and the P10 pipeline parameters.
* The audit's pairing derivation and the C1 cross-component caveat are
  adopted as the canonical assembly recipe (§9c).

## Residual evidence limits (recorded, not defects)

Fresh-olean execution, toolchain, and mathlib-pin claims remain
execution attestations (the auditor had no Lean executable); 2B's
detailed simulation-core customer verification awaits its continuation
round with the `Nondeterminism.lean` source in scope; the escalation
records' provenance is the decision logs, attested but not attached.

## What closes, what opens

Closed: the library spec surface — `Convention` (proved) plus **23
audited-true sorried contracts** (4 wrapper, 4 loop, 15 primitive) — and
the bridge export + TMSAT discharge (proof-audited in round 1, blob-pinned
unchanged since). Next per the frozen sequencing
(`machine-library-design.md` §10): the **library fill batches**
(harvest-adaptation; the loop fill flagged for continuation budget, now
with the auditor's items 4–5 as its construction ledger), then the E2
continuation briefs citing the library.


## ===== audits/ch1-lib-agent-reports/batchW.md =====

# Machine-library fill campaign — Batch W

**Complete: 4/4 targets, 14/14 points.** The final fresh sweep passes all 57
modules with zero `error:` lines. All four targets have exactly the allowed
axiom triple and no `sorryAx`. No statement escalation was needed.

## Revision and scope

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Required base branch: `complexity/arora-barak-ch1`.
- Base commit: `e346139ccc9e3141908f7414bf27f74d8759c9be`.
- Working branch: `fill/lib-W`, created directly from that base as instructed
  by `briefs/lib-fill-batchW.md`.
- Delivery commit: `f34cfd2686c9b426fcf71f61378c77973cad011a`.
- The only repository file changed is
  `TCSlib/Complexity/TuringMachine/Build/Wrappers.lean`.
- No push, pull request, or change to another existing branch was made.
- Final source: 687 lines, 7 existing public declarations, 20 new private
  declarations, no admissions. The file remains below the brief's 1000-line
  threshold; no size escalation is required.

## Targets, in fill order

| Target | Implemented proof route |
|---|---|
| `Turing.capture_run` | Induction on elapsed steps. `capture_apply` splits source and capture tapes, using `bufferTape_append` for an emission. The liveness guard permits the final halting transition, whose emission is captured before returning. Arbitrary prefixes and physical output are preserved. |
| `Turing.FinTM.redirectTM_computes` | Lockstep with the register equal to the optional last source emission. The register updates before the halt test. The correspondence includes absorbing source halts, so it applies directly at the supplied budget and gives empty output. |
| `Turing.FinTM.redirectTM_live` | The same correspondence includes the stationary live loop after a mismatching source halt. Any alleged redirected halt forces a genuine source halt with matching last bit; output uniqueness contradicts the supplied mismatching completed output. This includes empty output. |
| `Turing.FinTM.computesFunInTime_cond` | Pad the decider with blank branch tapes and instantiate `capture_run` with the actual controller as host. Two transitions read its captured singleton. A quantitative refinement of `rewind_from_any` rewinds the original input. `branchTM` then runs from its genuine initial configuration. The construction supplies multiplier **5**, without a monotonicity hypothesis. |

The redirect engine strengthens the first-halt invariant to an all-time
correspondence by handling both absorbing halt and stationary live-loop steps.
Consequently the halting clause does not need a separate final call to
`ComputesInTime.mono`; the absorption is inside the invariant. The conditional
clause uses `ComputesInTime.mono` for the branch maximum and final budget.

The conditional prefix is at most `2 * T₀ n + 5`; the selected branch takes at
most `max (T₁ n) (T₂ n)` further steps. Lean proves that their sum is at most
`5 * (T₀ n + max (T₁ n) (T₂ n) + 1)`.

Harvest sources acknowledged: the controller/capture engine in
`TuringMachine/Composition.lean`; the `acceptCfg`/`acceptTM` invariant family in
`ClassNP/Reductions.lean`; the `enumCapture_step`/`enumCapture_run` templates in
`ClassNP/EXP.lean`; and the `universalCaptureTM` layer in
`TuringMachine/UniversalStartup.lean`. The code adapts these routes locally and
does not reference any other file's private declarations. Public tape-block,
branch, buffer, and scan lemmas come from `TuringMachine/Simulation.lean`.

## New private declarations

The first declaration is in namespace `Turing`; all others are in
`Turing.FinTM`.

| Declaration | Meaning |
|---|---|
| `capture_apply` | Applying the transformed action equals capturing the source action's resulting configuration. |
| `redirectState` | Map source state and optional last bit to simulation, halt, or the live loop. |
| `redirectAction` | Suppress output and update the register before redirecting control. |
| `redirectCfg` | Preserve source input/work fields, store its last bit, and clear physical output. |
| `redirect_loop` | A configuration in the stationary live state is fixed for every run length. |
| `redirect_apply` | Redirection commutes with action application. |
| `redirect_step` | Redirection commutes with every step, including steps after source halt. |
| `redirect_run` | The initialized redirected run equals the correspondence applied to the source run. |
| `timedPadTM` | Simulate the decider with an additional idle tape bank. |
| `timedCondTM` | The finite capture/read/rewind/branch controller. |
| `timedBranchCfg` | Embed a branch configuration while retaining decider tapes and the captured bit. |
| `timedControlCfg` | Capture the padded decider with both branch banks blank. |
| `timed_capture` | Instantiate the public capture theorem through the first decider halt. |
| `timed_control_init` | Identify the host's actual initial configuration with the captured padded source initial configuration. |
| `timed_input_bound` | A run's input position is at most its initial position plus elapsed steps. |
| `timed_rewind` | Rewind from any input position in at most that position plus two steps, preserving work and output. |
| `timed_branch_run` | Branch lockstep retains the inactive decider and capture tapes. |
| `timedReadyCfg` | Branch work is initialized, the verdict is in control, and only input rewind remains. |
| `timed_read` | A halted singleton-output capture reaches the ready configuration in exactly two transitions. |
| `timed_start` | A completed decider run reaches the selected branch's initial configuration within twice its budget plus five. |

## Freeze, documentation, and requested shared lemmas

`verification/check-freeze.py` and `logs/freeze.log` verify:

- All seven existing declaration signatures and their public order are
  unchanged; all three existing definition bodies are unchanged.
- Every existing declaration docstring remains byte-identical.
- Imports and option headers are unchanged; all new declarations are private.
- No `sorry`, `admit`, `axiom`, `unsafe`, or `implemented_by` occurs in the
  comment-stripped edited source.
- The repository diff against the pinned base touches only the owned file.

The sole edit to existing prose is an **append-only module implementation
note**, disclosing that the four contracts are now proved and recording the
conditional controller's bound. Original spec-phase descriptions and every
target docstring are retained.

**Requested shared lemmas:** consider serial promotion of `timed_input_bound`
to the run calculus and `timed_rewind` to `Simulation.lean`. They are generic
in tape count and state type, and independent of the conditional controller.
They remain private copies here under the ownership rule. No shared edit is
needed to integrate this batch. **Escalations: none.**

## Verification

- Lean: **4.25.0**, release commit
  `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`.
- Mathlib: **`029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`**, from the unchanged
  committed manifest. Cache setup required interrupted retries, finally using
  an isolated cache for the 57-module order's imported dependencies. The
  successful fetch unpacked 916 cache files. No `lake build` was run.
- Checks use the committed `scripts/lean_check_tree.sh`. After proof
  development and bootstrap, the final downstream sweep checks positions
  **10–57: 48 PASS, exit 0, zero errors**.
- The final sweep uses a separate initially empty olean tree:
  **57/57 PASS, exit 0, zero errors**. It reports **47 out-of-scope admission
  warnings**, none in `Build/Wrappers.lean`; their files are unchanged.
- Axiom prints use this same final fresh olean tree; all four are:

```text
'Turing.capture_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.redirectTM_computes' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.redirectTM_live' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_cond' depends on axioms: [propext, Classical.choice, Quot.sound]
```

- Style lint on `Build/`: **0 FAIL, 0 WARN**. The broader campaign invocations
  report **0 FAIL, 6 WARN** on `TuringMachine/` and **0 FAIL, 1 WARN** on
  `ClassNP/`; all seven warnings concern unchanged pre-existing files over
  1000 lines. A supplemental whole-`Complexity/` invocation reports 14
  pre-existing failures, all in unchanged legacy `NPReductions/` files,
  outside this campaign. All invocation logs are included with their scope.
- `git diff --check`: pass. The post-commit working tree is clean.

Final sweep tail:

```text
CHECK 54 TCSlib/Complexity/Uncomputability
PASS 54 TCSlib/Complexity/Uncomputability
CHECK 55 TCSlib/Complexity/Formulas
PASS 55 TCSlib/Complexity/Formulas
CHECK 56 TCSlib/Complexity/CookLevin
PASS 56 TCSlib/Complexity/CookLevin
CHECK 57 TCSlib/Complexity/ClassNP
PASS 57 TCSlib/Complexity/ClassNP
```

## Archive and integration

The archive contains this report, the full modified source at its repository
path, one `git format-patch` patch, `fill-lib-W.bundle`, verification programs,
the final/downstream/style/freeze/axiom logs, and `SHA256SUMS` over every other
archive member. Verify with `sha256sum -c SHA256SUMS` from the extracted root.

The bundle is **incremental**, advertising `refs/heads/fill/lib-W` and requiring
the pinned base commit above. `git bundle verify` succeeds in the base
repository. This avoids including unrelated repository history. The patch is
the normal integration route (`git am -3`), preserving this batch's author.


## ===== audits/ch1-lib-agent-reports/batchP.md =====

# Batch P — partial fill delivery

**Status: 11 of 15 targets filled, in the prescribed order.** The continuation
frontier is target 12, `computesFunInTime_pairLenCheck`. Targets 12–15 retain
their original `sorry` bodies. This is the partial ZIP delivery permitted by
`briefs/lib-fill-batchP.md`; it is not a completed primitive-catalog batch.

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Required base branch: `complexity/arora-barak-ch1`.
- Base commit: `e346139ccc9e3141908f7414bf27f74d8759c9be`.
- Local working branch: `fill/lib-P`, created directly from that base.
- Delivery commit: `b855effc50795b4aa1625c9963b8387901e6af0d`.
- Only changed repository file:
  `TCSlib/Complexity/TuringMachine/Build/Primitives.lean`.
- No push or PR was made. No other branch was checked out or changed.

## Target ledger, in fill order

All names below have prefix `Turing.FinTM.computesFunInTime_`.

| # | Target | Status | Construction and source | Validation before physical output |
|---|---|---|---|---|
| 1 | `prepend` | Filled | In-file `catalogPrefixTM` and its emission/copy invariants, adapted from `ClassNP/Reductions.lean`'s private `prefixTM` family. The sharp source budget is weakened to the frozen uniform linear envelope. | Every input is legal; no parser guard is needed. |
| 2 | `pairEncodeFixed` | Filled | Apply target 1 to the doubled fixed first word followed by `[false,true]`. This is the `fixedPair_computes` harvest's fixed-first-component direction. | Every input is legal. |
| 3 | `pairDup` | Filled | New zero-work-tape `pairDupTM`: double the first input pass, emit the first separator bit, rewind, emit the second separator bit, copy the input. Exact budget `4(n+1)`. | Every input is legal; no buffering obligation. |
| 4 | `incFixed` | Filled | New zero-work-tape `incFixedTM`, adapting the enumerator's little-endian carry discipline from `ClassNP/EXP.lean` (`enumCarryTM`/`enumCarry_correct`) to native input and physical output. Bound `3(n+1)`. | State 0 scans silently for the first false; an all-true word, including `[]`, halts silently. Emission begins only after successful detection and rewind. |
| 5 | `pairValid` | Filled | New `pairValidTM`, finite control retaining the first bit of an aligned block; `pairValid_run` proves the `n+1` bound. | Only a terminal verdict transition emits. Equal-bit blocks remain silent; `01` succeeds; `10` and missing/incomplete separators fail. |
| 6 | `pairFst` | Filled | Shared private `pairExtractTM true false` and `extract_run`; bound `5(n+1)`. | Parser states emit nothing. `extract_block` sends a validated `01` to rewind/replay; malformed cases halt silently. The buffered decoded prefix is replayed only after this seam. |
| 7 | `pairSnd` | Filled | `pairExtractTM false true`; the same `5(n+1)` envelope. | The shared parser validates first. Its replay is silent when the first flag is false, and then it copies the suffix. |
| 8 | `pairConcat` | Filled | `pairExtractTM true true`; the same `5(n+1)` envelope. | Validated replay emits the buffered first component, then suffix copying emits the second. No physical output occurs during parsing. |
| 9 | `lengthBits` | Filled | Reuse the public, already-proved `Complexity.timeConstructible_id`. Its witness is exactly a linear-time machine for `Nat.bits x.length`, with the amortized in-place counter required by the sketch. | No parser. The public proof handles empty input and halts with `[]`. |
| 10 | `polyUnary` | Filled | The in-file `catalogPolyUnaryTM` family is adapted from `ClassNP/TMSAT.lean`'s `polyUnaryTM` through `poly_unary_computes`. For positive exponent, the predecessor is the loop parameter, implementing the audited `e-1` indexing. Degree zero uses the public fixed-word emission-chain contract. | Every input is legal. Coefficient zero, degree zero, and empty input are covered by the formal proof. |
| 11 | `polyBits` | Filled | Targets 10 and 9 composed with public `computesFunInTime_comp`. Monotonicity and explicit coefficient arithmetic retain exponent `e+1`. | Both total stages are already proved. |
| 12 | `pairLenCheck` | **Pending: next target** | Original admitted statement and body, unchanged. | Buffer/parse, polynomial unary generation, countdown comparison, and malformed `[false]` remain obligations. |
| 13 | `stripLast` | **Pending** | Original admitted statement and body, unchanged. | Validity and last-true detection before re-encoding remain obligations. |
| 14 | `pairMapSnd` | **Pending** | Original admitted statement and body, unchanged. | Silent parsing, relocated capture, and postcapture pair emission remain obligations. |
| 15 | `splitSolve` | **Pending** | Original admitted statement and body, unchanged. The continuation must use the audited `exists_loopFindTM` route. | The concrete body, invariant, fuel connection, and payload assembly remain obligations. |

The continuation begins at target 12; no later target was filled out of order.
No incomplete helper proof, temporary admission, or speculative controller is
included in this delivery.

## Proof-route notes and documentation preservation

The length counter reuses a **public** theorem from the already-earlier
`ClassP/TimeConstructible` module. No other module's private declaration is
cited in a proof. The prefix and polynomial-generator harvests are copied and
adapted as private declarations inside the owned file.

For fixed-width increment, the enumerator is the semantic carry template,
not a verbatim in-place-machine copy: the new machine first detects overflow
on native input, then rewinds and emits the incremented word. The final proof
handles every input by the proved all-true/first-false decomposition.

Suffix-only extraction shares the buffered parser, so it performs a silent
buffer replay before copying the suffix. This adds only linear work and
preserves the frozen function and budget.

All 15 original contract docstrings are byte-identical. The module docstring
has one appended implementation-status paragraph explaining these points and
identifying the four remaining stubs. Additional private helper docstrings and
two harvest-attribution notes were inserted without changing audited prose.

## Verification

- Lean: `4.25.0`, release commit
  `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`.
- mathlib: `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.
- PFR: `e1095d58b7c6f10734988816f7764f2103b9bf29`.
- `lake build` was never invoked. The single `lake exe cache get` invocation
  was interrupted by download/transport failures and a shared-cache
  configuration-file disappearance. The pinned 916-module import closure was
  recovered in an isolated cache using the pinned cache library's hash map,
  parallel downloads, and unpacking. Dependency pins and source files were
  not changed. `verification/cache-resume.log` records successful recovery.
- The 57-module dependency order was bootstrapped; local proof iterations
  used the owned-module checker. Later modules were checked after the initial
  fills, and the final result was checked by a complete fresh sweep.
- **Final sweep:** all 57 modules in the committed order, a fresh output tree,
  exit 0, zero error diagnostics, and `SWEEP_PASS modules=57`. All 57 expected
  headers and their order were independently recounted.
- **Admission-warning count:** 40 total: 4 wrapper, 4 loop, 4 pending primitive,
  and 28 outside Build. The owned module's final check has exactly its four
  pending-admission warnings and no other warnings.
- **Axiom checks:** all 15 target prints and checked-kernel root traversals
  passed. Every one of the 11 filled targets uses exactly
  `[propext, Classical.choice, Quot.sound]`, with an empty admission-root set.
  Each pending target has only its own unchanged root.
- **Sanctioned cross-batch roots:** `Turing.capture_run` and
  `Turing.FinTM.exists_loopFindTM` are **unused**. Pending targets are not
  presented as completed proofs justified by those roots.
- **Statement freeze:** all 15 raw signatures, and their comment-stripped
  forms, are unchanged; the public declaration sequence and multiset are
  unchanged; zero public declarations gained/lost/reordered. Each pending
  theorem through its original `sorry` is byte-identical.
- **Ownership:** the git diff from the pinned base touches only the owned
  `Primitives.lean`. `git diff --check` passed; the final worktree is clean.
- **Style lint:** 0 FAIL, 1 WARN over the four Build files. The warning is
  the owned file's size, justified below.

The axiom walker in `verification/PrimitiveAxioms.lean` adapts the committed
`ch1-infra-BridgeExportAxioms.lean` template. It traverses checked declarations'
types and values with `allowOpaque := true`, visits inductive constructors,
identifies direct `sorryAx` consumers, compares exact root sets, and rejects
any unexpected axiom. The source freeze checker and its per-signature hashes
are included in `verification/`.

### Final sweep tail

```text
MODULE 52 TCSlib/Complexity/TuringMachine
MODULE 53 TCSlib/Complexity/ClassP
MODULE 54 TCSlib/Complexity/Uncomputability
MODULE 55 TCSlib/Complexity/Formulas
MODULE 56 TCSlib/Complexity/CookLevin
MODULE 57 TCSlib/Complexity/ClassNP
SWEEP_PASS modules=57
```

## Requests and size justification

**Statement escalations: none. Shared-lemma requests: none.**

The owned file is 1,687 lines. The brief explicitly permits an over-1,000-line
file with a recorded justification. Exclusive ownership requires the finite
machines, transition/run invariants, and harvested nested-loop generator to
remain private in this one file. The generator alone needs roughly 420 lines,
and the frozen public specification/docstrings already occupy roughly 345.
The implementation shares one parser across three contracts and common scan
lemmas across the zero-tape machines. Compressing the remaining proofs to fit
1,000 lines would sacrifice the required readable invariants and sketches;
moving them into other modules would violate this batch's file boundary.
This size exception is recorded for the maintainer's decision log.

## Archive and integration

The archive contains the full modified source, one `git format-patch` patch,
an incremental git bundle, this report, verification logs/programs, and
`SHA256SUMS`. The bundle has the pinned base as its prerequisite and was
verified with `git bundle verify`. The patch changes only the owned file.
Applying it to the pinned base source in an isolated directory reproduced
the checked source byte-for-byte (`verification/patch.log`).

After verifying checksums, integrate the patch series onto the required
branch with the workflow's `git am -3` procedure. The integration commit's
source must match SHA-256
`90bd09a4deb607e47484f3fefb2163eb779d84ef45e173c7a47b07cff4f2b324`.
Re-run the repository's 57-module checker in its committed order, then run
the included axiom program with that fresh output tree first on `LEAN_PATH`.

## All new explicit private declarations

The following inventory lists all 54 new explicit private declarations in
source order. Lean-generated constructors, recursors, matchers, and instance
auxiliaries are generated from these declarations; the kernel traversal also
follows their dependencies.

| Kind | Declaration |
|---|---|
| def | `catalogPrefixTM` |
| def | `catalogPrefixCfg` |
| lemma | `catalogPrefixTM_emit` |
| lemma | `catalogPrefixTM_copy` |
| lemma | `catalogPrefixTM_computes` |
| def | `scanCfg` |
| lemma | `scanCfg_read` |
| lemma | `scanCopy_run` |
| lemma | `scanCopy_finish` |
| def | `pairDupTM` |
| lemma | `pairDup_double` |
| lemma | `pairDup_computes` |
| lemma | `scanCopy_suffix` |
| lemma | `scanTrues_run` |
| lemma | `incFixed_cases` |
| def | `incFixedTM` |
| lemma | `incFixed_computes` |
| lemma | `scanStep_right` |
| def | `pairValidTM` |
| lemma | `pairValid_block` |
| lemma | `pairValid_run` |
| lemma | `pairValid_computes` |
| def | `pairExtractTM` |
| def | `extractCfg` |
| lemma | `extractCfg_read` |
| lemma | `extract_first` |
| lemma | `extract_block` |
| lemma | `extract_rewind` |
| lemma | `extract_replay` |
| lemma | `extract_replay_finish` |
| lemma | `extract_suffix` |
| lemma | `extract_finish` |
| lemma | `extract_run` |
| lemma | `pairExtract_computes` |
| inductive | `CatalogPolyControl` |
| instance | `catalogPolyControlFintype` |
| instance | `catalogPolyControlDecidableEq` |
| def | `catalogPolyTape` |
| def | `catalogPolyMove` |
| def | `catalogPolyUnaryTM` |
| def | `catalogPolyCfg` |
| lemma | `catalogPolyMove_apply` |
| lemma | `catalogPoly_emit` |
| lemma | `catalogPoly_rewind` |
| lemma | `catalogPoly_advance` |
| def | `catalogPolyCost` |
| lemma | `catalogPoly_loop` |
| lemma | `catalogPolyTape_write` |
| lemma | `catalogPolyCost_le` |
| def | `catalogPolyCopyCfg` |
| lemma | `catalogPoly_copy` |
| lemma | `catalogPoly_setup` |
| lemma | `catalogPoly_start` |
| lemma | `catalogPoly_unary_computes` |

## Axiom prints

```text
'Turing.FinTM.computesFunInTime_prepend' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairEncodeFixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairDup' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_incFixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairValid' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairFst' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairSnd' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairConcat' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_lengthBits' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_polyUnary' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_polyBits' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairLenCheck' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_stripLast' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairMapSnd' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_splitSolve' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The complete per-target root report is in `verification/axioms.log`.

**Notation glossary.** `n` is input length; `e` is the frozen polynomial exponent; `[]` is the empty list. All Lean identifiers refer to declarations named above or in the frozen brief.


## ===== audits/ch1-lib-agent-reports/batchP2.md =====

# Batch P2 — partial continuation delivery

**Targets 12–13 are filled; targets 14–15 remain pending.** Together with the
integrated first eleven targets, the primitive catalog now has 13 of 15 filled.
This is the partial checkpoint allowed by `briefs/lib-fill-batchP2.md`, not a
completed P2 batch. The exact continuation frontier is target 14,
`computesFunInTime_pairMapSnd`; target 15's concrete loop body is not supplied.

## Repository, base, and delivery

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Required source branch: `complexity/arora-barak-ch1`.
- Required base: `90273dd6dea2f9e092ca7d4b5ab5dc72c96ef1ee`.
- The source branch was checked out first. Its observed head was
  `646b9ee6b482867cb588a67f3014dcc00ebac7d5`; the brief at that head pinned
  the older integrated checkpoint above, verified to be its ancestor.
- Working branch: `fill/lib-P2`, created from exactly the required base as
  directed by the brief. No existing branch was modified.
- Delivery commit: `f4167fc821188ef5c8ae65d340f477a3e794aa95`.
- Two commits/patches: `d94dfe8c` (target 12), `f4167fc8` (target 13 and
  proved target-14 relocation support).
- The only changed repository path is `TCSlib/Complexity/TuringMachine/Build/Primitives.lean`.
- No push or PR. The worktree is clean.

## Target ledger

| Target | Status | Construction and reused assets | Buffer-before-emit discharge |
|---|---|---|---|
| 12: `computesFunInTime_pairLenCheck` | Filled, admission-free | Existing `pairFst`/`pairExtractTM` composed with `polyUnary`/`catalogPolyUnaryTM`, then new `pairCountTM`. `capture_run` stores the generated bound; `catalogRewind`, `lenParse_run`, and `lenSuffix_run` perform the native-input comparison. | The extractor validates before writing its intermediate output; composition and `lenStart` capture it silently. The final parser emits only a terminal verdict. Malformed input produces `[false]`. |
| 13: `computesFunInTime_stripLast` | Filled, admission-free | Existing `pairSnd`/`pairExtractTM`, new `anyTrueTM`, proved `computesFunInTime_cond`, and new `rawStripTM`. Its copy, rewind, and replay invariants adapt the in-file extractor's invariant pattern. `catalogMarker_cases` proves the exact `reverse.dropWhile` semantics. | The guard establishes a valid payload containing a true bit. The successful branch silently buffers the whole original encoding, locates and erases its final marker/false-run, then replays. Invalid pairs and all-false payloads select the empty-output branch. |
| 14: `computesFunInTime_pairMapSnd` | Pending; original `sorry` unchanged | New, fully proved `catalogPayload_length` and `catalogPayload_computes` supply the relocated payload run at the required time scale. The retained-prefix/captured-output host is still missing. | No claim of a completed threaded-map controller. |
| 15: `computesFunInTime_splitSolve` | Pending; original `sorry` unchanged | The prescribed `exists_loopFindTM` instance and body remain continuation work. | No claim that candidate evaluation, restoration, stall, or anchor obligations have been filled. |

Targets were filled in order. No incomplete helper, new admission, speculative
controller, axiom, or alteration of a frozen statement is included. All existing
first-eleven proof bodies remain unchanged.

## Construction details and route adaptations

For target 12 the generator receives the first extractor's buffered output. The
proved timed composition controls the budget in that buffer's length, absorbing
the extractor's linear bound into the fixed polynomial coefficient without
changing the exponent. The captured generator may run even on malformed input;
the subsequent aligned parser still emits exactly `[false]`, with no earlier
physical output. Coefficient zero, degree zero, empty components, and a zero
countdown are covered by the formal proof.

For target 13 the successful branch strips the *whole encoding* after the guard
has proved that the last true is in the payload. `catalogPair_inverse` and
`catalogMarker_cases` show that the unchanged pairing prefix survives exactly.
This implements the audited reverse-sweep route with whole-encoding buffering
instead of separate component buffers. `rawStrip_trim` proves the two right-end
recurrences directly from `splitAtLastTrue`'s `reverse.dropWhile` definition.
The underlying construction is linear; its bound is weakened to the frozen
quadratic envelope.

The module docstring has one appended implementation note describing these
adaptations and the partial status. All 15 original public docstrings are
byte-identical. No other module's private declaration is cited. `catalogRewind`
adapts the wrapper's `timed_rewind` proof pattern using public `rewind_scan`.

For target 14, `catalogPayload_computes` deliberately uses the public
`bufferedComp_start` and `bufferedSecondCfg_run` directly. They implement
relocation through `bufferTape`/`virtualMove`. Its time is
`6 * (n + 1) + Tg n + 1`; the payload length is at most `n`, including malformed
input's empty default. Applying only the coarse public timed-composition bound
would instead evaluate `Tg` at the extractor's running-time bound, which cannot
be absorbed into a constant multiple of `Tg n` for arbitrary monotone `Tg`.

## Target-15 hypothesis map: outstanding, not asserted discharged

| Obligation | Status and required continuation |
|---|---|
| `hF` | Must instantiate `computesFunInTime_lengthBits` at fuel `R n = n`, then enlarge its linear budget to the common body envelope. The existing theorem remains available; this instance has not been written. |
| `hInv0` | Must prove the empty candidate satisfies the specified length invariant. |
| `hInvStep` | Must prove append-or-stall preserves the invariant, including length `n+1`. |
| `hstart` | Concrete body startup and its seam equation remain missing. |
| `hround` | Concrete bounded round, accepting payload, rejected scratch restoration, no-interior-anchor proof, and positive-time stall remain missing. |
| Final orbit/output/budget bridge | Must identify the unary orbit with the range search and prove the frozen exponent-`e+2` envelope through `exists_loopFindTM`. |

The sanctioned root `Turing.FinTM.loopHost_contracts` is **unused** by this
checkpoint's completed proofs. It is not used to disguise either pending target.

## Verification

- Pinned Lean: `Lean (version 4.25.0, x86_64-unknown-linux-gnu, commit cdd38ac5115bdeec5f609e9126cce00f51ae88b3, Release)`.
- Pinned mathlib checked against its actual Git checkout:
  `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.
- `lake build` was never invoked. `lake exe cache get` was attempted once but
  failed at executable-location detection before downloading. An existing local
  cache at the exact dependency pins was copied into the isolated checkout.
- This runner exposes a PID namespace that differs from its `/proc` mount.
  Lean 4.25 asks for `/proc/<getpid()>/exe`, which therefore fails even though
  `/proc/self/exe` works. The supplied `proc_self_compat.c` maps only that exact
  self-reference to `/proc/self/exe`; all other calls are unchanged. It does not
  modify Lean, its kernel, the source, or the dependency pins. The pinned release
  binaries then execute normally. Reproduction on an ordinary host needs no shim.
- The 57-module order was bootstrapped. The owned module was checked during
  proof development; the final full sweep also checks every later module.
- **Final full fresh sweep:** 57 modules in exact committed order; fresh output
  directory; exit 0; zero `error:` lines; all 57 nonempty fresh oleans verified.
- Final admission-warning count: **31** = one out-of-scope Loop admission,
  two unchanged pending primitive targets, and 28 other campaign admissions.
- Final owned-module check has exactly two admission warnings and no other
  warnings.
- **Axiom traversal:** all 15 targets printed; the 13 completed targets and all
  29 new private declarations have empty admission-root sets. `capture_run` is
  also checked admission-free. The two pending targets each have exactly their
  own unchanged declaration root. No unexpected axiom appears.
- The walker uses checked kernel declarations, including types, opaque values,
  and inductive constructors, and rejects unexpected roots and axioms.
- **Statement freeze:** all 69 existing declarations retain their signatures;
  only the proof bodies of targets 12 and 13 changed. Every other existing body
  is unchanged. Existing declaration order is unchanged; no public declaration
  is gained, lost, or reordered; all 15 public docstrings are byte-identical.
- **Lint:** 0 FAIL, 2 WARN over the four Build files. One warning is the unchanged
  Loop file's size; the other is the owned file's size, justified below.
- `git diff --check` passes; ownership is confined to `Primitives.lean`.
- Both patches apply in order to the pinned base source and reproduce the
  checked source byte-for-byte. The incremental bundle passes `git bundle verify`.

### Final sweep tail

```text
MODULE 52/57 TCSlib/Complexity/TuringMachine
MODULE 53/57 TCSlib/Complexity/ClassP
MODULE 54/57 TCSlib/Complexity/Uncomputability
MODULE 55/57 TCSlib/Complexity/Formulas
MODULE 56/57 TCSlib/Complexity/CookLevin
MODULE 57/57 TCSlib/Complexity/ClassNP
SWEEP_PASS modules=57 elapsed_seconds=146.4
```

### Axiom prints

```text
'Turing.FinTM.computesFunInTime_prepend' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairEncodeFixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairDup' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_incFixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairValid' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairFst' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairSnd' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairConcat' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_lengthBits' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_polyUnary' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_polyBits' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairLenCheck' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_stripLast' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairMapSnd' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_splitSolve' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

Full root results are in `verification/axioms.log`; freeze hashes and helper
inventory are in `verification/freeze.json`.

## Requests, size, and continuation

**Statement escalations: none. Requested shared lemmas: none.**

Final file size: **2504 lines**, compared with 1,687 at the
required base. Exclusive ownership keeps all finite controllers and simulation
invariants private in this file. The 29 new private declarations share the
existing parser/generator machinery and do not move code to other modules. The
larger size is recorded as the continuation of the brief's existing size
exception for the maintainer's decision log.

`CONTINUATION.md` records the exact target-14 frontier, the proved relocation
interface, and target-15's remaining obligations. The new helper inventory is
complete below. Generated Lean auxiliaries are covered by the kernel traversal.

## All new explicit private declarations

| Kind | Declaration |
|---|---|
| def | `lenAction` |
| def | `pairCountTM` |
| def | `lenCfg` |
| lemma | `lenCfg_read` |
| lemma | `lenAction_apply` |
| lemma | `lenSuffix_run` |
| lemma | `lenParse_first` |
| lemma | `lenParse_block` |
| lemma | `lenParse_run` |
| lemma | `catalogRewind` |
| lemma | `lenStart` |
| lemma | `pairCount_computes` |
| def | `rawStripTM` |
| def | `stripCfg` |
| lemma | `catalogBuffer_erase` |
| lemma | `rawStrip_copy` |
| lemma | `rawStrip_rewind` |
| lemma | `rawStrip_replay` |
| lemma | `rawStrip_finish` |
| lemma | `rawStrip_erase` |
| lemma | `rawStrip_trim` |
| lemma | `rawStrip_computes` |
| def | `anyTrueTM` |
| lemma | `anyTrue_run` |
| lemma | `anyTrue_computes` |
| lemma | `catalogPair_inverse` |
| lemma | `catalogMarker_cases` |
| lemma | `catalogPayload_length` |
| lemma | `catalogPayload_computes` |

## Integration

Verify `SHA256SUMS`, then apply the two patches in order with `git am -3` onto
the intended campaign checkpoint. Do not substitute another base silently.
The integrated source must have SHA-256:

`b3fe72dc57efaf817ce5da01ed27361ed37dea72e3cecaa6dedb5d650c124359`

Re-run the 57-module checker and the supplied axiom traversal on the fresh output
tree. The archive contains source, patches, incremental bundle, this report,
continuation notes, checksums, logs, and verification programs; it does not ship
cached oleans or the copied toolchain.

**Notation glossary.** `n` is physical input length; `Tg` is the target-14
hypothesis's monotone time function; `R` is target-15 fuel; `e` is its frozen
polynomial exponent. All other code identifiers name the committed contracts or
private declarations listed above.


## ===== audits/ch1-lib-agent-reports/batchP2-continuation.md =====

# P2 continuation frontier

Status: targets 12 and 13 filled; 14 and 15 retain their original admitted bodies.
Required original base: 90273dd6dea2f9e092ca7d4b5ab5dc72c96ef1ee.
This checkpoint: f4167fc821188ef5c8ae65d340f477a3e794aa95.
Only Primitives.lean is changed. Follow the next maintainer brief for its exact
integrated base; this document does not authorize work on a different branch.

## Target 14: pairMapSnd

Available and proved in this checkpoint:

- `catalogPair_inverse`: a successful parse reconstructs its exact encoding.
- `catalogPayload_length`: the total suffix extractor's output length is at most
  the physical input length, including the malformed empty default.
- `catalogPayload_computes`: the explicit machine
  `bufferedCompTM (pairExtractTM false true) Mg` computes
  `g ((pairDecode x).map Prod.snd |>.getD [])` within
  `6 * (n + 1) + Tg n + 1`, using the actual suffix-length bound.
- `catalogRewind`: quantitative input rewind preserving all tapes/output.
- `lenStart`: a concrete `capture_run` host-instantiation example, choosing the
  least halt time to satisfy its liveness guard. It is specialized to
  `pairCountTM`, so adapt its proof to the threaded-map host instead of pretending
  its endpoint already supplies that host.

Still missing: the finite controller retaining/replaying the first component
and capturing/replaying the transformed payload, with malformed-input silence.
`catalogPayload_computes` by itself emits only the transformed payload, so it is
not the threaded map. One possible continuation is to capture this proved total
payload machine on the original input, silently validate/recover the encoded
first-component prefix, and replay prefix/separator plus captured output. Prove
the exact phase seams and total bound; the sketch alone discharges nothing.
The direct parser-plus-relocated-capture route in the brief is also available.

Do not use a coarse composition bound `Tg (5*(n+1))` and then assert it is a
constant multiple of `Tg n`: arbitrary monotonicity does not imply that. Use the
proved actual-payload bound. `capture_run` is proved and must introduce no
admission. Nothing in target 14 is sanctioned to depend on `sorryAx`.

## Target 15: splitSolve

No target-15 body or instance proof is delivered. The original audited
`exists_loopFindTM` route is still binding. Instantiate the specified unary
candidate state, append-or-stall step, length invariant, acceptance equation,
encoded split payload, and fuel `R n = n`. Use the existing lengthBits witness
for fuel. Construct and prove startup, each candidate round, scratch restoration,
anchor discipline, and a positive-time stall beyond the final candidate.

The invariant admits arbitrary bit patterns unless explicitly strengthened and
proved; a round that uses lengths must preserve existing bits when appending or
stalling. Prove the `Nat.beq_eq`/range-search and unary-orbit bridge, then the
final exponent-`e+2` arithmetic. The only allowed root is `loopHost_contracts`,
reached through `exists_loopFindTM`, until the concurrent loop fill is integrated.
This checkpoint does not use that root.

## Reproduction

Run the pinned Lean 4.25.0 per-module checker in the committed 57-module order.
Never run `lake build`. Use a fresh olean directory and run
`verification/PrimitiveAxioms.lean` with that directory first on `LEAN_PATH`.
The expected current roots are empty for the first 13 targets and the 29 new
private declarations, and exactly each pending theorem itself for targets 14–15.
Update those expectations when the actual target proofs are completed.

The source's public docstrings and signatures are preserved. Append implementation
notes when adapting routes; do not alter the audited statements. Every helper
stays private and is listed in the next report.

Notation: `n` is input length; `Tg` is the given monotone running-time function;
`R` is loop fuel; `e` is the target's polynomial exponent.


## ===== audits/ch1-lib-agent-reports/batchP3.md =====

# Batch P3 — partial checkpoint

**Target 14 is proved. Target 15 remains open.** The P3 admission-free closure gate is not met. This is the continuation delivery allowed by the brief, with 4 of the 8 target points completed; the additional target-15 component proofs are not counted as a completed contract.

## Repository and scope

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Required and actual base: `b2f464197cfd071ff46b3f89aa611285d3983908`.
- Checkpoint commit: `aa1bad68313cb2bcdb0e8c6245c2b31ae3616063`.
- Working branch throughout: `complexity/arora-barak-ch1`, as explicitly requested. No other branch was created or modified; nothing was pushed and no PR was opened.
- The P3 brief was read at the branch's documentation commit `b8d569d27e6658cc38edb79f4135ee8f480cee70`; the clean checkout was then pinned to its required integrated source base.
- Only tracked source change: `TCSlib/Complexity/TuringMachine/Build/Primitives.lean`.
- Final source size: **3684 lines**, versus 2,504 at the base. The brief's existing size exception and exclusive-file ownership require keeping these private helpers in this file. No code was moved elsewhere.
- Added precise import: `TCSlib.Complexity.TuringMachine.Build.Loop`, for the proved conditional loop instance.

## Target disposition

| Target | Disposition |
|---|---|
| 1–13 | Previously proved; all existing declarations unchanged |
| 14, `computesFunInTime_pairMapSnd` | Filled, standard axioms only |
| 15, `computesFunInTime_splitSolve` | Original admitted proof body unchanged; concrete combined body and its `hround` proof remain missing |

### Target 14: construction, phase seams, and bound

`pairMapTM` captures the proved `catalogPayload_computes` source on the original physical input. `mapStart` reaches a silent validator with the capture head at zero and the native input at its origin. `mapValidate` either halts malformed inputs with empty output or reaches the second input-rewind seam. `catalogRewind` restores the native input again; `mapPrefix_replay` emits the exact encoded first component and separator; `mapPayload_replay` and `mapPayload_finish` emit the saved transformed suffix and halt.

The source bank remains intact throughout. Validation finishes before the first physical emission. The capture correspondence includes a source emission on its halting transition. The least source halt supplies the required liveness guard.

For a source time bound `T`, `pairMap_computes` proves `4*(T n+n+3)`. Its replay bound uses `MultiTapeTM.output_length_le`. Substituting the existing actual-payload bound gives

```text
4*(6*(n+1) + Tg n + 1 + n + 3)
= 28*n + 4*Tg n + 40
≤ 40*(n+1+Tg n).
```

Thus the public coefficient is 40. There is no evaluation of `Tg` at an inflated composition bound.

### Target 15: hypothesis map and exact remaining gap

| Loop obligation | Current evidence |
|---|---|
| `hF` | `splitSolve_of_body` obtains `computesFunInTime_lengthBits` and enlarges the common coefficient |
| `hInv0` | Discharged inside `splitSolve_of_body` for the empty initial candidate |
| `hInvStep` | `splitStep_inv`, for the original length-only invariant and arbitrary bits |
| `hstart` | Still an explicit hypothesis of `splitSolve_of_body`; no combined body witness is delivered |
| `hround` evaluation | `splitPrepare_run` / `splitPrepare_first`, `splitCount_run` / `splitCount_firstHalt`, `splitCount_accept`, and `splitPoly_loop_end` are proved components |
| `hround` rejection and stall | `splitRestore_run` restores the exact state-word seam; `splitRestore_first` proves positive duration and first return for that standalone component, including preservation of past-end candidate bits |
| `hround` acceptance | Missing native-prefix/suffix output controller and its proof |
| Complete anchor discipline and common body bound | Missing for the combined controller; standalone first-return facts are not claimed as a full discharge |
| Orbit, least search, failure, and payload bridges | `splitStep_orbit`, `splitFind_eq`, `splitFind_none`, `splitLoop_result` |
| Final exponent arithmetic | `splitLoop_bound`, used in `splitSolve_of_body` |

`P3-continuation.md` describes the proved configurations and the unfilled phase connections. No new helper is admitted. The sole remaining original admission is deliberately visible, and no axiom traversal expectation pretends it has been discharged.

## Freeze and verification

- Comment-stripped comparison preserves all **98** pre-existing declarations: target 14's signature is unchanged; every other existing declaration is unchanged in full. Existing declaration order is unchanged.
- All **15 public signatures and public docstrings** are unchanged. The new module-level implementation note is append-only.
- All **55** new declarations are private. The complete list is below.
- Fresh **57/57 module sweep**, required order, zero errors, exit zero; fresh output tree recorded in `environment.json`. No `lake build` was run.
- `lake exe cache get` was invoked once and completed successfully. Initial bootstrap overlapped cache population and was restarted; the delivered full fresh sweep is the verification gate.
- Pinned Lean 4.25.0, commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`; mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.
- All 23 contract axiom prints are included. Fourteen completed primitive contracts and all eight wrapper/loop contracts have at most the standard triple. Target 15 still prints `sorryAx`.
- Kernel-environment traversal checks all 55 new private declarations and all contracts. A shared traversal over all **984 Build declarations** finds exactly `[Turing.FinTM.computesFunInTime_splitSolve]`.
- Final sweep admission warnings: **29 = 1 unfinished Build target + 28 unchanged out-of-scope campaign admissions**.
- Style lint on all four Build files: **0 FAIL, 2 WARN**. The warnings are the inherited Loop size and the owned Primitives size; the required owned-file constraint and existing size exception are recorded above.
- `git diff --check` passes; tracked diff touches only the owned file.
- Format-patch replay on a clean checkout of the exact base succeeds and reproduces the full source byte-for-byte; the incremental bundle verifies against the same base.

Final sweep tail:

```text
MODULE 52/57 TCSlib/Complexity/TuringMachine
MODULE 53/57 TCSlib/Complexity/ClassP
MODULE 54/57 TCSlib/Complexity/Uncomputability
MODULE 55/57 TCSlib/Complexity/Formulas
MODULE 56/57 TCSlib/Complexity/CookLevin
MODULE 57/57 TCSlib/Complexity/ClassNP
SWEEP_PASS modules=57 elapsed_seconds=159.8
```

The axiom program is a **partial-checkpoint** gate. Its target-15 expected root must become empty after the actual body proof is completed. Therefore neither the requested zero-`sorry` owned-file condition nor the zero-`sorryAx` Build closure condition is asserted here.

## New private declarations

- `mapAction`
- `pairMapTM`
- `mapCfg`
- `mapAction_apply`
- `mapBuffer_rewind`
- `mapStart`
- `mapCfg_read`
- `mapParse_first`
- `mapParse_block`
- `mapValidate`
- `mapPrefix_replay`
- `mapPayload_replay`
- `mapPayload_finish`
- `catalogPair_length`
- `pairMap_computes`
- `splitStep`
- `splitAccept`
- `splitStep_inv`
- `splitStep_orbit`
- `catalogFind_congr`
- `splitFind_eq`
- `splitFind_none`
- `splitLoop_result`
- `splitLoop_bound`
- `splitPos`
- `splitPos_read`
- `splitPos_succ`
- `splitScratch`
- `splitScratch_erase`
- `splitRestoreTM`
- `splitRestoreScan`
- `splitRestore_scan`
- `splitRestoreClean`
- `splitRestore_append`
- `splitRestore_rewind`
- `splitRestore_run`
- `splitCountAction`
- `splitCountCfg`
- `splitCount_over`
- `splitCount_apply`
- `splitCount_run`
- `splitPoly_loop_end`
- `catalogFirstEntry`
- `splitRestore_first`
- `splitCount_accept`
- `splitCount_firstHalt`
- `splitPrepareTM`
- `splitPrepareScan`
- `splitPrepare_scan`
- `splitPrepareReady`
- `splitPrepare_extra`
- `splitPrepare_rewind`
- `splitPrepare_run`
- `splitPrepare_first`
- `splitSolve_of_body`

## Requests and escalations

Requested shared lemmas: **none**. Statement or realizability escalations: **none**. No frozen statement was changed. The unfilled body is a proof/construction frontier, not a claimed counterexample.

## Archive and reproduction

The archive is flat: every member is at the ZIP root, including `SHA256SUMS`. `Primitives.lean` is the complete modified source; its repository destination is the owned path above. Apply the included format-patch on the exact base, or use the bundle's branch endpoint. Both delivery forms preserve the one source commit.

The full sweep is reproduced with the pinned compiler on `PATH`, the pinned mathlib cache populated, and a fresh `TCSLIB_OLEANS` directory:

```bash
python3 /path/to/extracted/sweep.py
python3 /path/to/extracted/run_axioms.py --repo . --oleans "$TCSLIB_OLEANS"
```

Run those commands from the repository root. `PrimitiveAxioms.lean` must sit beside `run_axioms.py`, as it does in this flat archive. `freeze.py` records this checkpoint's exact comparisons; its output and JSON inventory are supplied. The small `proc_self_compat.c` workaround used here only maps the current process's `/proc/<pid>/exe` readlink to `/proc/self/exe`; it changes no Lean proof or kernel behavior and is normally unnecessary on a standard host.

Notation: `n` is physical input length; `T` is a source time bound; `Tg` is the given monotone payload time bound. Other identifiers are source declarations or the brief's named hypotheses.


## ===== audits/ch1-lib-agent-reports/batchP3-continuation.md =====

# P3 continuation frontier

Status: target 14 is filled. Target 15, `computesFunInTime_splitSolve`, retains its original admitted body. This is a partial checkpoint, not library closure.

Required P3 base: `b2f464197cfd071ff46b3f89aa611285d3983908`.
Checkpoint: `aa1bad68313cb2bcdb0e8c6245c2b31ae3616063`.
All source changes are in `TCSlib/Complexity/TuringMachine/Build/Primitives.lean`.
The next maintainer brief controls the next exact integrated base; this document authorizes no different branch or statement changes.

## Completed target 14

`computesFunInTime_pairMapSnd` is proved, with coefficient 40 and no admission dependency. Its source is `pairMapTM (bufferedCompTM (pairExtractTM false true) Mg)`.

The exact phase lemmas are:

- `mapStart`: capture the actual-payload computation on the original input, rewind the capture, and rewind the native input. Physical output is empty at the validator entry.
- `mapValidate`: silent aligned validation, in at most the unread input length plus one. Malformed inputs halt with empty output; valid inputs reach the second native-input rewind.
- `catalogRewind`: the second native-input rewind, instantiated in `pairMap_computes`.
- `mapPrefix_replay`: emit the original doubled first component and separator, in exactly twice the first-component length plus two steps. The captured payload head stays at zero.
- `mapPayload_replay` / `mapPayload_finish`: replay the captured result once, then halt on its right blank.
- `pairMap_computes`: assemble those phases at `4 * (T n + n + 3)` for a total source with time bound `T`.

The public proof invokes `catalogPayload_computes hg hTg`, whose source time is `6 * (n+1) + Tg n + 1`. Substitution gives at most `40 * (n+1+Tg n)`. The completed proof never substitutes a padded argument into `Tg`.

## Checked target-15 components

These are separate proved components. They are not yet an instantiated body satisfying `hround`.

### Semantic and loop closure

- `splitStep` is exactly the audited append-or-stall function, preserving all existing bits.
- `splitAccept` is the audited length equation as a Boolean.
- `splitStep_inv` proves closure of the original length-only invariant, for arbitrary bit patterns.
- `splitStep_orbit` proves the unary orbit through the one-past-end state.
- `splitFind_eq`, `splitFind_none`, and `splitLoop_result` identify the finite search, its failure branch, and the payload with `solveSplit`.
- `splitLoop_bound` proves the final exponent calculation.
- `splitSolve_of_body` calls the proved `exists_loopFindTM`. It obtains the existing `lengthBits` fuel machine, enlarges the body coefficient to cover its bound, discharges `hInv0` and `hInvStep`, and transfers the loop's result and time bound. Its two explicit missing arguments are the actual `hstart` and `hround` proofs. It is a conditional, admission-free theorem; it supplies no missing body existence claim.

### Candidate preparation

`splitPrepareTM k` uses tape zero for the candidate and `k` scratch tapes. The candidate may contain arbitrary bits.

`splitPrepare_run` starts from `Cfg.ofWords (0,false) (stateWord (k+1) s)` and runs exactly `2*(s.length+1)` silent steps. It preserves the candidate, fills every scratch tape with `s.length+1` trues, and restores all work heads to zero. The native input head is `splitPos w s.length`; the finite flag records whether the candidate length already exceeded the native input length.

`splitPrepare_first` supplies the same endpoint at the first visit to its return state. It supports a host embedding that intercepts that return.

### Counted evaluation

`splitCountAction`, `splitCountCfg`, `splitCount_apply`, and `splitCount_run` are a generic source-to-host correspondence. The source has empty virtual input and arbitrary initialized source tapes. It occupies the successor-indexed work tapes; tape zero retains the candidate at head zero.

The host suppresses every source emission and instead consumes one native input cell. The native head saturates at the right boundary. A finite flag records consumption past that boundary. The counted amount is the candidate length plus the source's output length. The correspondence includes an emission on the halting transition.

`splitCount_accept` proves that blank native input together with no overflow is exactly equality of the counted amount and the native input length.

`splitCount_firstHalt` removes any padded halted suffix of a source time bound, retains the exact source-bank endpoint, and reaches the host return state at the first source halt. A host must still discharge its transition-table agreement argument.

For positive exponent, `splitPoly_loop_end` supplies the exact endpoint of the existing generator's nested-loop phase on a unary scratch bank of side length `s.length+1`: output length `C*(s.length+1)^(c+1)`, all source work heads back at zero, unary tapes unchanged, halted in `catalogPolyCost (s.length+1) C (c+1)+1` steps. Use `e=c+1`, not an off-by-one loop depth.

For exponent zero, an available route is `catalogPrefixTM (List.replicate C true)` on the empty virtual input: the existing `catalogPrefixTM_computes` yields exactly the constant unary output in `C+1` steps, and there are no source scratch tapes. This has not yet been packaged into the combined body.

### Exact rejection restoration

`splitRestoreTM k` starts at `splitRestoreScan k w s 0`: native input at origin, candidate unchanged at work-head zero, and every scratch tape holding `s.length+1` trues at head zero.

`splitRestore_run` clears every scratch tape, appends a true to the candidate exactly when its old length is at most the input length, and restores the native input and every work head. Its endpoint is exactly

```lean
Cfg.ofWords (4, false) (stateWord (k + 1) (splitStep w s))
```

Its bound is `2*s.length+w.length+5`. It preserves arbitrary candidate bits. Thus the one-past-end case is a silent stall at the same word, not a replacement of arbitrary bits by trues.

`splitRestore_first` strengthens this to positive duration and no earlier visit to the return state. This is the local restoration component's first-return property; it has not yet been lifted to the complete body's anchor property.

`catalogFirstEntry` is the shared absorption argument used to expose these first-return endpoints.

## Work still required

1. Construct the combined finite body, with disjoint control phases and the candidate on tape zero. Keep all helpers private in the owned file.
2. Establish its genuine startup seam. A body whose start state is the anchor and whose initial candidate is empty can have startup time zero, but prove the exact `Cfg.ofWords` equation.
3. Embed preparation and transfer its return state to counted evaluation. Prove the configuration seam, including tape ordering, source initialized-bank configuration, zero work heads, native head, flag, and empty physical output.
4. Embed the appropriate source for positive and zero exponent; discharge `splitCount_run` / `splitCount_firstHalt` table agreement.
5. After evaluation, branch on the checked acceptance predicate and rewind the native input to its origin. The candidate head is already zero; the polynomial source endpoint has every source head zero.
6. On acceptance, implement and prove an emitter for `pairEncode (w.take s.length) (w.drop s.length)`. Use the candidate only as a length counter: emit native-input bits, not candidate bits. No acceptance emitter or accepting-round proof is present in this checkpoint.
7. On rejection, identify the configuration with `splitRestoreScan k w s 0`, invoke the checked cleanup, and map its return state to the body's anchor.
8. Prove the combined round's positive duration and strict-interior anchor exclusion across every phase. The standalone components' first-return lemmas do not by themselves prove this global condition.
9. Derive one common body coefficient for `A*(n+1)^(e+1)`, using the invariant to bound candidate length, `catalogPolyCost_le` for evaluation, and the actual scan/emission overheads of the completed controller. No complete body-envelope proof is delivered.
10. Apply `splitSolve_of_body`, remove the original target-15 admission, and rerun the required checks with empty expected root sets for all fifteen targets.

Do not reuse the old coarse-composition mistake for target 14, weaken the frozen statements, silently restrict the invariant to unary words, or count the conditional `splitSolve_of_body` theorem as a body construction.

## Verification state

The fresh 57-module sweep passes with zero errors. All fourteen completed primitive contracts, all eight wrapper/loop contracts, and all fifty-five new private declarations have only standard axioms. Traversing all 984 checked Build declarations finds exactly one admission root: the unchanged `computesFunInTime_splitSolve`.

`PrimitiveAxioms.lean` deliberately retains that one expected root for this partial checkpoint. The closure requirement is not met until it is changed to an empty root set and the body proof passes. The other 28 campaign admission warnings are out of scope and unchanged.

Notation: `w` is native input; `s` is the candidate; `n` is native input length; `k` is the number of source scratch tapes; `C` and `e` are the frozen polynomial parameters; `c` is the positive-exponent generator index, with `e=c+1`; `A` is the body-envelope coefficient; `T` is a source running-time bound; `Tg` is the given payload time bound.


## ===== audits/ch1-lib-agent-reports/batchP4.md =====

# Batch P4 — machine-library closure

**Complete.** `computesFunInTime_splitSolve` is proved by a concrete finite body and the existing `splitSolve_of_body` / `exists_loopFindTM` route. There are no remaining admissions in the owned file or anywhere in `Build/`. No continuation frontier remains.

## Base, branch, and ownership

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Required and actual base: `494d48353d292cca5d90675f5421f1bce09068e3`.
- Working branch: `fill/lib-P4`, created directly from that exact base on `complexity/arora-barak-ch1`.
- The P4 brief was read from branch head `23c04aba994ae8239b502b08cd915183971b1294` before selecting its required base. The four binding documents, P3 frontier, policy, workflow, and relevant audit findings were read before implementation.
- Only `TCSlib/Complexity/TuringMachine/Build/Primitives.lean` is changed in the commit. Verification programs and delivery files are outside the repository diff.
- Delivery commit: 67bdd83f7258f1230fc9976eb0424f26449916fe.
- Final source size: 4418 lines. The P4 brief explicitly retains the existing file-size exception and requires helpers to remain in this owned file; the additional phase proofs follow that rule. No code was moved elsewhere.
- No push or pull request was made; no other local branch was modified.

## Ten-step work-plan discharge

| Step | Discharging construction or lemma | What is checked |
|---|---|---|
| 1 | `SplitBodyState`, `splitBodyTM`, private finite/equality instances | A finite controller with disjoint anchor, preparation, counting, decision, rewind, restoration, and emission phases; candidate on tape zero. |
| 2 | `splitBody_start` | The genuine initial configuration is literally the empty-candidate `Cfg.ofWords` anchor seam. Startup time zero is justified by that equation. |
| 3 | `splitEmbed_cut`, `splitBody_prepare`, `splitBank` | First-return embedding and a field-by-field dispatch seam: native head, overflow flag, candidate/source tape order, unary side length, zero heads, empty physical output. |
| 4 | `splitBody_count`, `splitSource_poly`, `splitSource_constant` | Exact table agreement for counted simulation through the first source halt, including an emitting final transition. Positive exponent uses the existing generator at depth `e`; exponent zero uses `catalogPrefixTM` on empty virtual input. |
| 5 | `splitBody_round`, `splitBody_rewind`, `splitRewindTM` | The check uses both blank native input and the no-overflow flag via `splitCount_accept`; the Boolean verdict is retained during a proved native-input rewind. |
| 6 | `splitEmitTM`, `splitEmit_double`, `splitEmit_separator`, `splitEmit_suffix`, `splitEmit_run` | The new accepting emitter reads **native-input bits** and uses candidate cells only as a length counter. It outputs exactly the doubled native prefix, `[false, true]`, and the native suffix in `s.length + w.length + 3` steps. |
| 7 | `splitBody_restore`, rejection branch of `splitBody_round` | Dispatch is identified with `splitRestoreScan … 0`. Existing exact restoration is reused, followed by one explicit transition to the anchor. Scratch is blank, all heads are home, and output is empty. |
| 8 | `splitSafe`, `splitSafe_add`, `splitSafe_one`, `splitSafe_join`, `splitBody_round` | Safe traces compose through **every** phase. The initial anchor departure takes one step; the rejecting anchor return is the final step. Every strict interior time excludes the anchor, and round duration is positive on both branches. |
| 9 | `splitBody_envelope` | Counts source time plus all scans, dispatches, rewind, emission, and cleanup. Uses the original length-only invariant, including the one-past-end state. |
| 10 | `splitSolve_source`, `splitSolve_closed`, public `computesFunInTime_splitSolve` proof | Instantiates the constructed body in both exponent cases, supplies both missing body hypotheses, and applies the existing audited loop closure. All axiom-program expectations are empty. |

The accepting and rejecting branches are both formal Lean proofs. There is no remaining conditional body-existence assumption in the public theorem: `splitSolve_source`'s exact source hypothesis is discharged by `splitSource_constant` or `splitSource_poly` in the public proof.

### Round and time details

For source duration `T`, the full round proof gives a positive duration at most

`T + 5 * s.length + 3 * w.length + 20`.

The actual accepting emitter takes `s.length + w.length + 3` steps. Its tape-zero bit values never supply output symbols. All earlier preparation, counted evaluation, checking, and rewind transitions are physically silent, so output begins only after acceptance is established.

The common body coefficient is

`A = (C + 1 + 5 * e) * 2 ^ e + 40`.

The bound uses `s.length + 1 ≤ 2 * (w.length + 1)` and the existing `catalogPolyCost_le`. It does not increase the required body exponent `e + 1`; `splitSolve_of_body` supplies the final exponent `e + 2` and enlarges the coefficient to cover the existing binary length/fuel machine.

The invariant remains exactly `s.length ≤ w.length + 1`. No all-true restriction was added. At the one-past-end state, acceptance is impossible; the existing restoration component returns the **same arbitrary-bit word**, silently and in positive time. The checked combined trace proves the anchor guard on that stall too.

### Loop-hypothesis mapping

- `hF`: the existing `computesFunInTime_lengthBits` witness, with its coefficient enlarged inside `splitSolve_of_body`.
- `hInv0`: the existing empty-word length proof in `splitSolve_of_body`.
- `hInvStep`: unchanged `splitStep_inv`.
- `hstart`: `splitBody_start`, with the proved zero-time witness.
- `hround`: `splitBody_round`, acceptance-length simplification, and `splitBody_envelope`.
- Search, failure, payload, and final exponent: unchanged `splitStep_orbit`, `splitFind_eq`, `splitFind_none`, `splitLoop_result`, and `splitLoop_bound`, reused through the existing closure.

## Freeze and verification

- Final fresh sweep: **57/57 modules passed; 0 errors; 0 Build admission warnings**. Exactly 28 unchanged out-of-scope campaign admission warnings remain.
- All **23 library contracts** print at most `[propext, Classical.choice, Quot.sound]`; every expected root set is empty.
- Whole-`Build` traversal: **1,171 checked declarations; no admission roots; no nonstandard axioms**.
- Source freeze: all **153 existing declarations** retained in order; all **15 public source declarations** and their signatures preserved; all **153 original docstrings** retained verbatim. Only the target proof body changes.
- Kernel export freeze against a separately compiled exact baseline: **78 public kernel declarations preserved**, no removed declarations, and **187 added private declarations**, including the 29 named helpers and compiler-generated descendants.
- Style lint: **0 FAIL, 2 WARN**. Warnings are the already-excepted `Loop.lean` size and the explicitly permitted owned-file size.
- `git diff --check`, bundle verification, and patch application check against a temporary index at the exact base all pass.

Final sweep log tail:

```text
MODULE 54/57 TCSlib/Complexity/Uncomputability
MODULE 55/57 TCSlib/Complexity/Formulas
MODULE 56/57 TCSlib/Complexity/CookLevin
MODULE 57/57 TCSlib/Complexity/ClassNP
SWEEP_PASS modules=57
```

The mechanical freeze check compares existing declaration order, the public declaration multiset and order, complete old declaration bodies except the target proof, the target's exact signature, and all old docstrings. It records no removed or added public declarations and no changed existing helper. All historical status/spec docstrings remain verbatim; a new closure note records the final state.

The whole-`Build` traversal checks kernel declarations, types, opaque bodies, and constructor dependencies. It also checks the axioms of every declaration in all four `Build` modules, so unused helpers are covered. Every expected admission-root set for all 23 contracts is `[]`. All 29 new named private declarations have separate axiom reports. Compiler-generated descendants are covered by the whole-tree traversal and the private-export check.

A first export check detected that `deriving DecidableEq` generated a public instance for the private control type. That intermediate version was not delivered. The final code uses an explicitly private equality instance, and the final traversal checks that the new implementation declarations and their descendants are private. The exponent-case proof is also packaged in private `splitSolve_closed`, so the public target introduces no generated public proof helper. A separately compiled baseline inventory confirms that the complete public kernel-declaration set is unchanged.

Requested shared lemmas: **none**. Statement/realizability escalations: **none**. No frozen statement was weakened, restated, renamed, or altered. Target 14 and all previous proofs are unchanged.

## New private declarations

- `splitSafe`
- `splitSafe_add`
- `splitEmbed_cut`
- `splitRewindTM`
- `splitEmitTM`
- `SplitBodyState`
- `splitBodyStateFintype`
- `splitBodyStateDecidableEq`
- `splitBodyTM`
- `splitBank`
- `splitBody_start`
- `splitEmbed_run`
- `splitBody_prepare`
- `splitBody_count`
- `splitBody_rewind`
- `splitBody_restore`
- `splitEmitCfg`
- `splitEmit_double`
- `splitEmit_separator`
- `splitEmit_suffix`
- `splitEmit_run`
- `splitSafe_one`
- `splitSafe_join`
- `splitBody_round`
- `splitSource_poly`
- `splitSource_constant`
- `splitBody_envelope`
- `splitSolve_source`
- `splitSolve_closed`

These are the 29 explicitly named implementation declarations. `SplitBodyState` also generates private constructors/recursors and related declarations; definition compilation generates private equation/proof helpers. `new-kernel-privates.txt` records all newly added checked names, and `build-declarations.tsv` records the complete checked `Build` inventory.

## Environment and reproduction

- Lean 4.25.0, compiler commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`.
- Mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`; the repository manifest and toolchain file are unchanged.
- Exactly one `lake exe cache get` invocation was made. It built the cache executable but returned status 1 without a completion message on this host. Cache setup was completed by running that executable through `lake env`; the successful cache log is included. No project `lake build` was run.
- The host required the supplied `proc_self_compat.c` shim: it maps only the current process's `/proc/<pid>/exe` readlink to `/proc/self/exe`. It does not change Lean code, proof terms, or kernel verification. Ordinary hosts should not need it.
- Bootstrap checked the first 25 modules, and the owned module plus all 31 later modules were checked after implementation. The final gate is a separate full 57-module sweep into a fresh olean tree.

From the repository at the exact base, either apply the included patch with `git am` on `fill/lib-P4`, or recover the branch commit from the bundle. `Primitives.lean` is the complete source for the owned destination path above; it is also provided for inspection. The archive contains only root-level members.

With the pinned compiler on `PATH` and the pinned dependency cache available:

```bash
python3 /path/to/extracted/sweep.py --repo . --oleans /tmp/p4-fresh-oleans
P4_KERNEL_INVENTORY=/tmp/p4-build-declarations.tsv \
  python3 /path/to/extracted/run_axioms.py --repo . --oleans /tmp/p4-fresh-oleans
python3 /path/to/extracted/freeze.py --repo .
python3 scripts/style_lint.py TCSlib/Complexity/TuringMachine/Build
```

`PrimitiveAxioms.lean` must be beside `run_axioms.py`, as it is in the archive. `SHA256SUMS` lists every other archive member; verify with `sha256sum -c SHA256SUMS` after extraction. The bundle has the exact required base as its prerequisite.

Notation: `w` is native input; `s` is the candidate word; `C` and `e` are the frozen polynomial parameters; `T` is source duration; `A` is the common body-time coefficient. Other names are existing or listed Lean declarations.


## ===== audits/ch1-lib-agent-reports/batchL.md =====

# Batch L — partial continuation checkpoint

**Status: PARTIAL. The full batch acceptance gate remains OPEN.**
`Turing.loop_run` is proved without admissions. The three finite-machine
combinators have derivations, but all depend on the single admitted private
`Turing.FinTM.loopHost_contracts`. That root is **not** the sanctioned
`Turing.capture_run` admission. This ZIP is a continuation delivery under the
brief's continuation clause, not a completed construction or a closed gate.

## Provenance and scope

- Repository: https://github.com/Shilun-Allan-Li/tcslib
- Required source branch: `complexity/arora-barak-ch1` (cloned explicitly with `--single-branch`).
- Base: `e346139ccc9e3141908f7414bf27f74d8759c9be`.
- Local working branch: `fill/lib-L`, created from that base as the committed brief directs.
- Checkpoint: `769341f5bd042f5790f7a24fdfe9e439b32ff666`.
- Execution: `lib-L-20261003T191127Z`.
- Only changed tracked file: `TCSlib/Complexity/TuringMachine/Build/Loop.lean`.
- No remote branch was pushed; no PR was created; no other branch was modified.
- The brief, workflow §4/§6, policy, W environment protocol, epoch-1 pitfalls,
  round-1 construction notes, round-3 items 4–5, and enumerator harvest were read.

All five original public declarations, their signatures, and their order are
unchanged. `stateWord`'s implementation is unchanged. Every existing declaration
docstring is preserved verbatim. The module docstring receives only an appended
checkpoint-status paragraph. The only added import is `Build.Wrappers`, for W1.
No out-of-scope admission was edited. `verification/freeze.py` reproduces these
checks; `verification/freeze.json` records their results and the source hash.

## Targets, in brief order

| Target | Checkpoint result | Proof route |
|---|---|---|
| `Turing.loop_run` | **Proved, no admission root** | Induction on the candidate count, with shifted configuration and acceptance families; compose rejected segments with `runFrom_add`. The existing exhaustion hypothesis handles zero candidates. |
| `Turing.FinTM.exists_loopCfgTM` | **Conditional; construction remains open** | Instantiate the concrete `loopHost` and generalized `loopHost_contracts` in fixed-verdict mode. The latter is the sole admitted construction frontier. |
| `Turing.FinTM.exists_loopTM` | **Conditional on the same frontier** | Apply the configuration export, the proved private `loop_halted_run`, then `ComputesInTime.mono` to absorb startup. No application of the incompatible frozen `loop_run` to a `[false]` terminal. |
| `Turing.FinTM.exists_loopFindTM` | **Conditional on the same frontier** | Instantiate the same host in payload mode and use the proved private `loop_find_run`. Its ordered-range induction and `List.find?_map` identify the first accepting payload. |

The targets were taken in the brief's order. After isolating the unfinished
second construction, the downstream corollary derivations were completed
conditionally; this does not count target 2, 3, or 4 as fully discharged.
There is one textual `sorry`, inside `loopHost_contracts`; there are no other
new admissions. `CONTINUATION.md` gives the exact declaration and remaining work.

## Audit construction ledger → implementation/proof status

| Round-3 ledger item | Checked material in this checkpoint | Still required inside `loopHost_contracts` |
|---|---|---|
| Finite controller phases | `LoopHostState`, `loopFuelSource`, `loopBodySource`, `loopControlAction`, and concrete `loopHost`; all definitions typecheck. The controller has separate fuel, startup-body, active-body, counter, and final phases. | Prove the complete phase assembly. A typechecked transition table alone is not its contract proof. |
| Fuel capture and genuine start | `loopHost_init` uses `initCfg_ofWords`; `loopHost_fuel_capture` instantiates W1 with the actual host; `loop_fuel_width` bounds bit width by the fuel budget. | Relate relocated source runs to `F`, then prove fuel capture rewind, copy/clear, and synchronized counter/capture rewind (phases 0–3). |
| Native input rewind | `loop_input_move_le`, `loop_input_run_le`, `loop_rewind_bounded`, and actual-host `loopHost_input_rewind` (phases 4–5). The bound uses the preceding run's displacement, not input length. | Connect that displacement estimate to the completed fuel setup in the startup sum. |
| Body startup and released first action | `loopBodyTM`/`loopBodyCfg`; `loopBody_stop`, `loopBody_step`, `loopBody_run`; `loopBody_capture` and actual-host `loopHost_body_capture`. The release bit forces a real source action before anchor recognition. | Lift the original seam and scratch-restoration hypotheses into the padded source; compose startup return/flag clearing and active-round returns. |
| Admissible orbit and configuration family | `loop_orbit_inv`; `loopDebit_iterate_length` and `loopDebit_iterate_value`. `loopFrame`, `loopWrite`, and `loopControl_apply` describe controller-local effects with arbitrary inactive residue. | Define the complete family of host seams, preserving fuel residue; establish startup equality and all empty-output clauses. |
| Accepting segment | `loop_first_halt` handles padded halting witnesses; body/capture lemmas preserve the halting emission; `loop_output_length_le` bounds payload length; `loopHost_replay` proves actual phase-13 replay in `payload.length + 1` steps. | Compose accepting return/flag recognition and the phase-12 rewind with final emission/replay and a uniform bound. |
| Rejecting segment before exhaustion | `loop_live_prefix`, `loop_silent_prefix`; standalone `loopBorrow_step`, `loopBorrow_run`, `loopBorrow_rewind`, `loopBorrow_correct`; exact debit arithmetic. | Lift the standalone debit into actual phases 8–9, prove flag clearing and equality to the next host seam. |
| Last rejecting segment and zero fuel | `loopDebit_success` identifies zero underflow; standalone decrement and rewind include empty width. Host phase 11 is the exhaustion dispatcher; initial release occurs before any debit. | Lift phases 8/10/11 and include underflow plus final emission in the last segment; choose and prove the halted terminal configuration. |
| Worst-case counter estimate | **Proved:** `2 * loopBorrowPos u + 2 ≤ 2 * u.length + 2`; width is preserved at every debit; fuel width is at most the actual fuel budget. No amortization is used for this estimate. | Transfer the same bound to the actual host, including its dispatch transitions. |
| Unreachable rejection terminal after acceptance | The proposed contract and controller permit the audit's arbitrary halted rejection terminal when the last candidate accepts. Local invariant lemmas apply to all orbit indices, including unreachable ones. | Implement the case split and prove the selected terminal and local contracts. |
| One constant ledger | Displacement, payload-length, counter-width, standalone counter-time, and actual replay bounds are proved. | Supply all remaining phase bounds and choose the single exported constant by the audit's maximum construction. **No completed uniform-constant proof is claimed.** |

The already-halted-terminal summation lemma is **`loop_halted_run`**. It is
admission-free, as is the first-payload summation lemma **`loop_find_run`**.
The corresponding summation proofs handle zero candidates; the host still
needs its construction proof for the separate zero-fuel/one-candidate case.

Harvests: the summation proofs adapt `ClassNP/EXP.lean`'s private
`enumLoop_run`; the fixed-width borrow privately adapts its `enumCarry*` and
buffer templates, reversing the bit roles for decrement. The bounded input
rewind follows `Simulation.lean`'s proved `rewind_from_any`/`rewind_scan` recipe,
retaining the exact time witness. No foreign private declaration is cited.
The body's stop-flag wrapper and concrete host are local constructions.

## Admissions and sanctioned W1 dependency

The kernel-environment traversal includes declaration types and values,
including opaque values, and follows constructor dependencies. It checks the
four targets and every one of the 55 new private declarations (59 checks).

- `loop_run`: no admission roots; only the standard axiom triple.
- All three public combinators: exactly `[Turing.FinTM.loopHost_contracts]`.
- `loopBody_capture`, `loopHost_body_capture`, `loopHost_fuel_capture`:
  exactly `[Turing.capture_run]`, the sanctioned W1 root.
- `loopHost_contracts`: its own direct admission root.
- All other new private declarations: no admission root.
- Every checked axiom list is a subset of the standard triple, with `sorryAx`
  present exactly for the declared roots above. No other axiom was found.

Thus W1 is used and root-verified in the capture helpers. It is currently
**unused in the public targets' proof dependency graph**, because the admitted
assembly has not yet consumed those helpers. Removing the assembly admission
must produce actual proof dependencies on the supporting lemmas; the present
root audit must not be misread as construction completion.

Headline prints from the fresh tree:

```text
'Turing.loop_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.exists_loopCfgTM' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.FinTM.exists_loopTM' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.FinTM.exists_loopFindTM' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

## Verification

- Lean `4.25.0`, release commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`.
- Mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`; committed manifest unchanged.
- `lake exe cache get` was invoked once. It failed during transfer; isolated
  cache recovery used the built cache executable to fetch 566 missing files.
  This setup failure was repaired before the successful sweeps. No `lake build`
  was invoked. `verification/environment.json` records this recovery explicitly.
- Bootstrap checked all modules in the committed order; subsequent iteration
  checks covered the owned module and the later 47-module suffix.
- **Final full fresh sweep:** all 57 modules, exact committed order, 57 fresh
  nonempty oleans, **zero `error:` lines**, exit 0. The tree was new and separate
  from the bootstrap/iteration output.
- Final sweep admissions: 48 declaration warnings = 4 Wrappers + 1 Loop +
  15 Primitives + 28 outside Build. The drop from the baseline's 51 is partly
  admission consolidation and is **not** evidence that three combinators closed.
- Lint: owned Build subtree **0 FAIL / 1 WARN** over 4 files. Full machine
  subtree **0 FAIL / 7 WARN** over 28 files; ClassNP **0 FAIL / 1 WARN** over
  10 files. Combined: 0 FAIL / 8 WARN over 38 distinct files. Seven are the
  inherited file-size warnings; the eighth is this owned file, addressed below.
- Freeze: five public signatures/order preserved, no public gains/losses,
  55 new private declarations, one source file changed, one textual admission.
- `git diff --check`, reverse patch application check, and `git bundle verify`
  all passed. The bundle advertises `fill/lib-L` and requires the recorded base.

Final sweep tail:

```text
MODULE 56/57 TCSlib/Complexity/CookLevin
MODULE 57/57 TCSlib/Complexity/ClassNP
SWEEP_PASS modules=57 elapsed_seconds=135.9
```

## Shared lemmas and escalations

Requested shared lemmas: **none**. No frozen statement was judged false or
changed; no statement-level escalation is asserted.

**Size exception for maintainer review:** the owned file is 1,466 lines. The
brief's exclusive ownership prevents moving these helpers into another file
within this batch, and the shared controller, supporting simulation lemmas,
and exact continuation interface form one construction. The continuation is
kept together so another agent can complete the existing frontier without
reconstructing its machine. Lint therefore has one documented new WARN; this
is not a claim that a maintainer already approved the size exception.

## Complete new-private-declaration inventory

All line numbers below refer to the supplied `Build/Loop.lean`.

| Declaration | Kind | Line | Admission status |
|---|---|---:|---|
| `loop_live_prefix` | lemma | 172 | No admission |
| `loop_silent_prefix` | lemma | 183 | No admission |
| `loop_first_halt` | lemma | 197 | No admission |
| `loop_orbit_inv` | lemma | 220 | No admission |
| `loop_fuel_width` | lemma | 230 | No admission |
| `loop_input_move_le` | lemma | 237 | No admission |
| `loop_input_run_le` | lemma | 251 | No admission |
| `loop_output_length_le` | lemma | 267 | No admission |
| `loop_rewind_bounded` | lemma | 284 | No admission |
| `loopDebit` | def | 316 | No admission |
| `loopBorrowPos` | def | 322 | No admission |
| `loopBorrowPos_le` | lemma | 327 | No admission |
| `loopDebit_length` | lemma | 333 | No admission |
| `loopValue` | def | 339 | No admission |
| `loopValue_bits` | lemma | 344 | No admission |
| `loopDebit_value` | lemma | 355 | No admission |
| `loopDebit_success` | lemma | 369 | No admission |
| `loopDebit_iterate_length` | lemma | 380 | No admission |
| `loopDebit_iterate_value` | lemma | 390 | No admission |
| `loopBuffer_read` | lemma | 404 | No admission |
| `loopBuffer_write` | lemma | 412 | No admission |
| `loopDebitTM` | def | 433 | No admission |
| `loopDebitCfg` | def | 449 | No admission |
| `loopBorrow_step` | lemma | 456 | No admission |
| `loopBorrow_run` | lemma | 482 | No admission |
| `loopBorrow_rewind` | lemma | 507 | No admission |
| `loopBorrow_correct` | lemma | 541 | No admission |
| `loopBodyTM` | def | 559 | No admission |
| `loopBodyCfg` | def | 582 | No admission |
| `loopBody_stop` | lemma | 594 | No admission |
| `loopBody_step` | lemma | 612 | No admission |
| `loopBody_run` | lemma | 659 | No admission |
| `loopBody_capture` | lemma | 687 | W1 only |
| `LoopHostState` | abbrev | 710 | No admission |
| `loopFuelSource` | def | 714 | No admission |
| `loopBodySource` | def | 722 | No admission |
| `loopControlAction` | def | 729 | No admission |
| `loopHost` | def | 753 | No admission |
| `loopHost_body_capture` | lemma | 830 | W1 only |
| `loopHost_fuel_capture` | lemma | 844 | W1 only |
| `loopHost_init` | lemma | 856 | No admission |
| `loopControl_idle` | lemma | 865 | No admission |
| `loopHost_input_rewind` | lemma | 873 | No admission |
| `loopFrame` | def | 890 | No admission |
| `loopWrite` | def | 910 | No admission |
| `loopControl_apply` | lemma | 917 | No admission |
| `loopReplayTM` | def | 953 | No admission |
| `loopReplayCfg` | def | 963 | No admission |
| `loopReplay_step` | lemma | 969 | No admission |
| `loopReplay_run` | lemma | 993 | No admission |
| `loopControl_payload` | lemma | 1009 | No admission |
| `loopHost_replay` | lemma | 1029 | No admission |
| `loopHost_contracts` | lemma | 1083 | **OPEN construction** |
| `loop_halted_run` | lemma | 1217 | No admission |
| `loop_find_run` | lemma | 1351 | No admission |

## Delivery and integration

- Full source: `TCSlib/Complexity/TuringMachine/Build/Loop.lean`.
- One-commit `git format-patch` series: `patches/`.
- Delta bundle: `fill-lib-L.bundle`, requiring base `e346139ccc9e3141908f7414bf27f74d8759c9be`.
- Continuation instructions and exact admitted declaration: `CONTINUATION.md`.
- Required logs: `logs/final-sweep.log`, `logs/axioms.log`; lint, freeze, and
  bundle verification logs are included too.
- Reproducible audit programs and machine-readable summaries: `verification/`.
- Checksums: `SHA256SUMS`, covering every other file in the archive.

Apply the patch with `git am -3` on a checkout descended from the required
campaign branch, preserving unrelated concurrent W/P work. Treat this as a
checkpoint, not an acceptance-ready fill. Recheck the frozen statements and
rerun the committed 57-module sweep and axiom traversal after integration.


## ===== audits/ch1-lib-agent-reports/batchL-continuation.md =====

# Continue machine-library batch L

**Partial checkpoint, not a closed batch.** Read the committed
`briefs/lib-fill-batchL.md` on `complexity/arora-barak-ch1` first. Its statement
freeze, ownership, construction route, and verification rules remain binding.

Base: `e346139ccc9e3141908f7414bf27f74d8759c9be`.
Checkpoint: `769341f5bd042f5790f7a24fdfe9e439b32ff666`.
Only owned file: `TCSlib/Complexity/TuringMachine/Build/Loop.lean`.

The public target bodies are present, but the three combinators remain
conditional on the single private admission below. `loop_run`, both terminal
summation lemmas, and all non-capture helpers are admission-free. The three
capture helpers use only the sanctioned `Turing.capture_run` root. Preserve
all five original public declarations and existing docstrings.

## Exact remaining admitted declaration

```lean
private lemma loopHost_contracts (body F : FinTM Bool) (anchor : body.State)
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
      ∃ (cfg : ℕ → Cfg (loopHost body F anchor findMode).k Bool
          (loopHost body F anchor findMode).State x) (startup : ℕ),
        startup ≤ c * (T x.length + 1) ∧
        (loopHost body F anchor findMode).tm.runFrom
          ((loopHost body F anchor findMode).tm.initCfg x) startup = cfg 0 ∧
        (∀ i ≤ R x.length, (cfg i).output = []) ∧
        (cfg (R x.length + 1)).state = none ∧
        (cfg (R x.length + 1)).output = (if findMode then [] else [false]) ∧
        (∀ i ≤ R x.length, ∃ t ≤ c * (T x.length + 1),
          if acceptF x ((stepF x)^[i] (s0 x)) then
            ((loopHost body F anchor findMode).tm.runFrom (cfg i) t).state = none ∧
            ((loopHost body F anchor findMode).tm.runFrom (cfg i) t).output =
              (if findMode then out x ((stepF x)^[i] (s0 x)) else [true])
          else (loopHost body F anchor findMode).tm.runFrom (cfg i) t = cfg (i + 1)) := by
  -- Continuation frontier: the controller is defined, but its phase assembly,
  -- canonical seam family, and uniform time ledger still require proof.
  sorry
```

This is an unproved **concrete-machine** contract. Neither the fact that the
controller typechecks nor the abstract summation lemmas discharge it. Do not
replace it by an untimed computability result or by another out-of-scope
admitted theorem. The two output modes deliberately share the same finite
controller: false gives fixed verdicts; true replays the full first payload.

## Controller and tape layout

The first `body.k` tapes are the body's work tapes. Tape `body.k` is the
one-cell stop-kind flag. Tape `body.k + 1` is the fixed-width counter. The
next `F.k` tapes hold fuel-machine work and are preserved after fuel. The
last tape, `body.k + 1 + (1 + F.k)`, captures fuel and then body output.
The fuel setup copies its captured bits into the counter while clearing the
capture tape; both heads are then rewound together.

The state space has distinct fuel states, body states tagged startup/active,
and `Fin 14` controller phases. `loopBodyTM` has an additional release bit:
true forces one source action; every successor clears it. An unreleased
anchor stops silently with flag `some false`; a genuine source halt sets
flag `some true` while retaining every source emission. This also distinguishes
acceptance with an empty payload from exhaustion.

| Phase | Transition responsibility | Existing proof |
|---|---|---|
| 0, 1 | Mandatory left move and rewind captured fuel to its origin | Pending |
| 2 | Copy fuel to counter while clearing the capture tape | Pending |
| 3 | Rewind counter and capture heads together under the counter word | Pending |
| 4, 5 | Rewind native input and dispatch to body startup | `loopHost_input_rewind` |
| 6 | Clear startup's false stop flag; release initial anchor for free | Pending |
| 7 | Read stop kind; accept or clear flag and debit | Pending |
| 8 | Fixed-width binary borrow | Standalone `loopBorrow_*`; host lifting pending |
| 9 | Successful borrow rewind; release next body seam | Standalone rewind; host lifting pending |
| 10 | Underflow rewind | Standalone rewind; host lifting pending |
| 11 | Emit false (decision) or nothing (find), and halt | Pending one-step assembly |
| 12 | Rewind the captured accepting payload | Pending |
| 13 | Emit captured payload verbatim and halt at the right blank | `loopHost_replay` |

## Recommended next proof obligations

1. **Relocations and fuel setup.** Use `rightCfg_run` twice to relate
   `loopFuelSource` to `F`, retaining initially blank body/flag/counter tapes.
   Choose the first fuel halt with `loop_first_halt`, use `loopHost_init` and
   `loopHost_fuel_capture`, then prove phases 0–3 with their exact scan lengths.
   `loopFrame`/`loopControl_apply` isolate the active track operations. Combine
   `loop_input_run_le` and the checked phase-4/5 rewind to preserve a budget
   in the fuel run's time, even when that time is sublinear in input length.
2. **Startup return and active body calls.** Lift `loopBodyTM` through
   `loopBodySource` using `leftCfg_run`, with arbitrary counter/fuel residue.
   Use the checked `loopBody_run` and actual-host `loopHost_body_capture`.
   Startup's no-anchor guard includes time zero; active rounds use release
   true and the strict-interior guard. Rejecting endpoints imply no prior
   halt or output (`loop_live_prefix`, `loop_silent_prefix`). For acceptance,
   replace a padded endpoint by its first halt before applying W1.
3. **Host counter lifting.** Prove that actual phases 8–10 implement the
   standalone decrement, preserving every non-counter track and native
   input position. The exact standalone cost is `2 * loopBorrowPos u + 2`,
   bounded by `2 * u.length + 2`. Phase 11's final emission is an additional
   part of the last rejecting segment, not a separate unbudgeted round.
4. **Acceptance completion.** Prove flag dispatch and the payload rewind
   before applying `loopHost_replay`. `loop_output_length_le` charges the
   payload length to the original body round because its starting output is
   empty. Fixed-verdict mode takes its one final emission directly.
5. **Canonical configuration family.** At candidate index `i`, use the
   original body's `Cfg.ofWords anchor (stateWord body.k ...)`, host active
   release state, blank stop flag and capture tape, and counter word
   `((fun w => (loopDebit w).1)^[i] (Nat.bits (R x.length)))`. Its width and
   value at `i ≤ R x.length` are already proved. Retain the completed fuel
   work tapes and their heads. Thread `loop_orbit_inv` before every body call.
6. **Terminal choice and budget.** At the last rejecting candidate, use the
   actual underflow-plus-emission endpoint for the halted terminal. If that
   candidate accepts, use any halted terminal with the required false/empty
   output. Prove local contracts even for seams unreachable after an earlier
   acceptance. Include `R = 0` and empty binary fuel explicitly. Sum the
   proved startup/body/counter/dispatch constants and use the audit's single
   maximum constant. No completed uniform bound is claimed in this checkpoint.

The corollary proofs should then close without additional construction work.
Do not use frozen `loop_run` directly for the `[false]` terminal;
`loop_halted_run` is the checked lemma for that case. `loop_find_run` already
proves the exact `List.range.find?` output, including an empty selected payload.

## Reproduction and closure

The ZIP contains the one-file patch and prerequisite-based bundle; integrate
without overwriting concurrent W/P changes. Use Lean 4.25.0 and the committed
mathlib pin. Never invoke `lake build`.

From the repository root, with the pinned `lean` on `PATH`, set
`TCSLIB_OLEANS` to a new writable directory and run the included
`verification/sweep.py` (or the committed shell-script loop). Run
`verification/run_axioms.py` with the same variable. The scripts take the
repository from the working directory, or `TCSLIB_REPO` if provided.

At this checkpoint, `verification/Axioms.lean` explicitly expects the private
construction root. After filling it, change the expectations for all three
combinators and for `loopHost_contracts` to the actual sanctioned W1-only root
(or none, once W1 is merged and proved). Once W1 itself is proved, also change the three capture-helper expectations
to empty. Keep every other closed-helper expectation empty. Re-run a fresh full 57-module sweep, all root checks, lint, statement
freeze, and checksum generation. The current 1,466-line file size needs the
recorded ownership justification, or a separately authorized refactor after
this batch; do not move code out of the owned file during the continuation.


## ===== audits/ch1-lib-agent-reports/batchL2.md =====

# Batch L2 — completed loop-controller fill

**Complete.** `Turing.FinTM.loopHost_contracts` is proved. The owned file has
zero `sorry` tokens. All four public loop theorems are admission-free, as are
all 95 private helpers. No continuation frontier remains.

## Provenance and scope

- Repository: https://github.com/Shilun-Allan-Li/tcslib
- Required campaign branch: `complexity/arora-barak-ch1`, explicitly cloned with `--single-branch --branch`.
- Required base: `90273dd6dea2f9e092ca7d4b5ab5dc72c96ef1ee`.
- Brief read from campaign tip `646b9ee6b482867cb588a67f3014dcc00ebac7d5`; its required base was then selected.
- Local working branch, as prescribed by the brief: `fill/lib-L2`.
- Completion commit: `2f40ca5fde2a71770fdd943c81ff337f34e6cd1d`.
- Execution: `lib-L2-20261003T213754Z`.
- Only changed tracked file: `TCSlib/Complexity/TuringMachine/Build/Loop.lean`.
- No push or PR; no other branch was modified. Delivery is this ZIP.

Read and followed: the L2 brief, original L brief, predecessor continuation
and report ledger, workflow §§4/6, policy, W environment protocol, epoch-1
pitfalls, and the audited construction ledger. The predecessor's ordered
obligations were worked in order; no machine definition or existing signature
was changed. The extra verification files live only in this delivery directory.

## Six obligations and construction ledger

| Obligation | Discharging declarations and result |
| --- | --- |
| 1. Relocations and fuel setup, phases 0–3 | `loopFuel_run` uses `rightCfg_run` twice; `loopFuel_init` identifies the genuine start. `loopHost_fuel_rewind`, `loopHost_fuel_copy`, `loopHost_fuel_return`, and `loopHost_fuel_setup` prove exact setup scans. `loopHost_prepare` chooses the first fuel halt, uses the actual-host capture helper, retains fuel residue, and connects the checked input rewind to the source displacement bound. |
| 2. Startup return and active body calls | `loopBodySource_run` uses `leftCfg_run`. `loopHost_anchor_return` supplies the silent false-flag stop; `loopReady_call`, `loopHost_release`, and `loopHost_start` assemble startup. `loopHost_halt_return` captures the first genuine halt and its full emission. Startup uses the no-anchor guard including time zero; active calls use the release bit and strict-interior guard. |
| 3. Counter lifting, phases 8–10 | `loopHost_borrow_step`, `loopHost_borrow_run`, `loopHost_borrow_rewind`, and `loopHost_borrow` prove the counter operation in the actual host against arbitrary preserved residue. `loopHost_reject` clears the flag and includes phase 11's exhaustion emission in the rejecting segment. The bound is worst-case width, never amortization. |
| 4. Acceptance completion, phases 7/12/13 | `loopHost_payload_rewind` proves phase 12. `loopHost_frame_replay` applies the existing `loopHost_replay`. `loopHost_accept` dispatches by the true flag independently of payload length; `loopHost_round` charges output length to elapsed body time via `loop_output_length_le`. |
| 5. Canonical configuration family | Inside `loopHost_contracts`, `words` is the debit iterate of the initial binary fuel and `orbit` is the body-state iterate. `candidate` uses `Cfg.ofWords` and `loopCall` with blank flag/capture, released active control, and the same completed fuel residue. The existing width/value lemmas and `loop_orbit_inv` supply each local round contract, including unreachable seams after earlier acceptance. |
| 6. Terminal and single constant | The main proof fixes one time witness per candidate. For a rejecting last candidate, `terminal` is its actual completed underflow/emission endpoint. For an accepting last candidate, it is an arbitrary halted configuration with the required false/empty output. `cfg` selects candidates up to the fuel value and that terminal afterwards. `loopHost_bound = max 1 (max 9 (3 + 2 + 5)) = 10` is the single exported coefficient. |

The 14-phase table is fully discharged: phases 0/1 by fuel setup/rewind;
2 by fuel copy; 3 by fuel return; 4/5 by the inherited input rewind inside
`loopHost_prepare`; 6 by release/start; 7 by reject/accept; 8 by borrow
step/run; 9/10 by borrow rewind; 11 by reject; 12 by payload rewind; and
13 by frame replay through the inherited actual-host replay lemma.

All construction helpers have empty admission-root sets. The body-capture
and fuel-capture helpers now depend on the integrated, proved `Turing.capture_run`.
The existing corollary proofs were left unchanged: `loop_halted_run` handles
the decision terminal, and `loop_find_run` supplies the exact first payload.
No application of frozen `loop_run` to a `[false]` terminal was introduced.

## Checked time ledger

The following calculations are formalized in the indicated lemmas. Each body
round duration is at most `T x.length`, and every retained counter width is
at most `T x.length`.

| Component | Bound |
| --- | --- |
| Fuel rewind/copy/return, including the first left move | `1 + (word.length + 1) + (word.length + 1) + (word.length + 1) = 3 * word.length + 4` |
| Input rewind after fuel | At most `fuel.inputPos.val + 2`, and the source input position is at most `1 + firstHaltTime`. |
| Prepared startup | `firstHaltTime + 3 * fuel.output.length + 4 + rewindTime ≤ 5 * T x.length + 7` |
| Body startup and release | `btime + 2 ≤ T x.length + 2` |
| Complete startup | `(5 * T x.length + 7) + (T x.length + 2) = 6 * T x.length + 9 ≤ 9 * (T x.length + 1)` |
| Counter, including underflow rewind | `2 * loopBorrowPos word + 2 ≤ 2 * word.length + 2` |
| Rejecting return dispatch, counter, and possible final emission | At most `2 * word.length + 4` |
| Accepting return dispatch/replay | At most `2 * c.output.length + 3`, including an empty payload |
| Entire local body/controller segment | At most `3 * t + 2 * word.length + 5`, hence at most the audit ledger's `(3 + 2 + 5) * (T x.length + 1)` |

The maximum of one, startup coefficient nine, and segment coefficient ten
is ten. The proof includes zero fuel and width zero through the same formulas:
startup performs no debit, so candidate zero is tested before the first underflow.

## Freeze and admissions

`verification/freeze.py` verifies:

- All 60 pre-existing declaration signatures and their order are unchanged,
  including the private `loopHost_contracts` interface.
- All five public declarations are preserved, with no public gains or losses.
- All 17 pre-existing definitions/abbreviations, including the controller,
  are unchanged after comment stripping and whitespace normalization.
- All 60 pre-existing declaration docstrings remain verbatim.
- The module docstring has only an appended completion paragraph; a separate
  ordinary comment marks the old private continuation docstring as historical.
- Forty new declarations are private; no import was added.
- Only the owned source differs from the required base, and it has zero admissions.

The updated `verification/Axioms.lean` sets **every** expected root set to
empty, including the three combinators, `loopHost_contracts`, and the three
capture helpers. It checks the four public loop targets, all 95 private
helpers, and `Turing.capture_run`: **100 checks**. The kernel walk traverses
both types and values, including opaque values and constructor dependencies.
Every axiom list is required to be a subset of the standard triple.

```text
'Turing.loop_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.exists_loopCfgTM' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.exists_loopTM' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.exists_loopFindTM' depends on axioms: [propext, Classical.choice, Quot.sound]
CLOSURE_AUDIT_PASS declarations=100; every checked declaration has empty admission roots and only standard axioms.
```

## Verification and environment

- Lean 4.25.0, release commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`.
- Mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`; committed manifest unchanged.
- `lake exe cache get` was invoked once; the launcher failed before cache
  processing. Reused the available pinned dependency/cache tree after checking
  all 11 materialized package revisions against the manifest. Four packages
  for documentation generation were not materialized and are not needed by
  the required module sweep. No `lake build` was invoked.
- This runner's PID namespace/procfs mismatch blocked Lean's executable-path
  lookup. The small `verification/self-exe.c` compatibility shim redirects only
  its own `/proc/<pid>/exe` lookup to `/proc/self/exe`. The pinned Lean executable,
  libraries, proof checker, and kernel are unmodified. Setup details are recorded
  in `verification/environment.json`; reproduction instructions disclose the shim.
- Bootstrap: all 57 modules passed. Iteration used the owned module; final
  verification includes every subsequent module in the committed order.
- **Final full fresh sweep:** 57/57, 57 fresh nonempty oleans, zero `error:`
  lines, exit zero. The final output tree was new. A preceding complete sweep
  was repeated after the two trailing-space cleanups so the shipped bytes are
  exactly the verified source.
- Final declaration-admission warnings: **32**, all outside the owned file
  (4 pending primitives and 28 campaign admissions). Bootstrap had
  **33**. No out-of-scope admission was edited or used by a checked loop declaration.
- Lint: Build subtree 0 FAIL / 2 WARN over 4 files. Full TuringMachine subtree
  0 FAIL / 8 WARN over 28 files; ClassNP 0 FAIL / 1 WARN over 10 files.
  Combined, without counting the Build subset twice: 0 FAIL / 9 WARN over
  38 distinct files. These are file-size warnings; the owned file is addressed below.
- `git diff --check`, reverse patch application check, and `git bundle verify` pass.

Final sweep tail:

```text
MODULE 56/57 TCSlib/Complexity/CookLevin
MODULE 57/57 TCSlib/Complexity/ClassNP
SWEEP_PASS modules=57 elapsed_seconds=157.9
```

## Shared lemmas, escalations, and file size

Requested shared lemmas: **none**. Statement-level escalations: **none**.
The construction is complete; no remaining admitted private or continuation
work is being passed to another agent.

The owned file is **2,693 lines**, up from the recorded 1,466-line checkpoint.
The brief requires this construction to remain in the owned file and forbids
moving it elsewhere. The forty private helpers supply the previously missing
actual-host phase proofs and their assembly, so the inherited size exception
is retained and its final size is explicitly reported for the maintainer's
records. No authorization for a separate refactor is presumed.

## Complete new-private inventory

All names are in `Turing.FinTM`. Line numbers refer to the delivered source.
Every entry is admission-free.

| Declaration | Kind | Line |
| --- | --- | ---: |
| `loopFuelCfg` | def | 1075 |
| `loopFuel_run` | lemma | 1084 |
| `loopFuel_init` | lemma | 1097 |
| `loopFrame_payload` | lemma | 1114 |
| `loopFrame_counter` | lemma | 1124 |
| `loopHost_fuel_rewind` | lemma | 1136 |
| `loopCopyTape` | def | 1186 |
| `loopCopy_read` | lemma | 1190 |
| `loopCopy_erase` | lemma | 1195 |
| `loopCopy_initial` | lemma | 1208 |
| `loopCopy_final` | lemma | 1216 |
| `loopHost_fuel_copy` | lemma | 1230 |
| `loopHost_fuel_return` | lemma | 1281 |
| `loopHost_fuel_setup` | lemma | 1336 |
| `loopFuelCaptured` | def | 1367 |
| `loopReady` | def | 1374 |
| `loopFuelCaptured_frame` | lemma | 1386 |
| `loopHost_prepare` | lemma | 1445 |
| `loopBodyPadded` | def | 1485 |
| `loopCall` | def | 1495 |
| `loopBodySource_run` | lemma | 1505 |
| `loopHost_anchor_return` | lemma | 1520 |
| `loopReady_call` | lemma | 1561 |
| `loopHost_release` | lemma | 1600 |
| `loopHost_start` | lemma | 1631 |
| `loopHost_halt_return` | lemma | 1651 |
| `loopCall_frame` | lemma | 1678 |
| `loopCall_reframe` | lemma | 1705 |
| `loopHost_borrow_step` | lemma | 1737 |
| `loopHost_borrow_run` | lemma | 1775 |
| `loopHost_borrow_rewind` | lemma | 1808 |
| `loopHost_borrow` | lemma | 1858 |
| `loopFrame_flag` | lemma | 1880 |
| `loopFlag_clear` | lemma | 1889 |
| `loopHost_reject` | lemma | 1900 |
| `loopHost_payload_rewind` | lemma | 1972 |
| `loopHost_frame_replay` | lemma | 2025 |
| `loopHost_accept` | lemma | 2060 |
| `loopHost_round` | lemma | 2126 |
| `loopHost_bound` | def | 2189 |

## Delivery and integration

- Full source at the original repository-relative path.
- One-commit `git format-patch` series in `patches/`.
- `fill-lib-L2.bundle`, advertising only `fill/lib-L2` and requiring the recorded base.
- Final and bootstrap sweep logs, axiom/root log, lint, freeze, bundle and patch checks in `logs/`.
- Reproducible checks, the governing continuation brief, and machine-readable
  environment/results/freeze records in `verification/`.
- `SHA256SUMS` covers every other file in the archive.

Apply the patch with `git am -3` to a checkout descended from the required
campaign branch, preserving concurrent P2 changes. The bundle provides the
same single commit. Re-run the campaign integration checks as usual; this ZIP
is a completed fill, not a continuation checkpoint.

**Notation.** Code-font identifiers denote the Lean declarations or local
variables in the delivered source. `word.length` is the counter width;
`c.output.length` is the captured payload length; `t` is a source round's
positive duration. `firstHaltTime` and `rewindTime` in the time table describe
the witnesses named `u` and `v` in `loopHost_prepare`.


## ===== audits/programs/ch1-libfill-ClosureAxioms.lean =====

import TCSlib.Complexity.TuringMachine
import TCSlib.Complexity.ClassNP
import Lean

set_option maxHeartbeats 0

-- Maintainer axiom attestation: library-fill checkpoint integration (W+P+L).
-- Expected state: W complete (4/4 clean); P 11/15 clean with 4 pending at their
-- own roots; L's loop_run clean and the three combinators rooted solely at the
-- admitted private loopHost_contracts; headline and campaign regressions
-- unchanged.

open Lean Elab Command

namespace LibFillAudit

structure WalkState where
  visited : NameSet := {}
  roots : Array Name := #[]

abbrev WalkM := ReaderT Environment (StateM WalkState)

partial def visit (name : Name) : WalkM Unit := do
  if (← get).visited.contains name then return
  modify fun s => { s with visited := s.visited.insert name }
  let env ← read
  match env.checked.get.find? name with
  | none => panic! s!"Missing checked kernel declaration: {name}"
  | some ci =>
    let mut deps := ci.type.getUsedConstants
    if let some value := ci.value? (allowOpaque := true) then
      deps := deps ++ value.getUsedConstants
    if deps.contains ``sorryAx then
      modify fun s => { s with roots := s.roots.push name }
    deps.forM visit
    match ci with
    | .inductInfo i => i.ctors.forM visit
    | _ => pure ()

def roots (env : Environment) (name : Name) : Array Name :=
  (((visit name).run env).run {}).2.roots

def allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

def userRoots (env : Environment) (name : Name) : List Name :=
  ((roots env name).map privateToUserName).toList.eraseDups.mergeSort
    (fun a b => a.toString ≤ b.toString)

def hostC : Name := `Turing.FinTM.loopHost_contracts

run_cmd do
  let env ← getEnv
  let expectations : Array (Name × List Name) := #[
    -- W: complete, clean.
    (``Turing.capture_run, []),
    (``Turing.FinTM.redirectTM_computes, []),
    (``Turing.FinTM.redirectTM_live, []),
    (``Turing.FinTM.computesFunInTime_cond, []),
    -- L: complete after L2 - every loop theorem admission-free.
    (``Turing.loop_run, []),
    (``Turing.FinTM.exists_loopCfgTM, []),
    (``Turing.FinTM.exists_loopTM, []),
    (``Turing.FinTM.exists_loopFindTM, []),
    -- P: the eleven filled targets, clean.
    (``Turing.FinTM.computesFunInTime_prepend, []),
    (``Turing.FinTM.computesFunInTime_pairEncodeFixed, []),
    (``Turing.FinTM.computesFunInTime_pairDup, []),
    (``Turing.FinTM.computesFunInTime_incFixed, []),
    (``Turing.FinTM.computesFunInTime_pairValid, []),
    (``Turing.FinTM.computesFunInTime_pairFst, []),
    (``Turing.FinTM.computesFunInTime_pairSnd, []),
    (``Turing.FinTM.computesFunInTime_pairConcat, []),
    (``Turing.FinTM.computesFunInTime_lengthBits, []),
    (``Turing.FinTM.computesFunInTime_polyUnary, []),
    (``Turing.FinTM.computesFunInTime_polyBits, []),
    -- P: targets 12-13 now filled and clean.
    (``Turing.FinTM.computesFunInTime_pairLenCheck, []),
    (``Turing.FinTM.computesFunInTime_stripLast, []),
    (``Turing.FinTM.computesFunInTime_pairMapSnd, []),
    (``Turing.FinTM.computesFunInTime_splitSolve, []),
    -- Headline and campaign regressions.
    (``Turing.timed_universal, []),
    (``Turing.timed_universal_concrete, []),
    (``Complexity.timed_universal_quantitative, []),
    (``Complexity.NP_subset_EXP, [`Complexity.enumMachine_contracts]),
    (``Complexity.TMSAT_mem_NP, [``Complexity.TMSAT_mem_NP])]
  for (name, expectedRaw) in expectations do
    let expected := expectedRaw.eraseDups.mergeSort (fun a b => a.toString ≤ b.toString)
    let found := userRoots env name
    logInfo m!"ROOTS {name}: {found}"
    unless found == expected do
      throwError "Unexpected admission roots for {name}: {found}; expected {expected}"
    let ax ← collectAxioms name
    unless ax.all (fun a => allowed.contains a || a == ``sorryAx) do
      throwError "Unexpected axiom for {name}: {ax}"
    if expected.isEmpty && ax.contains ``sorryAx then
      throwError "Unexpected sorryAx for {name}"
    unless expected.isEmpty || ax.contains ``sorryAx do
      throwError "Expected sorryAx for {name} but it is absent"
  logInfo "LIBRARY CLOSURE AUDIT PASS: all 23 contracts admission-free; the Build tree carries zero admissions; headline and campaign regressions unchanged." -- : W complete and clean; P's eleven fills clean with four pending at their own roots; L's combinators rooted solely at loopHost_contracts; headline and campaign regressions unchanged."

end LibFillAudit


## ===== audits/logs/ch1-libfill4-sweep.log =====

P4 closure integration: full fresh sweep
HEAD: c013f270402ec5babaf33f94d3c15c3ca2589239
START_UTC: 2026-10-04T14:25:51Z
=== 1/57 TCSlib/Complexity/TuringMachine/Configuration
TCSlib/Complexity/TuringMachine/Configuration.lean:137:17: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Configuration.lean:140:61: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/TuringMachine/Configuration.lean:155:17: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
=== 2/57 TCSlib/Complexity/TuringMachine/Deterministic
=== 3/57 TCSlib/Complexity/TuringMachine/StateRenaming
=== 4/57 TCSlib/Complexity/TuringMachine/Finite
=== 5/57 TCSlib/Complexity/TuringMachine/Oracle
=== 6/57 TCSlib/Complexity/TuringMachine/Simulation
=== 7/57 TCSlib/Complexity/TuringMachine/Sweep
=== 8/57 TCSlib/Complexity/TuringMachine/Composition
=== 9/57 TCSlib/Complexity/TuringMachine/Build/Convention
=== 10/57 TCSlib/Complexity/TuringMachine/Build/Wrappers
=== 11/57 TCSlib/Complexity/TuringMachine/Build/Loop
=== 12/57 TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction
=== 13/57 TCSlib/Complexity/TuringMachine/Robustness/SingleTape
=== 14/57 TCSlib/Complexity/TuringMachine/Robustness/Bidirectional
=== 15/57 TCSlib/Complexity/ClassP/DTIME
=== 16/57 TCSlib/Complexity/ClassP/TimeConstructible
=== 17/57 TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule
=== 18/57 TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:473:6: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:501:37: warning: This simp argument is unused:
  hl

Hint: Omit it from the simp argument list.
  simp [inputTag, clippedMove, hl̵,̵ ̵h̵r]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:533:45: warning: This simp argument is unused:
  hw

Hint: Omit it from the simp argument list.
  simp [h̵w̵,̵ ̵Cfg.workTapeSymbols]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:535:49: warning: This simp argument is unused:
  hw

Hint: Omit it from the simp argument list.
  simp [hz, h̵w̵,̵ ̵Function.update_of_ne hn]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:535:53: warning: This simp argument is unused:
  Function.update_of_ne hn

Hint: Omit it from the simp argument list.
  simp [hz, hw,̵ ̵F̵u̵n̵c̵t̵i̵o̵n̵.̵u̵p̵d̵a̵t̵e̵_̵o̵f̵_̵n̵e̵ ̵h̵n̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:614:44: warning: This simp argument is unused:
  List.append_nil

Hint: Omit it from the simp argument list.
  simp only [payloadZone, List.reverse_cons, FinTM.sweepFold_append, he, ih, FinTM.sweepFold,
  ̲  ̲ ̲ ̲ ̲ ̲p̵a̵y̵l̵o̵a̵d̵B̵a̵c̵k̵w̵a̵r̵d̵_̵r̵o̵w̵,̵ ̵L̵i̵s̵t̵.̵a̵p̵p̵e̵n̵d̵_̵n̵i̵l̵]̵p̲a̲y̲l̲o̲a̲d̲B̲a̲c̲k̲w̲a̲r̲d̲_̲r̲o̲w̲]̲

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:764:27: warning: This simp argument is unused:
  act

Hint: Omit it from the simp argument list.
  simp only [a̵c̵t̵,̵ ̵Option.map_none]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:768:21: warning: This simp argument is unused:
  act

Hint: Omit it from the simp argument list.
  simp only [a̵c̵t̵,̵ ̵Option.map_some, Function.update_self]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:769:21: warning: This simp argument is unused:
  act

Hint: Omit it from the simp argument list.
  simp only [a̵c̵t̵,̵ ̵Option.map_some, Function.update_of_ne hz]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:774:29: warning: This simp argument is unused:
  act

Hint: Omit it from the simp argument list.
  simp only [a̵c̵t̵,̵ ̵Option.toList_none, List.append_nil]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:776:21: warning: This simp argument is unused:
  act

Hint: Omit it from the simp argument list.
  simp only [a̵c̵t̵,̵ ̵Option.toList_some, clockTape_append]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:784:65: warning: This simp argument is unused:
  ho

Hint: Omit it from the simp argument list.
  simp [act, List.length_append,̵ ̵h̵o̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:784:73: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:784:73: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:881:25: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
=== 19/57 TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:191:25: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:217:4: warning: This simp argument is unused:
  SignType.coe_neg_one

Hint: Omit it from the simp argument list.
  simp only [setupWrite, moveInputPos_zero, SignType.coe_zero, add_zero, S̵i̵g̵n̵T̵y̵p̵e̵.̵c̵o̵e̵_̵n̵e̵g̵_̵o̵n̵e̵,̵ ̵zero_add]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:249:56: warning: This simp argument is unused:
  SignType.coe_one

Hint: Omit it from the simp argument list.
  simp only [setupWrite, SignType.coe_zero, add_zero, S̵i̵g̵n̵T̵y̵p̵e̵.̵c̵o̵e̵_̵o̵n̵e̵,̵ ̵copyGuide_next]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:313:64: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:313:23: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:313:35: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:313:64: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:405:16: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:405:41: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:405:16: warning: 'simp [SignType.cast]' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:405:41: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:600:25: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:686:26: warning: This simp argument is unused:
  hg

Hint: Omit it from the simp argument list.
  simp_all ̵[̵h̵g̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:731:38: warning: This simp argument is unused:
  layoutPhase

Hint: Omit it from the simp argument list.
  simp [layoutP̵h̵a̵s̵e̵,̵ ̵l̵a̵y̵o̵u̵t̵Move, hi]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:747:36: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:747:48: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:756:32: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:778:15: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only [F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵,̵ ̵Nat.cast_add, Nat.cast_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:778:27: warning: This simp argument is unused:
  Nat.cast_add

Hint: Omit it from the simp argument list.
  simp only [Fin.val_mk, Nat.cast_a̵d̵d̵,̵ ̵N̵a̵t̵.̵c̵a̵s̵t̵_̵one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:778:41: warning: This simp argument is unused:
  Nat.cast_one

Hint: Omit it from the simp argument list.
  simp only [Fin.val_mk, Nat.cast_add,̵ ̵N̵a̵t̵.̵c̵a̵s̵t̵_̵o̵n̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:879:17: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only [F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵,̵ ̵Nat.cast_add, Nat.cast_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:879:29: warning: This simp argument is unused:
  Nat.cast_add

Hint: Omit it from the simp argument list.
  simp only [Fin.val_mk, Nat.cast_a̵d̵d̵,̵ ̵N̵a̵t̵.̵c̵a̵s̵t̵_̵one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:879:43: warning: This simp argument is unused:
  Nat.cast_one

Hint: Omit it from the simp argument list.
  simp only [Fin.val_mk, Nat.cast_add,̵ ̵N̵a̵t̵.̵c̵a̵s̵t̵_̵o̵n̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
=== 20/57 TCSlib/Complexity/TuringMachine/Robustness/ObliviousLedger
=== 21/57 TCSlib/Complexity/TuringMachine/Robustness/Oblivious
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:182:25: warning: This simp argument is unused:
  hc

Hint: Omit it from the simp argument list.
  simp only [hfirst,̵ ̵h̵c̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:240:19: warning: This simp argument is unused:
  hd

Hint: Omit it from the simp argument list.
  simp only [h̵d̵,̵ ̵SignType.cast, add_zero, ← sub_eq_add_neg, hleft', hc]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:379:26: warning: This simp argument is unused:
  hw

Hint: Omit it from the simp argument list.
  simp [setupWrite, h̵w̵,̵ ̵Function.update_of_ne hz, h, hz]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:379:30: warning: This simp argument is unused:
  Function.update_of_ne hz

Hint: Omit it from the simp argument list.
  simp [setupWrite, hw, F̵u̵n̵c̵t̵i̵o̵n̵.̵u̵p̵d̵a̵t̵e̵_̵o̵f̵_̵n̵e̵ ̵h̵z̵,̵ ̵h, hz]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:737:38: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:743:6: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:756:24: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:756:24: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:695:64: warning: This simp argument is unused:
  Fin.reduceFinMk

Hint: Omit it from the simp argument list.
  simp only [prepInvariant, Action.apply, Fin.addCases_right, Fin.r̵e̵d̵u̵c̵e̵F̵i̵n̵M̵k̵,̵ ̵F̵i̵n̵.̵val_one, Nat.one_ne_zero,
  ̲  ̲ ̲ ̲ ̲ ̲show (2 : ℕ) ≠ 0 by decide, ↓reduceIte,
  ̵  ̵ ̵ ̵ ̵ ̵SignType.coe_zero, add_zero]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:695:111: warning: This simp argument is unused:
  show (2 : ℕ) ≠ 0 by decide

Hint: Omit it from the simp argument list.
  simp only [prepInvariant, Action.apply, Fin.addCases_right, Fin.reduceFinMk, Fin.val_one,
  ̲  ̲ ̲ ̲ ̲ ̲Nat.one_ne_zero, s̵h̵o̵w̵ ̵(̵2̵ ̵:̵ ̵ℕ̵)̵ ̵≠̵ ̵0̵ ̵b̵y̵ ̵d̵e̵c̵i̵d̵e̵,̵ ̵↓reduceIte, SignType.coe_zero, add_zero]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:725:52: warning: This simp argument is unused:
  hi

Hint: Omit it from the simp argument list.
  simp only [obliviousSchedule, obliviousVisit, h̵i̵,̵ ̵setupWrite, Option.toList_none, List.append_nil]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:729:52: warning: This simp argument is unused:
  hi

Hint: Omit it from the simp argument list.
  simp only [obliviousSchedule, obliviousVisit, h̵i̵,̵ ̵setupWrite, Option.toList_none, List.append_nil]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
=== 22/57 TCSlib/Complexity/ClassP/P
=== 23/57 TCSlib/Complexity/ClassP/ModelInvariance
=== 24/57 TCSlib/Complexity/ClassP/Examples
=== 25/57 TCSlib/Complexity/TuringMachine/Encoding
=== 26/57 TCSlib/Complexity/TuringMachine/Build/Primitives
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2491:42: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2497:72: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2491:42: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2497:72: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2489:82: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2519:72: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2519:72: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2507:38: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2511:38: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2569:29: warning: This simp argument is unused:
  List.append_nil

Hint: Omit it from the simp argument list.
  simp only [↓reduceIte,̵ ̵L̵i̵s̵t̵.̵a̵p̵p̵e̵n̵d̵_̵n̵i̵l̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2532:42: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2537:42: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2540:42: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2579:46: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2603:43: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2926:25: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2926:25: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3025:59: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3173:34: warning: This simp argument is unused:
  splitRestoreScan

Hint: Omit it from the simp argument list.
  simp [Action.apply,̵ ̵s̵p̵l̵i̵t̵R̵e̵s̵t̵o̵r̵e̵S̵c̵a̵n̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3203:79: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3203:79: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3266:6: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3311:52: warning: This simp argument is unused:
  Nat.cast_one

Hint: Omit it from the simp argument list.
  simp only [List.length_nil, Nat.zero_add, N̵a̵t̵.̵c̵a̵s̵t̵_̵o̵n̵e̵,̵ ̵Fin.ext_iff, Fin.val_one] at h₁

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3311:66: warning: This simp argument is unused:
  Fin.ext_iff

Hint: Omit it from the simp argument list.
  simp only [List.length_nil, Nat.zero_add, Nat.cast_one, Fin.e̵x̵t̵_̵i̵f̵f̵,̵ ̵F̵i̵n̵.̵val_one] at h₁

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3311:79: warning: This simp argument is unused:
  Fin.val_one

Hint: Omit it from the simp argument list.
  simp only [List.length_nil, Nat.zero_add, Nat.cast_one, Fin.ext_iff,̵ ̵F̵i̵n̵.̵v̵a̵l̵_̵o̵n̵e̵] at h₁

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3351:20: warning: This simp argument is unused:
  MultiTapeTM.step

Hint: Omit it from the simp argument list.
  simp [M̵u̵l̵t̵i̵T̵a̵p̵e̵T̵M̵.̵s̵t̵e̵p̵,̵ ̵catalogPolyUnaryTM, Action.apply, catalogPolyCfg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3351:38: warning: This simp argument is unused:
  catalogPolyUnaryTM

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.step, c̵a̵t̵a̵l̵o̵g̵P̵o̵l̵y̵U̵n̵a̵r̵y̵T̵M̵,̵ ̵Action.apply, catalogPolyCfg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3351:72: warning: This simp argument is unused:
  catalogPolyCfg

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.step, catalogPolyUnaryTM, Action.apply,̵ ̵c̵a̵t̵a̵l̵o̵g̵P̵o̵l̵y̵C̵f̵g̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3352:10: warning: This simp argument is unused:
  MultiTapeTM.step

Hint: Omit it from the simp argument list.
  simp [M̵u̵l̵t̵i̵T̵a̵p̵e̵T̵M̵.̵s̵t̵e̵p̵,̵ ̵catalogPolyUnaryTM, Action.apply, catalogPolyCfg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3352:28: warning: This simp argument is unused:
  catalogPolyUnaryTM

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.step, c̵a̵t̵a̵l̵o̵g̵P̵o̵l̵y̵U̵n̵a̵r̵y̵T̵M̵,̵ ̵Action.apply, catalogPolyCfg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3352:62: warning: This simp argument is unused:
  catalogPolyCfg

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.step, catalogPolyUnaryTM, Action.apply,̵ ̵c̵a̵t̵a̵l̵o̵g̵P̵o̵l̵y̵C̵f̵g̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3399:23: warning: This simp argument is unused:
  Prod.mk.injEq

Hint: Omit it from the simp argument list.
  simp only [ht0, MultiTapeTM.runFrom_zero, splitRestoreScan, Cfg.ofWords,
      Option.some.injEq,̵ ̵P̵r̵o̵d̵.̵m̵k̵.̵i̵n̵j̵E̵q̵] at hstate

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
=== 27/57 TCSlib/Complexity/TuringMachine/CodeParser
TCSlib/Complexity/TuringMachine/CodeParser.lean:339:13: warning: This simp argument is unused:
  codeBitsNat_bits

Hint: Omit it from the simp argument list.
  simp only [c̵o̵d̵e̵B̵i̵t̵s̵N̵a̵t̵_̵b̵i̵t̵s̵,̵ ̵List.append_assoc, codeReadFin_append, bind, Option.bind,
  ̵  ̵ ̵ ̵codeReadTable_append,
  ̲  ̲ ̲ ̲List.all_replicate, id_eq, Bool.true_eq, or_true,
  ̵  ̵ ̵ ̵ite_self, ↓reduceIte, pure]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:339:70: warning: This simp argument is unused:
  bind

Hint: Omit it from the simp argument list.
  simp only [codeBitsNat_bits, List.append_assoc, codeReadFin_append, b̵i̵n̵d̵,̵ ̵Option.bind,
      codeReadTable_append, List.all_replicate, id_eq, Bool.true_eq, or_true,
  ̵  ̵ ̵ ̵ite_self, ↓reduceIte,
  ̲  ̲ ̲ ̲pure]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:339:76: warning: This simp argument is unused:
  Option.bind

Hint: Omit it from the simp argument list.
  simp only [codeBitsNat_bits, List.append_assoc, codeReadFin_append, bind, O̵p̵t̵i̵o̵n̵.̵b̵i̵n̵d̵,̵
  ̵ ̵ ̵ ̵ ̵codeReadTable_append,
  ̲  ̲ ̲ ̲List.all_replicate, id_eq, Bool.true_eq, or_true,
  ̵  ̵ ̵ ̵ite_self, ↓reduceIte, pure]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:340:53: warning: This simp argument is unused:
  Bool.true_eq

Hint: Omit it from the simp argument list.
  simp only [codeBitsNat_bits, List.append_assoc, codeReadFin_append, bind, Option.bind,
      codeReadTable_append, List.all_replicate, id_eq, B̵oo̵l̵.̵t̵ru̵e̵_e̵q̵,̵ ̵o̵r̵_̵true,
  ̵  ̵ ̵ ̵ite_self, ↓reduceIte, pure]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:340:67: warning: This simp argument is unused:
  or_true

Hint: Omit it from the simp argument list.
  simp only [codeBitsNat_bits, List.append_assoc, codeReadFin_append, bind, Option.bind,
      codeReadTable_append, List.all_replicate, id_eq, Bool.true_eq, o̵r̵_̵t̵r̵u̵e̵,̵
  ̵ ̵ ̵ ̵ ̵ite_self, ↓reduceIte, pure]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:420:43: warning: This simp argument is unused:
  h₁

Hint: Omit it from the simp argument list.
  simp [pairDecode, h₁̵,̵ ̵h̵₂, h₃] at h

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:420:47: warning: This simp argument is unused:
  h₂

Hint: Omit it from the simp argument list.
  simp [pairDecode, h₁, h₂̵,̵ ̵h̵₃] at h

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:420:51: warning: This simp argument is unused:
  h₃

Hint: Omit it from the simp argument list.
  simp [pairDecode, h₁, h₂,̵ ̵h̵₃̵] at h

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
=== 28/57 TCSlib/Complexity/TuringMachine/MathlibBridge
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:448:8: warning: This simp argument is unused:
  Function.update_self

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index, F̵u̵n̵c̵t̵i̵o̵n̵.̵u̵p̵d̵a̵t̵e̵_̵s̵e̵l̵f̵,̵ ̵hs]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:454:12: warning: This simp argument is unused:
  Action.apply_workTapes

Hint: Omit it from the simp argument list.
  simp [A̵c̵t̵i̵o̵n̵.̵a̵p̵p̵l̵y̵_̵w̵o̵r̵k̵T̵a̵p̵e̵s̵,̵ ̵bridgeOne, bridgeCfg, hi, hk]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:459:8: warning: This simp argument is unused:
  Function.update_self

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index, F̵u̵n̵c̵t̵i̵o̵n̵.̵u̵p̵d̵a̵t̵e̵_̵s̵e̵l̵f̵,̵ ̵hs,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲SignType.pos_eq_one, SignType.coe_one, List.length_cons, Nat.cast_add, Nat.cast_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:484:8: warning: This simp argument is unused:
  Function.update_self

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index,
          F̵u̵n̵c̵t̵i̵o̵n̵.̵u̵p̵d̵a̵t̵e̵_̵s̵e̵l̵f̵,̵ ̵SignType.neg_eq_neg_one, SignType.coe_neg_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:490:12: warning: This simp argument is unused:
  Action.apply_workTapes

Hint: Omit it from the simp argument list.
  simp [A̵c̵t̵i̵o̵n̵.̵a̵p̵p̵l̵y̵_̵w̵o̵r̵k̵T̵a̵p̵e̵s̵,̵ ̵bridgeOne, bridgeCfg, hi, hk]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:495:8: warning: This simp argument is unused:
  Function.update_self

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index,
          F̵u̵n̵c̵t̵i̵o̵n̵.̵u̵p̵d̵a̵t̵e̵_̵s̵e̵l̵f̵,̵ ̵SignType.neg_eq_neg_one, SignType.coe_neg_one, SignType.zero_eq_zero, SignType.coe_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲List.length_cons, Nat.cast_add, Nat.cast_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:496:50: warning: This simp argument is unused:
  List.length_cons

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index,
          Function.update_self, SignType.neg_eq_neg_one, SignType.coe_neg_one, SignType.zero_eq_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲SignType.coe_zero, L̵i̵s̵t̵.̵l̵e̵n̵g̵t̵h̵_̵c̵o̵n̵s̵,̵ ̵Nat.cast_add, Nat.cast_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:496:68: warning: This simp argument is unused:
  Nat.cast_add

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index,
          Function.update_self, SignType.neg_eq_neg_one, SignType.coe_neg_one, SignType.zero_eq_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲SignType.coe_zero, List.length_cons, N̵a̵t̵.̵c̵a̵s̵t̵_̵a̵d̵d̵,̵ ̵Nat.cast_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:496:82: warning: This simp argument is unused:
  Nat.cast_one

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index,
          Function.update_self, SignType.neg_eq_neg_one, SignType.coe_neg_one, SignType.zero_eq_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲SignType.coe_zero, List.length_cons, N̵a̵t̵.̵c̵a̵s̵t̵_̵a̵d̵d̵,̵ ̵N̵a̵t̵.̵c̵a̵s̵t̵_̵o̵n̵e̵]̵N̲a̲t̲.̲c̲a̲s̲t̲_̲a̲d̲d̲]̲

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:719:32: warning: This simp argument is unused:
  Num.cast_zero

Hint: Omit it from the simp argument list.
  simp only [Num.to_of_nat,̵ ̵N̵u̵m̵.̵c̵a̵s̵t̵_̵z̵e̵r̵o̵] at hz

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:821:75: warning: This simp argument is unused:
  hk

Hint: Omit it from the simp argument list.
  simp [bridgeStore, PartrecToTM2.K'.elim, hi, hk̵,̵ ̵h̵] at *

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:869:15: warning: This simp argument is unused:
  Action.apply

Hint: Omit it from the simp argument list.
  simp only [̵A̵c̵t̵i̵o̵n̵.̵a̵p̵p̵l̵y̵,̵ ̵b̵r̵i̵d̵g̵e̵C̵f̵g̵,̵[̲b̲r̲i̲d̲g̲e̲C̲f̲g̲,̲ bridgeOne, SignType.zero_eq_zero, moveInputPos_zero]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:869:40: warning: This simp argument is unused:
  bridgeOne

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeCfg, b̵r̵i̵d̵g̵e̵O̵n̵e̵,̵ ̵SignType.zero_eq_zero, moveInputPos_zero]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:878:41: warning: This simp argument is unused:
  SignType.coe_zero

Hint: Omit it from the simp argument list.
  simp only [bridgeCfg, bridgeStore_at, ↓reduceIte, List.length_nil, Nat.cast_zero, neg_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲SignType.zero_eq_zero, S̵i̵g̵n̵T̵y̵p̵e̵.̵c̵o̵e̵_̵z̵e̵r̵o̵,̵ ̵SignType.neg_eq_neg_one, SignType.coe_neg_one, zero_add]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
=== 29/57 TCSlib/Complexity/TuringMachine/UniversalStartup
TCSlib/Complexity/TuringMachine/UniversalStartup.lean:160:54: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalStartup.lean:164:54: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalStartup.lean:190:52: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalStartup.lean:197:54: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalStartup.lean:215:52: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalStartup.lean:274:46: warning: This simp argument is unused:
  VirtualTag

Hint: Omit it from the simp argument list.
  simp_all ̵[̵V̵i̵r̵t̵u̵a̵l̵T̵a̵g̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
=== 30/57 TCSlib/Complexity/TuringMachine/UniversalInterpreter
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:330:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:353:6: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:378:83: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:439:60: warning: This simp argument is unused:
  zero_add

Hint: Omit it from the simp argument list.
  simp only [universalStateWindow, Nat.cast_zero, add_zero,̵ ̵z̵e̵r̵o̵_̵a̵d̵d̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:503:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:510:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:519:71: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:519:83: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:546:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:553:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:563:39: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:1020:75: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:1021:16: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:1021:28: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
=== 31/57 TCSlib/Complexity/TuringMachine/UniversalBlock
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:68:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:83:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:62:10: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:79:64: warning: This simp argument is unused:
  universalSkipDone

Hint: Omit it from the simp argument list.
  simp [universalInterpreter, universalFour, hr, h, hz,̵ ̵u̵n̵i̵v̵e̵r̵s̵a̵l̵S̵k̵i̵p̵D̵o̵n̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:93:50: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:93:62: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:108:10: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:164:53: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:164:65: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:185:50: warning: This simp argument is unused:
  Nat.add_zero

Hint: Omit it from the simp argument list.
  simp only [List.length_nil, List.flatMap_nil, Nat.a̵d̵d̵_̵zero,̵ ̵N̵a̵t̵.̵z̵e̵r̵o̵_add,
  ̵  ̵ ̵ ̵ ̵ ̵Nat.cast_zero, add_zero,
  ̲  ̲ ̲ ̲ ̲ ̲MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:244:40: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:271:40: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:289:6: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:289:61: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:289:73: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:289:6: warning: 'simp only [Fin.val_mk, Nat.cast_add, Nat.cast_one]' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:289:61: warning: 'congr 1' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:289:73: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:313:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:321:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:426:40: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:574:68: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
=== 32/57 TCSlib/Complexity/TuringMachine/Universal
TCSlib/Complexity/TuringMachine/Universal.lean:314:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:337:6: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:362:83: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:427:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:434:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:443:71: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:443:83: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:470:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:477:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:487:39: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:621:75: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:622:16: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:622:28: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:644:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:659:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:638:10: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/TuringMachine/Universal.lean:655:85: warning: This simp argument is unused:
  universalSkipDone

Hint: Omit it from the simp argument list.
  simp [timedCutInterpreter, universalInterpreter, universalFour, hr, h, hz,̵ ̵u̵n̵i̵v̵e̵r̵s̵a̵l̵S̵k̵i̵p̵D̵o̵n̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Universal.lean:669:50: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:669:62: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:684:10: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/TuringMachine/Universal.lean:740:53: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:740:65: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:761:50: warning: This simp argument is unused:
  Nat.add_zero

Hint: Omit it from the simp argument list.
  simp only [List.length_nil, List.flatMap_nil, Nat.a̵d̵d̵_̵zero,̵ ̵N̵a̵t̵.̵z̵e̵r̵o̵_add,
  ̵  ̵ ̵ ̵ ̵ ̵Nat.cast_zero, add_zero,
  ̲  ̲ ̲ ̲ ̲ ̲MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Universal.lean:820:40: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:847:40: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:865:6: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:865:61: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:865:73: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:865:6: warning: 'simp only [Fin.val_mk, Nat.cast_add, Nat.cast_one]' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:865:61: warning: 'congr 1' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:865:73: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:889:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:897:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:1006:40: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:1106:68: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Universal.lean:1484:16: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1484:34: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1484:61: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1484:16: warning: 'apply Fin.ext' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1484:34: warning: 'simp only [Fin.val_mk]' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1484:61: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1578:30: warning: This simp argument is unused:
  Nat.reduceAdd

Hint: Omit it from the simp argument list.
  simp only [Nat.add_assoc,̵ ̵N̵a̵t̵.̵r̵e̵d̵u̵c̵e̵A̵d̵d̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Universal.lean:1583:16: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1583:34: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1583:61: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1583:16: warning: 'apply Fin.ext' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1583:34: warning: 'simp only [Fin.val_mk]' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1583:61: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1606:28: warning: This simp argument is unused:
  Nat.reduceAdd

Hint: Omit it from the simp argument list.
  simp only [Nat.add_assoc,̵ ̵N̵a̵t̵.̵r̵e̵d̵u̵c̵e̵A̵d̵d̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Universal.lean:1608:43: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Universal.lean:1608:10: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:1608:28: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:1608:55: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:2278:46: warning: This simp argument is unused:
  VirtualTag

Hint: Omit it from the simp argument list.
  simp_all ̵[̵V̵i̵r̵t̵u̵a̵l̵T̵a̵g̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
=== 33/57 TCSlib/Complexity/Uncomputability/Computable
=== 34/57 TCSlib/Complexity/Uncomputability/Diagonalization
=== 35/57 TCSlib/Complexity/Uncomputability/Halting
=== 36/57 TCSlib/Complexity/TuringMachine/Nondeterministic
=== 37/57 TCSlib/Complexity/Formulas/CNF
=== 38/57 TCSlib/Complexity/Formulas/CNFEncoding
=== 39/57 TCSlib/Complexity/Formulas/DNF
=== 40/57 TCSlib/Complexity/ClassNP/PolyTime
=== 41/57 TCSlib/Complexity/ClassNP/NP
TCSlib/Complexity/ClassNP/NP.lean:359:8: warning: declaration uses 'sorry'
=== 42/57 TCSlib/Complexity/ClassNP/CoNP
=== 43/57 TCSlib/Complexity/ClassNP/EXP
TCSlib/Complexity/ClassNP/EXP.lean:750:16: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/EXP.lean:879:8: warning: declaration uses 'sorry'
=== 44/57 TCSlib/Complexity/ClassNP/Reductions
=== 45/57 TCSlib/Complexity/ClassNP/NTIME
TCSlib/Complexity/ClassNP/NTIME.lean:215:8: warning: `Set.eq_empty_iff_forall_not_mem` has been deprecated: Use `Set.eq_empty_iff_forall_notMem` instead
=== 46/57 TCSlib/Complexity/ClassNP/Nondeterminism
TCSlib/Complexity/ClassNP/Nondeterminism.lean:672:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/Nondeterminism.lean:712:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/Nondeterminism.lean:722:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/Nondeterminism.lean:742:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/Nondeterminism.lean:763:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/Nondeterminism.lean:774:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/Nondeterminism.lean:810:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/Nondeterminism.lean:816:8: warning: declaration uses 'sorry'
=== 47/57 TCSlib/Complexity/ClassNP/SAT
TCSlib/Complexity/ClassNP/SAT.lean:108:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/SAT.lean:120:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/SAT.lean:155:8: warning: declaration uses 'sorry'
=== 48/57 TCSlib/Complexity/ClassNP/TMSAT
TCSlib/Complexity/ClassNP/TMSAT.lean:951:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/TMSAT.lean:1140:8: warning: declaration uses 'sorry'
=== 49/57 TCSlib/Complexity/CookLevin/Snapshot
TCSlib/Complexity/CookLevin/Snapshot.lean:176:8: warning: declaration uses 'sorry'
TCSlib/Complexity/CookLevin/Snapshot.lean:192:8: warning: declaration uses 'sorry'
TCSlib/Complexity/CookLevin/Snapshot.lean:204:8: warning: declaration uses 'sorry'
TCSlib/Complexity/CookLevin/Snapshot.lean:217:8: warning: declaration uses 'sorry'
TCSlib/Complexity/CookLevin/Snapshot.lean:244:8: warning: declaration uses 'sorry'
=== 50/57 TCSlib/Complexity/CookLevin/Hardness
TCSlib/Complexity/CookLevin/Hardness.lean:82:8: warning: declaration uses 'sorry'
TCSlib/Complexity/CookLevin/Hardness.lean:212:8: warning: declaration uses 'sorry'
TCSlib/Complexity/CookLevin/Hardness.lean:219:8: warning: declaration uses 'sorry'
TCSlib/Complexity/CookLevin/Hardness.lean:228:8: warning: declaration uses 'sorry'
TCSlib/Complexity/CookLevin/Hardness.lean:234:8: warning: declaration uses 'sorry'
=== 51/57 TCSlib/Complexity/ClassNP/Tautology
TCSlib/Complexity/ClassNP/Tautology.lean:110:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/Tautology.lean:130:8: warning: declaration uses 'sorry'
=== 52/57 TCSlib/Complexity/TuringMachine
=== 53/57 TCSlib/Complexity/ClassP
=== 54/57 TCSlib/Complexity/Uncomputability
=== 55/57 TCSlib/Complexity/Formulas
=== 56/57 TCSlib/Complexity/CookLevin
=== 57/57 TCSlib/Complexity/ClassNP
SWEEP_PASS modules=57
END_UTC: 2026-10-04T14:27:42Z


## ===== audits/logs/ch1-libfill4-axioms.log =====

P4 closure integration: axiom attestation
HEAD: c013f270402ec5babaf33f94d3c15c3ca2589239
UTC: 2026-10-04T14:28:00Z
ROOTS Turing.capture_run: []
ROOTS Turing.FinTM.redirectTM_computes: []
ROOTS Turing.FinTM.redirectTM_live: []
ROOTS Turing.FinTM.computesFunInTime_cond: []
ROOTS Turing.loop_run: []
ROOTS Turing.FinTM.exists_loopCfgTM: []
ROOTS Turing.FinTM.exists_loopTM: []
ROOTS Turing.FinTM.exists_loopFindTM: []
ROOTS Turing.FinTM.computesFunInTime_prepend: []
ROOTS Turing.FinTM.computesFunInTime_pairEncodeFixed: []
ROOTS Turing.FinTM.computesFunInTime_pairDup: []
ROOTS Turing.FinTM.computesFunInTime_incFixed: []
ROOTS Turing.FinTM.computesFunInTime_pairValid: []
ROOTS Turing.FinTM.computesFunInTime_pairFst: []
ROOTS Turing.FinTM.computesFunInTime_pairSnd: []
ROOTS Turing.FinTM.computesFunInTime_pairConcat: []
ROOTS Turing.FinTM.computesFunInTime_lengthBits: []
ROOTS Turing.FinTM.computesFunInTime_polyUnary: []
ROOTS Turing.FinTM.computesFunInTime_polyBits: []
ROOTS Turing.FinTM.computesFunInTime_pairLenCheck: []
ROOTS Turing.FinTM.computesFunInTime_stripLast: []
ROOTS Turing.FinTM.computesFunInTime_pairMapSnd: []
ROOTS Turing.FinTM.computesFunInTime_splitSolve: []
ROOTS Turing.timed_universal: []
ROOTS Turing.timed_universal_concrete: []
ROOTS Complexity.timed_universal_quantitative: []
ROOTS Complexity.NP_subset_EXP: [Complexity.enumMachine_contracts]
ROOTS Complexity.TMSAT_mem_NP: [Complexity.TMSAT_mem_NP]
LIBRARY CLOSURE AUDIT PASS: all 23 contracts admission-free; the Build tree carries zero admissions; headline and campaign regressions unchanged.
lean exit: 0


## ===== audits/logs/ch1-libfill-lint.log =====

WARN  TCSlib/Complexity/TuringMachine/Build/Loop.lean                     2693 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/Primitives.lean               4418 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/MathlibBridge.lean                  1100 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean           1147 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean  1127 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean      1102 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Universal.lean                      2901 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean           1027 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
INFO  TCSlib/Complexity/TuringMachine/Build/Convention.lean               122 lines; 6 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Loop.lean                     2693 lines; 5 public / 95 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Primitives.lean               4418 lines; 15 public / 167 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Wrappers.lean                 687 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Build/Wrappers.lean                 687 lines; 7 public / 20 private declarations
INFO  TCSlib/Complexity/TuringMachine/CodeParser.lean                     790 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/CodeParser.lean                     790 lines; 13 public / 49 private declarations
INFO  TCSlib/Complexity/TuringMachine/Composition.lean                    651 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Composition.lean                    651 lines; 6 public / 11 private declarations
INFO  TCSlib/Complexity/TuringMachine/Configuration.lean                  224 lines; 18 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Deterministic.lean                  403 lines; 33 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Encoding.lean                       481 lines; 19 public / 10 private declarations
INFO  TCSlib/Complexity/TuringMachine/Finite.lean                         257 lines; 13 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/MathlibBridge.lean                  1100 lines; 1 public / 73 private declarations
INFO  TCSlib/Complexity/TuringMachine/Nondeterministic.lean               248 lines; 16 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Oracle.lean                         517 lines; 29 public / 2 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean   600 lines; 1 public / 50 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/Bidirectional.lean       464 lines; 2 public / 37 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean           1147 lines; 1 public / 37 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean  1127 lines; 47 public / 42 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/ObliviousLedger.lean     219 lines; 4 public / 2 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule.lean   688 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule.lean   688 lines; 19 public / 18 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean      1102 lines; 8 public / 59 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean          981 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean          981 lines; 2 public / 53 private declarations
INFO  TCSlib/Complexity/TuringMachine/Simulation.lean                     919 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Simulation.lean                     919 lines; 48 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/StateRenaming.lean                  124 lines; 6 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Sweep.lean                          392 lines; 22 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Universal.lean                      2901 lines; 4 public / 130 private declarations
INFO  TCSlib/Complexity/TuringMachine/UniversalBlock.lean                 794 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/UniversalBlock.lean                 794 lines; 6 public / 17 private declarations
INFO  TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean           1027 lines; 37 public / 13 private declarations
INFO  TCSlib/Complexity/TuringMachine/UniversalStartup.lean               591 lines; 10 public / 21 private declarations

style_lint: 0 FAIL, 8 WARN over 28 files
---
WARN  TCSlib/Complexity/ClassNP/TMSAT.lean           1206 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
INFO  TCSlib/Complexity/ClassNP/CoNP.lean            165 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/ClassNP/EXP.lean             882 lines > target 600
INFO  TCSlib/Complexity/ClassNP/EXP.lean             882 lines; 6 public / 40 private declarations
INFO  TCSlib/Complexity/ClassNP/NP.lean              382 lines; 3 public / 18 private declarations
INFO  TCSlib/Complexity/ClassNP/NTIME.lean           222 lines; 7 public / 0 private declarations
INFO  TCSlib/Complexity/ClassNP/Nondeterminism.lean  819 lines > target 600
INFO  TCSlib/Complexity/ClassNP/Nondeterminism.lean  819 lines; 8 public / 32 private declarations
INFO  TCSlib/Complexity/ClassNP/PolyTime.lean        162 lines; 5 public / 1 private declarations
INFO  TCSlib/Complexity/ClassNP/Reductions.lean      477 lines; 10 public / 16 private declarations
INFO  TCSlib/Complexity/ClassNP/SAT.lean             158 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/ClassNP/TMSAT.lean           1206 lines; 6 public / 40 private declarations
INFO  TCSlib/Complexity/ClassNP/Tautology.lean       133 lines; 5 public / 0 private declarations

style_lint: 0 FAIL, 1 WARN over 10 files


## ===== scripts/ab_ch1_module_order.txt =====

TCSlib/Complexity/TuringMachine/Configuration
TCSlib/Complexity/TuringMachine/Deterministic
TCSlib/Complexity/TuringMachine/StateRenaming
TCSlib/Complexity/TuringMachine/Finite
TCSlib/Complexity/TuringMachine/Oracle
TCSlib/Complexity/TuringMachine/Simulation
TCSlib/Complexity/TuringMachine/Sweep
TCSlib/Complexity/TuringMachine/Composition
TCSlib/Complexity/TuringMachine/Build/Convention
TCSlib/Complexity/TuringMachine/Build/Wrappers
TCSlib/Complexity/TuringMachine/Build/Loop
TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction
TCSlib/Complexity/TuringMachine/Robustness/SingleTape
TCSlib/Complexity/TuringMachine/Robustness/Bidirectional
TCSlib/Complexity/ClassP/DTIME
TCSlib/Complexity/ClassP/TimeConstructible
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup
TCSlib/Complexity/TuringMachine/Robustness/ObliviousLedger
TCSlib/Complexity/TuringMachine/Robustness/Oblivious
TCSlib/Complexity/ClassP/P
TCSlib/Complexity/ClassP/ModelInvariance
TCSlib/Complexity/ClassP/Examples
TCSlib/Complexity/TuringMachine/Encoding
TCSlib/Complexity/TuringMachine/Build/Primitives
TCSlib/Complexity/TuringMachine/CodeParser
TCSlib/Complexity/TuringMachine/MathlibBridge
TCSlib/Complexity/TuringMachine/UniversalStartup
TCSlib/Complexity/TuringMachine/UniversalInterpreter
TCSlib/Complexity/TuringMachine/UniversalBlock
TCSlib/Complexity/TuringMachine/Universal
TCSlib/Complexity/Uncomputability/Computable
TCSlib/Complexity/Uncomputability/Diagonalization
TCSlib/Complexity/Uncomputability/Halting
TCSlib/Complexity/TuringMachine/Nondeterministic
TCSlib/Complexity/Formulas/CNF
TCSlib/Complexity/Formulas/CNFEncoding
TCSlib/Complexity/Formulas/DNF
TCSlib/Complexity/ClassNP/PolyTime
TCSlib/Complexity/ClassNP/NP
TCSlib/Complexity/ClassNP/CoNP
TCSlib/Complexity/ClassNP/EXP
TCSlib/Complexity/ClassNP/Reductions
TCSlib/Complexity/ClassNP/NTIME
TCSlib/Complexity/ClassNP/Nondeterminism
TCSlib/Complexity/ClassNP/SAT
TCSlib/Complexity/ClassNP/TMSAT
TCSlib/Complexity/CookLevin/Snapshot
TCSlib/Complexity/CookLevin/Hardness
TCSlib/Complexity/ClassNP/Tautology
TCSlib/Complexity/TuringMachine
TCSlib/Complexity/ClassP
TCSlib/Complexity/Uncomputability
TCSlib/Complexity/Formulas
TCSlib/Complexity/CookLevin
TCSlib/Complexity/ClassNP
