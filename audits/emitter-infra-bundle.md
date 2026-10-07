# External audit pack — the emitter increment, shared-infrastructure audit

Audits the **statements** of the machine-construction library's emitter
increment (design `machine-library-design.md` §11, approved; §11a
spec-phase refinements): **five sorried contracts** —
`Turing.emit_run`, `Turing.FinTM.exists_emitLoopTM`,
`Turing.FinTM.computesFunInTime_splitSolveWith`,
`Turing.FinTM.computesFunInTime_unaryToken`,
`Turing.FinTM.computesFunInTime_appendBit` — plus the two real
transformers (`emitAction`, `emitCfg`) and two pure vocabulary
definitions (`solveSplitWith`, `unaryTokenSplit`). This is the
statements-first adversarial round in the mold of the original
shared-infrastructure audit, whose round 1 caught a **false loop
statement** (`exists_loopTM`'s zero-step vacuity against the input-head
information bound) and whose round 2 caught a final-answer/configuration
gap: bring exactly that scrutiny to these five. **No proofs are in
question — there are none yet**; fills follow only after this gate
closes on **zero blockers/majors**. Record findings in
`audits/emitter-infra-findings.md`.

**Evidence separation.** Out of scope: the existing library (two closed
gates — `audits/ch1-infra-resolutions.md` attached for the loop-contract
history, `audits/ch1-libfill-resolutions.md` committed); the epoch-1–3
fills (epochs 1–2 gate-closed; **epoch 3 is not yet audited** — its two
attached REPORTs are *customer frontier evidence*, not audited material,
and nothing here certifies them); the model files (attached as the
definitions the statements quantify over). The A continuation (3A-cont)
is in flight and independent: it builds its body bespoke and consumes
none of these statements.

## Maintainer-side attestations (verify or challenge)

1. **Append-only spec commit.** `883ebc79` touches the four `Build/`
   files, the design document, and logs/records with **1,467 insertions
   and zero deletions** — no existing declaration, docstring, import, or
   option changed anywhere.
2. **Elaboration.** Fresh 57/57 sweep, zero `error:` lines; admissions
   **18 = the 13 campaign admissions + exactly the five spec contracts**
   (Wrappers 1, Loop 1, Primitives 3; `audits/logs/emitter-spec-sweep.log`,
   attached).
3. **Regressions.** The committed epoch-2 closure program re-run against
   the fresh oleans: every expectation unchanged — all ten epoch-2
   targets admission-free, Chapter-1 headline and library regressions
   intact (`audits/logs/emitter-spec-axioms.log`, attached).
4. **Policy.** Build-scope lint 0 FAIL / 2 WARN (the standing
   `Loop`/`Primitives` size exceptions, which this increment grows under
   the recorded D7 deferral; `audits/logs/emitter-spec-lint.log`,
   attached). Every new declaration carries statement prose, a
   construction sketch, named customers, and the spec-phase flag.

## What is under audit, and priorities

The five statements' **truth** (a machine with the stated contract must
exist) and **adequacy** (the named customers must be closable through
them). Riskiest first:

1. **`exists_emitLoopTM`** (Loop.lean, the centerpiece). Attack it the
   way round 1 attacked `exists_loopTM`:
   - *Truth of the clean-seam discipline*: rounds are hypothesized from
     `Cfg.ofWords anchor (stateWord body.k s)` — empty output — while
     the real run reaches round `i` with the accumulated concatenation.
     The construction sketch claims runs commute with output prefixes
     because the transition table never reads the output tape. Verify
     this against the model (`MultiTapeTM.step`, `Action.apply`): is
     output genuinely write-only, including clamping/boundary behavior?
   - *The self-bounding chunk claim*: the statement carries **no**
     emission-size hypothesis, on the argument that the round equality
     forces `|emitF x s| ≤ t ≤ T |x|` (output grows at most one symbol
     per step). Verify that model fact, including the halting
     transition's emission.
   - *Round-count alignment*: the conclusion's
     `(List.range (R x.length + 1)).flatMap …` (indices `0..R`) against
     the decision loop's `i ≤ R` segment structure and the find-mode
     host's exhaustion terminal, which appends nothing. Off-by-one here
     is a blocker.
   - *Vacuity and information flow*: `Inv`-discipline (`hInv0` +
     `hInvStep` cover every iterate), `0 < t` positive rounds, anchor
     exclusion at positive times only, fuel via `hF` — all mirrored
     from the audited sibling; check nothing was weakened in
     transcription.
   - *Envelope*: `c·(T n + 1)·(R n + 2)` — the loopFind envelope; check
     startup + `R+1` rounds + countdown bookkeeping fit, including
     `R = 0`.
   - *Feasibility of the sketch* (find-mode host reuse, all-advance
     rounds, output-prefix commutation, `loop_run`-template summation):
     is any step of that plan structurally blocked?
2. **`emit_run`** (Wrappers.lean). The dual-of-capture transcription:
   host has the **same** tape count (capture's host has `k + 1`);
   `emitAction` forwards `a.output` verbatim and redirects halt to
   `ret`; `emitCfg` carries `output = pre ++ c.output`. Check the
   halting-transition emission is forwarded (capture's audited trap, in
   mirror image); the guard semantics (`∀ t' < t, ¬Halted` supplying a
   genuine source step including at the final halt) transcribe
   correctly; the `t = 0` and already-halted-`c₀` edges; and that the
   lemma composes with the existing embedding vocabulary
   (`leftAction`/`rightCfg`) the way `capture_run`'s consumers use it.
3. **`computesFunInTime_splitSolveWith`** (Primitives.lean). Truth of
   the envelope `c·(n+1)·(TE (n+1) + n + 2)` under `Monotone TE`:
   candidates `0..n`, per-round evaluator run on the length-`i`
   candidate prefix (`TE i ≤ TE (n+1)`), whole-canonical-word binary
   comparison, scratch restore, increment; the one-past-end stall;
   exhaustion output `[]`; the `n = 0` and `f 0 = 0` edges
   (`Nat.bits 0 = []` comparisons). Check the hypothesis set is neither
   too weak (is monotonicity of `TE` alone enough — no monotonicity of
   `f` is assumed, and none should be needed for the *least*-solution
   semantics) nor too strong for the named instantiation
   (`e3_exp_bits_timed`'s budget is monotone). Verify
   `solveSplitWith (fun i => C*(i+1)^e)` definitionally recovers
   `solveSplit C e`.
4. **`computesFunInTime_unaryToken`** (Primitives.lean). The token
   conventions (`unaryTokenSplit`: unterminated trailing token; empty
   word; leading `false` as the length-zero token) against the three
   customers' grammars (3B's serialization scanner, 4A's index reads,
   4B); the `c·(n+1)` budget against the `pairEncode` output length
   (`2|tok| + 2 + |rest|`).
5. **`computesFunInTime_appendBit`** and the §11a narrowings: P17's
   subsumption (a constant chunk stage = `emitPhase` over the existing
   P2 `constTM`) and P18's reduction to the append atom (cross-round
   persistence via the loop state word) — are both really available to
   the customers without a further statement?
6. **Customer fit**, against the two attached frontier REPORTs and the
   committed phase-4 records:
   - 3B-cont: can `satRedTM`'s streaming states 9–34 be realized as an
     `exists_emitLoopTM` instantiation (loop state = cursor + position,
     chunks = emitted clause fragments) with `emit_run`/`unaryToken`
     supplying the phases, delivering `PolyTimeComputable` of the proved
     `satReduction`? Name any missing seam **now**, not at fill time.
   - 4A: does the emitting loop's shape serve the Cook-Levin emitter
     under the six-stage output-silence contract and the exact
     serialization-length ledger (`audits/ch2-phase4-*`), per decision
     11.3 (its brief waits on this gate)?
   - 3A-cont: is `computesFunInTime_splitSolveWith` the correct
     generalization of the body existential displayed in the batch-A
     REPORT (whose bespoke construction is the harvest template)?
7. **Vocabulary hygiene**: the two pure definitions' edge conventions
   as stated in their docstrings; no drift against the audited
   `solveSplit`/`incFixed` conventions beside them.

Severity scheme as always: blocker / major / minor / note; findings to
`audits/emitter-infra-findings.md`; this pack is immutable once sent
(errata via the resolutions file).

## Verification appendix (runs and manifest)

- Sweep: `emitter-spec-sweep.log` (attached) — 57/57, zero errors, 18
  admissions as itemized above.
- Regressions: `emitter-spec-axioms.log` (attached) — the committed
  epoch-2 closure program, exit 0.
- Lint: `emitter-spec-lint.log` (attached) — 0 FAIL / 2 WARN.
- Bundle manifest — **14 attachments** after the pack: the 4 `Build/`
  sources (`Convention`, `Wrappers`, `Loop`, `Primitives`); the 2 model
  files (`TuringMachine/Finite`, `TuringMachine/Composition`); the
  design document (`machine-library-design.md`, §11/§11a included); the
  2 customer frontier REPORTs
  (`audits/ch2-epoch3-agent-reports/batch{A,B}.md`); the prior
  infra-gate record (`audits/ch1-infra-resolutions.md`); the 3 logs;
  the 57-module order list. Total 4 + 2 + 1 + 2 + 1 + 3 + 1 = 14. The
  phase-4 records, the libfill resolutions, and all earlier logs are
  committed in the repository at the paths cited above.

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

/-- **Emitter-increment vocabulary** (design §11, spec phase): least
solution `i ≤ n` of the width-parametric split equation `i + f i = n`, or
`none` — the generalization of `Turing.solveSplit` from the hardwired
polynomial family to an arbitrary width function. At
`f = fun i => C * (i + 1) ^ e` this definitionally recovers
`solveSplit C e n`. -/
def solveSplitWith (f : ℕ → ℕ) (n : ℕ) : Option ℕ :=
  (List.range (n + 1)).find? fun i => i + f i == n

/-- **Emitter-increment vocabulary** (design §11, spec phase): split off
the leading unary token — the maximal `true`-prefix together with its
terminating `false` delimiter — returning the token and the remainder. A
word with no delimiter yields the whole word as an unterminated token with
empty remainder; the empty word yields two empty words; a leading `false`
is the length-zero token `[false]`. This is the shared atom of the
serialization grammars (unary indices with terminators); single-bit
markers are read by the same step at token length zero or one. -/
def unaryTokenSplit : List Bool → List Bool × List Bool
  | [] => ([], [])
  | false :: rest => ([false], rest)
  | true :: rest =>
    let (tok, r) := unaryTokenSplit rest
    (true :: tok, r)

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

**Maintainer note (D6 promotion).** Batch W's two shared-lemma promotion
requests are executed: `timed_input_bound` is now the public
`Turing.MultiTapeTM.timed_input_bound` in `Deterministic.lean` (generalized
from `Bool` to an arbitrary symbol type; the proof was symbol-free), and
`timed_rewind` is the public `Turing.FinTM.timed_rewind` in
`Simulation.lean`, verbatim. The private copies formerly here are removed;
the two call sites below consume the public lemmas.
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

/-- **E2 action transformer** (design §11, spec phase): the forwarding dual
of `Turing.captureAction`. Transform one source action into a host action
over the **same** tapes: input move and work-tape actions are kept
verbatim; the source's emission, **if any, is forwarded as the host's
physical emission** — including an emission on the halting transition; a
live source successor is embedded via `emb`, and a halting source action
transfers control to the designated live return state `ret`. This is what
lets a proved transducer serve as one emission stage of a larger host. -/
def emitAction (emb : S → H) (ret : H) (a : Action k Bool S) :
    Action k Bool H where
  inputTape := a.inputTape
  workTapes := a.workTapes
  output := a.output
  state := some ((a.state.map emb).getD ret)

/-- **E2 configuration correspondence** (design §11, spec phase): a source
configuration `c`, viewed inside the host — state embedded (a halted source
appears at the live return state `ret`), tapes, heads, and input position
verbatim, and the host's physical output equal to the host's prior output
`pre` followed by everything the source has emitted. -/
def emitCfg {input : List Bool} (emb : S → H) (ret : H)
    (pre : List Bool) (c : Cfg k Bool S input) :
    Cfg k Bool H input where
  state := some ((c.state.map emb).getD ret)
  inputPos := c.inputPos
  workTapes := c.workTapes
  workTapePos := c.workTapePos
  output := pre ++ c.output

/-- **E2, the forwarding wrapper** (spec, fill pending — design §11;
customers: the emitting loop's per-round chunk calls, the Cook-Levin
clause-group emission (4A), 3B-cont's fresh-literal chains). Any host
machine agreeing with the transformed table on an embedded copy of the
source states runs the source in lockstep while **appending the source's
output to the host's physical output**, the exact dual of
`Turing.capture_run`: source tapes verbatim, the halting transition's
emission forwarded like any other, and the host landing in the live
return state at the source's halt.

**Construction sketch.** Mirror `capture_run`: one `emitAction`-apply
lemma (source fields preserved; the optional emission appended to the
host output after `pre`), then induction over the guarded run, the guard
supplying a genuine source step including at the final halt. -/
theorem emit_run {input : List Bool} (tm : MultiTapeTM k Bool S)
    (host : MultiTapeTM k Bool H) (emb : S → H) (ret : H)
    (hagree : ∀ (s : S) (inp : Option Bool) (w : Fin k → Option Bool),
      host.tr (emb s) inp w = emitAction emb ret (tm.tr s inp w))
    (pre : List Bool) (c₀ : Cfg k Bool S input) (t : ℕ)
    (hlive : ∀ t' < t, ¬(tm.runFrom c₀ t').Halted) :
    host.runFrom (emitCfg emb ret pre c₀) t =
      emitCfg emb ret pre (tm.runFrom c₀ t) := by
  sorry

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
        MultiTapeTM.timed_input_bound (tm := D.tm) (D.tm.initCfg x) t
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
per-segment cost bounded worst-case by the counter width (the proved
estimate below at the borrow lemmas; the amortized aggregate also holds
but is not used per segment), exhaustion exactly at borrow-overflow, so
rounds `0, …, R |x|` run before the exhaustion rejection `[false]`.
Acceptance surfaces as the captured halt and emits `[true]`. The private
already-halted-terminal summation lemma `loop_halted_run` sums the seam
family (the frozen `Turing.loop_run` does not apply to the `[false]`
terminal — fill-audit minor 1's documentation correction, maintainer
closing sweep); the invariant hypotheses confine every round to
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

/-- **E1, the emitting loop** (spec, fill pending — design §11; customers:
the Cook-Levin clause-group emitter (4A), 3B-cont's streaming reduction
transducer, 4B's dual-reduction emitter). The emitting sibling of
`Turing.FinTM.exists_loopCfgTM`: the same anchored round discipline —
startup within the envelope and no earlier anchor visit; per-round
positive duration, anchor exclusion, and input-length-only budgets — but
each round, instead of staying silent and either accepting or advancing,
**advances and appends its exact chunk** `emitF x s` to the physical
output. The machine runs all `R + 1` rounds and computes the
concatenation of the chunks in order. There is no verdict bit and no
deciding variant: compose with the existing decision layer instead
(design §11 non-goals).

Each round's seam is stated from the canonical clean configuration; the
round equality itself bounds the chunk length by the round's duration
(output grows by at most one symbol per step), so no separate emission
bound is hypothesized.

**Construction sketch.** The find-mode `loopHost` is the engine: its
exhaustion terminal appends nothing, so with every round advancing, the
accumulated output survives to the halt. Re-derive the host contract
with the output-prefixed seam (runs commute with output prefixes — the
transition table never reads the output tape), and thread the
concatenation through `loop_run`'s summation template. The fuel counter,
startup, and countdown machinery are reused unchanged; they are silent. -/
theorem exists_emitLoopTM (body F : FinTM Bool) (anchor : body.State)
    (Inv : List Bool → List Bool → Prop)
    (stepF emitF : List Bool → List Bool → List Bool)
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
        body.tm.runFrom
          (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t =
            { Cfg.ofWords (input := x) anchor (stateWord body.k (stepF x s))
                with output := emitF x s }) :
    ∃ (E : FinTM Bool) (c : ℕ),
      E.ComputesFunInTime
        (fun x => (List.range (R x.length + 1)).flatMap
          (fun i => emitF x ((stepF x)^[i] (s0 x))))
        (fun n => c * (T n + 1) * (R n + 2)) := by
  sorry

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

/-- **E4′, width-parametric split search** (spec, fill pending — design
§11; customers: 3A-cont's exponential padding equation — whose bespoke
body is this contract's harvest template — and every later padding
argument, including the ch3 hierarchy theorems). The generalization of
`Turing.FinTM.computesFunInTime_splitSolve` from the hardwired polynomial
family to a hypothesis-supplied width evaluator: given a machine `E`
computing the binary representation of `f` of the input length within a
monotone budget `TE`, a machine solving `i + f i = n` by first-success
search, emitting the threaded split of the original input, and `[]` on
exhaustion, inside the loopFind envelope over `TE`. At
`f = fun i => C * (i + 1) ^ e` the computed function definitionally
recovers the catalog split's.

**Construction sketch.** The `exists_loopFindTM` engine with candidate
word as loop state: per round, run `E` on the prepared candidate prefix
with captured output (charging `TE` before any validity check), compare
whole canonical binary words against the suffix length, restore scratch,
advance by one; the one-past-end candidate takes a positive silent
stall. 3A-cont's displayed body contracts are exactly this round
discipline. -/
theorem computesFunInTime_splitSolveWith (f : ℕ → ℕ) (E : FinTM Bool)
    (TE : ℕ → ℕ) (hTE : Monotone TE)
    (hE : E.ComputesFunInTime (fun s => Nat.bits (f s.length)) TE) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun w => match solveSplitWith f w.length with
          | some i => pairEncode (w.take i) (w.drop i)
          | none => [])
        fun n => c * (n + 1) * (TE (n + 1) + n + 2) := by
  sorry

/-- **P16, the unary token step** (spec, fill pending — design §11;
customers: 3B-cont's streaming scanner, the Cook-Levin emitter's index
reads (4A), 4B's dual scanner — the fourth re-derivation of this atom
otherwise, after 2D's parsers, 3B's `satScanTM`, and 3D's six-state
scan). Split off the leading unary token (`Turing.unaryTokenSplit`) as a
self-delimiting pair, in linear time.

**Construction sketch.** One left-to-right scan emitting the token bits
as read, the delimiter, the pair framing, and the remainder — the proved
scanner stages of the 3B and 3D deliveries are the harvest sources. -/
theorem computesFunInTime_unaryToken :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun x => pairEncode (unaryTokenSplit x).1 (unaryTokenSplit x).2)
        fun n => c * (n + 1) := by
  sorry

/-- **P18′, append one bit** (spec, fill pending — design §11, narrowed at
spec time from the drafted accumulator row: cross-round persistence is the
loop engine's state-word mechanism, so the catalog atom is just the
append; customers: fresh-variable counters in 3B-cont and 4A, via the
loop state word). Append a single fixed bit to the input word, in linear
time.

**Construction sketch.** Copy the input verbatim, emit `b`, halt — P1's
copier with one extra emission on the halting transition. -/
theorem computesFunInTime_appendBit (b : Bool) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => x ++ [b]) fun n => c * (n + 1) := by
  sorry

end Turing.FinTM

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

## ===== audits/ch2-epoch3-agent-reports/batchA.md =====

# Chapter 2, epoch 3, batch A — partial continuation delivery

**INCOMPLETE: zero of the six public targets is fully closed.** The first
public target has 35 new, proved private components and one remaining local
admission for a native exponential split-search body. Its degree-zero case
is closed. Targets 2–6 remain untouched, respecting the brief's order.
The six-target no-`sorryAx` gate **does not pass**. This is a continuation
checkpoint under ground rule 6 of `briefs/ch2-epoch3-batchA.md`, not a
completed batch or a statement escalation.

## Repository and provenance

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Requested base branch: `complexity/arora-barak-ch1`.
- Required and actual source base: `b55180a8bb38b94427e75e63630aa6eab5fd6e95`.
- Working branch: `fill/ch2-e3-A`.
- Delivery commit: `6b521020358c97303f1dd550b10776de1df0ea25`.
- The brief was read before source work from the specified remote branch,
  whose cloned tip was `3293de776053bf755a89c16c5cfbcc7f7d3b8501`. The work
  branch was then created at the brief's required source base. No rebase,
  push, PR, or modification of another named branch occurred.
- Single-agent execution, without delegation.

## Target status

| Order | Target | Status and remaining work |
|---|---|---|
| 1 | `ntime_expPow_subset_NEXP` | **Partial.** Exact exponential certificate correspondence, split semantics, native binary evaluator, loop instantiation conditional on concrete body contracts, and timed loader/simulator composition are proved. One local `sorry` remains in the positive-degree search-body construction. |
| 2 | `NEXP_subset_iUnion_NTIME` | Original admission, byte-identical. The exponential emission scheduler and its integration with the existing B2 host have not been implemented. |
| 3 | `NEXP_eq_iUnion_NTIME` | Original admission, byte-identical. Not filled ahead of the two directions. |
| 4 | `EXP_eq_NEXP_of_P_eq_NP` | Original admission and audited sketch, byte-identical. Neither the nested-pair verifier with both exact checks nor the pad-emission/relocated-decider construction has been implemented. |
| 5 | `P_ne_NP_of_EXP_ne_NEXP` | Original admission, byte-identical. Not filled ahead of target 4. |
| 6 | `EXP_subset_NEXP` | Original admission; the entire `EXP.lean` file is byte-identical to the required base. No completed exponential padding verifier is claimed. |

The admission count is unchanged: five explicit `sorry` sites in
`Nondeterminism.lean`, one in `EXP.lean`, and 21 warnings in the complete
campaign sweep. **There are no admitted new private helpers.** The first
public theorem's single `sorry` moved from its whole proof to the exact
native-body existential below. The other five public admissions are
unmodified. Kernel traversal confirms each of the six targets is rooted
only in its own admission.

## Proved components and binding seams

| Obligation | Discharging declarations and precise limitation |
|---|---|
| Strict increase and unique exact-width split | `e3_split_strictMono`, `e3_split_unique`; coefficient zero and degree zero are included. |
| Finite search, exact equation, all-input failure | `e3Split`, `e3_split_spec`, `e3_split_none_iff`, `e3_split_complete`; `e3_split_empty` rejects the empty input for positive coefficient. These are semantic contracts, not a native split implementation. |
| Exact choice-word verifier and source-budget transfer | `e3ChoiceVerifier`, `e3_choice_append`, `e3_choice_no_split`, `e3_choice_budget`, `e3_choice_certificate`. The existing `acceptsWithin_iff_of_halts` uses all-branch halting for backward truncation; the certificate width is not enlarged. `e3_coefficient_pos` proves the zero-time case impossible. |
| Binary evaluation before validation | `e3_bits_shift` proves the exact little-endian representation for a positive coefficient; `e3_bits_length_bound` proves the polynomial bit bound from the candidate's input-length bound, without any padding-validity hypothesis. |
| Native binary evaluator | `e3ShiftTM`, `e3_shift_scan`, `e3_shift_computes`, `e3_shift_timed`, `e3_exp_bits_timed`. The catalog unary generator emits only the exponent's polynomial number of symbols; the scanner replaces them with zero bits and appends the fixed coefficient's bits. Coefficient zero uses the constant empty binary word. Timed composition gives a coefficient times degree `c+1`. |
| Loader, guarded input simulation, choice alignment and output | `e3_split_answer` reuses the unchanged `cont_pair_computes`, `cont_pair_empty`, and their already audited loader/core. It rejects the empty failure payload and handles every successful split. The core's guarded input, isolated tapes, exact choice alignment, halting-emission capture and singleton verdict remain those of the existing proof. |
| Complete verifier after a split emitter | `e3_split_length` bounds every emitted intermediate word by twice the original length plus two. `e3_verifier_of_split` carries the actual intermediate-length and timed phase contracts through `bufferedComp_start`/`bufferedSecondCfg_run`, adding thirteen copies of the positive polynomial envelope. Its split-emitter hypothesis is still uninstantiated in the positive-degree case. |
| Result-bearing loop and complete failed-search branch | `e3SplitStep`, `e3SplitAccept`, `e3_step_inv`, `e3_step_orbit`, `e3_find_congr`, `e3_find_eq`, `e3_loop_result`, `e3_loop_bound`, `e3_split_of_body`. The last lemma invokes `exists_loopFindTM`, uses `computesFunInTime_lengthBits` for fuel, and proves the first-success payload and exhaustion semantics. It explicitly requires native startup and positive first-return, scratch-restoring round contracts. |
| Small cases | `e3_split_degree_zero` is the catalog split with coefficient `2*C`, exponent zero; `e3_split_coefficient_zero` is the catalog's zero-width split. The former closes the first target's degree-zero branch. |
| Reverse-host seam | Not attempted in this continuation. Existing B2 and `cont_*` material is byte-identical. No guessing phase is presented as a decider, and no mathematical deadline is presented as a native clock. |
| Theorem-2.22 pad-validation seam | Not implemented. The binary evaluator and pre-validation bit estimate are reusable components only; they do not perform the two required exact checks, parsing, assembly, or captured verifier call. |

## Exact first-target frontier and continuation plan

Inside the sole remaining local admission of `ntime_expPow_subset_NEXP`,
the context contains a positive time coefficient, a nonzero degree, and
`Eval`, `B`, `hEval` from the proved `e3_exp_bits_timed`. That evaluator
computes the exact binary padding length in time
`B * (n + 1) ^ (c + 1)` on **every** input word of length `n`.

The remaining goal is to construct a finite deterministic `body`, an
`anchor`, and constants `A,r` with exactly these contracts:

1. **Startup:** from the genuine blank-tape initial configuration on `w`,
   reach `Cfg.ofWords anchor (stateWord body.k [])` within
   `A * (w.length + 1) ^ (r + 1)`; no earlier configuration has the anchor
   state.
2. **Round:** from `Cfg.ofWords anchor (stateWord body.k s)`, for every
   `s.length <= w.length + 1`, take a positive number of steps within the
   same input-length-only envelope and do not visit the anchor at a
   positive earlier time. If
   `s.length + a * 2 ^ (s.length + 1) ^ c = w.length`, halt with output
   exactly `pairEncode (w.take s.length) (w.drop s.length)`. Otherwise
   return exactly the canonical seam with candidate `e3SplitStep w s`.
   Every scratch tape, work head, input head, and output is covered by
   this full-configuration equality.

The source contains the complete Lean existential; it is deliberately not
weakened to a function-level computation. A continuation should proceed:

1. Handle the one-past-end candidate by a positive silent stall. For a
   live candidate, preserve the original input and state word, prepare the
   evaluator's virtual candidate input with blank source work tapes, and
   capture its binary output. Dispatch at actual completed source states.
2. Compute the remaining suffix length in binary on its actual prepared
   input, and compare the entire canonical binary words. Charge evaluation
   before any validity check. The candidate invariant permits length at
   most `w.length+1`, so the pre-validation envelope must absorb the
   corresponding `w.length+2` factor; do not use an unjustified logarithmic
   bound.
3. On success emit the exact threaded split of the preserved original
   input, with no leaked evaluator output. On failure restore all source
   and administrative scratch, append one true to the state word where
   permitted, restore the input head, and prove the exact canonical seam.
4. Prove the positive first-return property and the common polynomial
   envelope. The existing `e3_split_of_body` and `e3_verifier_of_split`
   then finish target 1 without further machine constructions.
5. Continue with target 2's exponential scheduler and B2 host, followed by
   targets 3–6 in the brief's order. Preserve all existing proofs.

The catalog's polynomial-width `splitSolve` instance cannot be supplied
for this positive-degree exponential equation. The loop engine has been
adapted, but its **body remains missing**. Neither the binary evaluator nor
the conditional loop lemma is claimed to supply that body.

Statement escalations: **none**. Requested shared lemmas: **none**. The
obstruction is unfinished native construction work, not evidence that a
frozen statement is false.

## All new declarations

All 35 declarations below are `private`, have proved bodies, and have empty
kernel admission roots. Definitions and their generated descendants are
included in the separate closure traversal.

- `e3_split_strictMono`
- `e3_split_unique`
- `e3Split`
- `e3_split_spec`
- `e3_split_none_iff`
- `e3_split_complete`
- `e3_split_empty`
- `e3ChoiceVerifier`
- `e3_choice_append`
- `e3_choice_no_split`
- `e3_choice_budget`
- `e3_choice_certificate`
- `e3_coefficient_pos`
- `e3_bits_shift`
- `e3_bits_length_bound`
- `e3ShiftTM`
- `e3_shift_scan`
- `e3_shift_computes`
- `e3_shift_timed`
- `e3_exp_bits_timed`
- `e3SplitWord`
- `e3_split_length`
- `e3_split_answer`
- `e3_verifier_of_split`
- `e3SplitStep`
- `e3SplitAccept`
- `e3_step_inv`
- `e3_step_orbit`
- `e3_find_congr`
- `e3_find_eq`
- `e3_loop_result`
- `e3_loop_bound`
- `e3_split_of_body`
- `e3_split_degree_zero`
- `e3_split_coefficient_zero`

## Source preservation and size

Only `TCSlib/Complexity/ClassNP/Nondeterminism.lean` changes in git: 561
insertions, two deletions (the former whole-target `sorry` and the target
comment's old closing line). The first target's docstring gains a clearly
marked append-only partial-fill appendix; its original content and its
entire theorem signature are preserved. The complete prefix containing all
previously proved material is byte-identical. The suffix beginning at
target 2 is byte-identical. No existing private was changed or removed.

- `Nondeterminism.lean`: 3,013 lines, 157,403 UTF-8 bytes;
  SHA-256 `deed194fd5abc2d7b10ad64306d952a669c860b278bb5f87f1a8558c14905c22`.
- `EXP.lean`: 2,534 lines, unchanged; included as an explicitly unchanged
  reference snapshot.
- The brief records size exceptions for both owned modules. The new
  private families stay in the owned file under its exclusive-ownership
  rule; no split or cross-file visibility change was attempted.
- `verify_surface.py` reproduces the exact prefix/suffix, public-signature,
  append-only docstring, helper-inventory, unchanged-EXP and changed-path
  checks against the required base. `surface-check.json` records the result.
- Style lint: **0 FAIL / 3 WARN**, all three recorded large-file warnings.

## Verification and environment

- Lean **4.25.0**, commit
  `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`.
- Mathlib **029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e**; all 11 installed
  dependency revisions match the committed manifest (`dependency-pins.json`).
- Required `lake exe cache get`: invoked once. It built the cache utility
  but **failed in its ProofWidgets cloud-release step** (`cache-get.log`).
  The underlying release-step failure was not diagnosed beyond its nonzero
  exit. This is not reported as a successful `cache get`.
- Recovery used the pin-matched existing compressed cache and the cache
  package's hash-directed unpacking API (`RecoverCache.lean` and
  `cache-recovery.log`). Unneeded generated artifacts were pruned locally
  to preserve disk space; no dependency source or pinned revision changed.
- The existing pinned toolchain was reused. Its process-location workaround
  redirects only its own `/proc/<pid>/exe` lookup to `/proc/self/exe` in
  this execution environment; it does not modify Lean or its kernel.
- No direct `lake build` was run. All TCSlib checking used the committed
  `lean_check_tree.sh` script. Intermediate failures while filling the new
  proofs were repaired before the final sweep.
- **Final full fresh sweep: 57/57**, 57 fresh nonempty oleans, exit **0**,
  **zero `error:` lines**, `FULL_SWEEP_COMPLETE`. The output tree was new
  and empty before the sweep. There are **21 expected admission warnings**,
  unchanged from the required source base.
- Owned-and-downstream sweep: pass (`downstream-final.log`).
- Axiom prints and checked-kernel traversal on the final fresh tree:
  exit **0**. **35 source helpers / 83 helper-and-generated declarations**
  have empty admission roots and axioms within
  `[propext, Classical.choice, Quot.sound]`.
- The five regression headlines (`ntime_poly_subset_NP`,
  `NP_subset_iUnion_NTIME`, `NP_eq_iUnion_NTIME`, `NP_subset_EXP`, and
  `mem_NP_iff_exists_length_le`) retain empty roots and the standard triple.
- **All six batch targets still print `sorryAx`**, each rooted only in its
  own declaration. `PARTIAL_CLOSURE_AUDIT_PASS` means the partial inventory
  and regression expectations passed; it does **not** mean the batch's
  completion gate passed.
- `git diff --check`, surface verification, git-bundle verification and
  detached patch replay pass. Replay produces the identical complete git
  tree `d22abd101f493db5a145bde5ae4eb3d63ad43577` and byte-identical source.

Final sweep tail:

```text
CHECK TCSlib/Complexity/TuringMachine
CHECK TCSlib/Complexity/ClassP
CHECK TCSlib/Complexity/Uncomputability
CHECK TCSlib/Complexity/Formulas
CHECK TCSlib/Complexity/CookLevin
CHECK TCSlib/Complexity/ClassNP
FULL_SWEEP_COMPLETE
```

## Flat archive and integration

`fill-ch2-e3-A.zip` is flat: every member, including `SHA256SUMS`, is at
its root. It contains this report, the full modified source, the unchanged
EXP reference snapshot, one numbered `git format-patch`, an incremental
git bundle, final sweep and axiom logs, the axiom program, and verification
records and scripts. `SHA256SUMS` covers every other member; no oleans,
toolchain or dependency cache is included.

| Archive file | Repository path / purpose |
|---|---|
| `Nondeterminism.lean` | `TCSlib/Complexity/ClassNP/Nondeterminism.lean`, full modified source |
| `EXP.lean` | `TCSlib/Complexity/ClassNP/EXP.lean`, unchanged pinned reference |
| `0001-*.patch` | Apply with `git am` at the required source base; preserves Codex authorship |
| `fill-ch2-e3-A.bundle` | Alternative containing the same commit; requires the recorded base |
| `AxiomChecks.lean` | Run on the fresh tree with pinned package build paths in `LEAN_PATH` |
| `verify_surface.py` | Run with the repository path to reproduce the source-preservation checks |

Verify the extracted payload using `sha256sum -c SHA256SUMS`. Use the
repository's committed script and 57-module order for elaboration. The
archive's check-script copy is provenance; its relative-root convention
expects its original `scripts/` location when executed.

## Notation

`n` is a candidate or evaluator input length; `w` is the original verifier
input; `s` is the loop's current candidate state word. `a` (or generic `C`)
is the exact exponential-width coefficient; `c` is its degree. `Eval` and
`B` are the binary evaluator and its time coefficient. `body`, `anchor`,
`A`, and `r` are the missing round machine, return state, common time
coefficient and round-envelope degree parameter. All other code names
refer to declarations in the pinned source or this delivery.

## ===== audits/ch2-epoch3-agent-reports/batchB.md =====

# Epoch 3, Batch B — partial delivery

Date: 2026-10-05. Repository: https://github.com/Shilun-Allan-Li/tcslib.

**Partial delivery under brief ground rule 5.** Targets 1 and 2 are proved with
no admitted dependencies. Target 3 remains admitted at its original public
root. Its formula semantics, all-string reduction equivalence, size bounds,
and the machine initialization/maximum-variable pass are proved. The streaming
serializer correctness and time proof remain for continuation. The construction
budget was exhausted at that boundary; this is not a completion claim for all
three targets.

## Branch, base, scope, and delivery

- Required upstream branch: `complexity/arora-barak-ch1`; no `main` work.
- Required immutable base: `b55180a8bb38b94427e75e63630aa6eab5fd6e95`.
- Sole working branch: `fill/ch2-e3-B`.
- Delivery head: `d93ef0cb88c7e9758b0b6a0e309ef8c4ac90799a`.
- The brief was read from the requested upstream branch at
  `3293de776053bf755a89c16c5cfbcc7f7d3b8501`; the work branch was then created at
  the brief's required base. No rebase, push, or PR was performed.
- Commits, in order:
  1. `fdbb1dcd30e90ec4d55067fde04307ba42c14049` — guarded finite SAT/3SAT verifiers.
  2. `d93ef0cb88c7e9758b0b6a0e309ef8c4ac90799a` — clause-splitting semantics and
     the explicit machine continuation frontier.
- Only repository path changed: `TCSlib/Complexity/ClassNP/SAT.lean`.
  The full replacement appears as **`SAT.lean` at the archive root**.
- Final source: **2363 lines; 123206 bytes**.
  SHA-256: `a74dc1dd898c0ad8649d28e38b4625a035a2705689ba59aed4958d2dff0d0c8a`.
- The repository working tree is clean. Other branches and all out-of-scope
  source files are unchanged. A temporary detached verification worktree was
  used only to replay the patch series, then removed.
- `fill-ch2-e3-B.bundle` is an **incremental bundle requiring the exact base
  above**. It advertises only `refs/heads/fill/ch2-e3-B` and passed `git bundle
  verify`. It is not intended as a stand-alone clone without the base objects.

The archive is flat: every member, including `SHA256SUMS`, is at the root.
`SHA256SUMS` covers every other member and excludes itself. The two patches
apply in numeric order. Replay with `git am --committer-date-is-author-date`
from the required base reproduced the exact head hash, not only an equivalent
source tree; see `patch-replay.log`.

## Target status and admissions

| Frozen target | Status | Checked admission roots |
| --- | --- | --- |
| `Complexity.SAT_mem_NP` | Proved first, exact `(1,1)` certificate parameters | `[]` |
| `Complexity.SAT3_mem_NP` | Proved second, exact `(1,1)` certificate parameters | `[]` |
| `Complexity.SAT_reducible_SAT3` | **Admitted; original `by sorry` body retained** | `[Complexity.SAT_reducible_SAT3]` |

The owned file has exactly **one** admission, the third target at line 2360.
There are no admitted private helpers, new axioms, weakened statements, or
sanctioned admitted dependencies. Neither completed membership uses the
remaining reduction admission.

## Verifier obligations and their proofs

| Obligation | Discharging declarations and behavior |
| --- | --- |
| Exactly `n+1` certificate bits | `satAssignment`, `sat_certificate`, `sat_verifier_equiv`, `sat3_verifier_equiv`; use `CNF.numVars_decode_le` and `eval_congr_of_lt_numVars` |
| Unique odd split, including total length one | `sat_split_some`, `sat_split_exists`, `satVerdict_append`; actual machine uses `computesFunInTime_splitSolve 1 1` |
| **Explicit even-length rejection** | `sat_split_even` proves split failure on every even total length; `satVerdict` and both polynomial verifier constructions reject that failure branch |
| Exact complete syntax check | `sat_takeTrues_repr`, `sat_parseLit_repr`, `sat_parseClause_repr`, `sat_parseClauses_repr`, `sat_parse_repr`, and the `satSyntaxSuffix_*` invariant |
| Parser realized by a finite machine | `satSyntaxStep`, `satScanTM`, `satScan_computes`, `satSyntax_spec`, `satSyntax_poly` |
| Parse failure accepts the fallback | `satSafe_spec`, `satVerdict_false_poly`, `satVerdict_true_poly`; malformed instances decode to the satisfiable empty formula |
| Unary assignment walks | `satEval_index`, `satEval_literal`, `satEval_clause`, `satEval_formula`; each literal of index `v` takes `3*v+8` transitions in the doubled input representation |
| Capture and output isolation | `sat_first_halt`, `satEval_start`; catalog capture includes a final halting emission, then native and certificate heads rewind |
| Buffered final verdict | Evaluation accumulates clause/formula Booleans in finite control and emits only at the final formula terminator; conditional/composition wrappers capture intermediate outputs |
| Width pass for 3SAT | `satWidthStep` counts occurrences with a saturated finite counter; `satWidthScan_serialize`, `satWidthScan_poly`, `satVerdict_true_poly` |
| Polynomial-time composition | `sat_pipeline_poly`, `satSafeValue_poly`, `sat_comp_on_image`, `sat_pt_cond`, `satVerifier_of_poly` |

**Complete syntax comes first.** The six-state grammar machine distinguishes
formula markers, clause markers, unary indices, polarity, exact end, and error.
Any trailing bit after the formula terminator enters the error state. Clause
and formula zero terminators are accepted even at zero parser fuel; successful
parse reconstruction and `parse_serialize` connect this machine to the frozen
parser on every string. No failed clause or excessive width may reject an
incompletely parsed prefix. In particular the malformed prefix/trailing-data
case `[true,false,false,true]` follows the accepting fallback branch. The 3SAT
width machine runs only after full syntax success; evaluation runs only after
width success. Length-zero instances have a one-bit certificate and are
covered by the same proof.

Both syntax and width scanners use zero work tapes and run in exactly `m+1`
steps on an `m`-bit scanner input. The uniform evaluation contract is linear
in its safe paired-input length. The audited `(1,1)` split catalog contract
uses a cubic bound. The full verifiers obtain actual finite-machine polynomial
witnesses through the audited wrappers; no appeal to informal algorithmic
complexity or output length substitutes for a machine proof.

## Reduction work proved so far

The private transform is exactly the requested construction:
`head :: b :: c :: d :: rest` produces `[head,b,(n,true)]`, then recurses on
`(n,false) :: c :: d :: rest` at cursor `n+1`. Clauses of width at most three,
including the empty clause, pass through. The whole-formula transform starts
at `φ.numVars` and threads the cursor between clauses.

| Mathematical obligation | Discharging declarations |
| --- | --- |
| Monotone fresh cursor and width at most three | `satChain_cursor`, `satChain_width`, `satSplitClause_cursor`, `satSplitClause_width`, `satTransformFrom_width` |
| Soundness: transformed satisfying assignment satisfies the original clause/formula | `satChain_sound`, `satSplitClause_sound`, `satTransformFrom_sound` |
| Completeness: extend assignments without changing smaller indices | `satChain_extend_step`, `satChain_complete`, `satSplitClause_complete`, `satTransformFrom_complete` |
| Fresh-variable preservation | `satChain_vars`, `satSplitClause_vars`, `sat_numVars_le`; whole-formula preservation uses the existing `eval_congr_of_lt_numVars` |
| Equisatisfiability | `satTransform_equisat` |
| String reduction is `serialize ∘ transform ∘ decode` | `satReduction` |
| Correctness for **every string** | `satReduction_correct`, with no well-formedness premise |
| Fallback fixed by transform | `satReduction_fallback`; failed parsing maps to `CNF.serialize []` |
| Cursor, clause-count, and serialization growth | `satChain_sizes`, `satSplitClause_sizes`, `satTransformFrom_bounds`, `sat_clause_serial_bound`, `sat_serial_bound` |
| All-input output-size bound | `satReduction_size`: at most `6*|x|^2 + 8*|x| + 1` bits |

Completeness assigns the new fresh variable the truth value of the remaining
tail clause. The first emitted link and the recursively transformed clause
beginning with the negated fresh variable are then true. Each extension
preserves all smaller indices, which keeps earlier chains true when later
clauses allocate more variables. Soundness follows the converse link
induction. The serialized output bound is explicitly a **size bound**, not a
polynomial-time computation theorem.

## Exact machine continuation frontier

`satRedTM` defines a **candidate** two-work-tape, 35-state transducer. Its
unproved streaming states are documented as a candidate, not a completed
reduction witness. All definitions and proved support lemmas are axiom-clean.

The first tape is a contiguous unary fresh-variable counter. The second tape
is a temporary literal buffer with a permanent marker at position -1.
The following machine stages are fully proved:

- `satRed_init`: two silent transitions install the buffer marker.
- `satRedCounter_write`, `satRed_maxOnes`: the counter records the maximum
  unary literal length encountered, without losing a larger earlier maximum.
- `satRed_maxLiteral`: the literal pass costs `2*v+5` transitions and restores
  the counter head to zero.
- `satRed_maxClause`, `satRed_maxFormula`: the complete maximum pass is
  silent and costs at most twice the serialized input length.
- `satRed_start`: initialization, maximum pass, and audited native rewind
  reach state 9 with the native input and both work heads at their starting
  positions, empty output, an empty marked buffer, and **exactly `φ.numVars`**
  on the counter tape, in at most `3*|serialize φ|+5` transitions.

The proposed streaming states have these roles:

| States | Role | Proof status |
| --- | --- | --- |
| 9–16 | Formula/clause markers and copying the first two literals | Transition definition only |
| 17–21 | Buffer the prospective third literal and inspect whether another follows | Transition definition only |
| 22–32 | Emit positive fresh literal, close/open clauses, emit its negation, increment/rewind counter | Transition definition only |
| 33–34 | Replay/erase the buffered literal and restore its head | Transition definition only |

**Next obligations:**

1. Prove the streaming literal-buffer, fresh-variable emission, and replay
   invariants. Then induct over clauses/chains to show that the output is
   exactly `CNF.serialize (satTransform φ)`, including empty clauses/formulas.
2. Establish a uniform polynomial transition bound for those streaming states,
   then compose it with `satRed_start`. The existing output-size bound alone
   is insufficient.
3. Guard the core on **all strings** using the existing complete syntax pass.
   One suitable route is a polynomial canonicalizer
   `x ↦ if satSyntax x then x else CNF.serialize []`; parse reconstruction
   identifies its output with `serialize (decode x)`. Compose on this safe
   image using `sat_comp_on_image`, measuring its bound at the original
   input length. Finally prove `PolyTimeComputable satReduction` and combine
   it with `satReduction_correct` to fill the frozen public reduction target.

There is no new placeholder admission for these obligations: the sole owned
`sorry` remains the original public target. No statement obstruction was
encountered; continuation is a proof-construction task.

## Verification and environment

- Pinned Lean **4.25.0**, commit
  `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`.
- Pinned mathlib **`029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`**.
- Setup command `lake exe cache get` was attempted once. It checked out the
  pinned dependencies but failed fetching the ProofWidgets cloud release.
  Existing official cache archives were then unpacked with `lake exe cache
  unpack` (7506 files). Both setup logs are included. No dependency sources
  or repository build configuration were edited. `lake build` was never run.
- The available pinned toolchain was used from
  `/tmp/ch2-b2-toolchain/lean-4.25.0-linux/bin`. This host's PID namespace
  required a pre-existing `readlink` shim, supplied as `proc-self.c`: it maps
  only the current process's `/proc/<pid>/exe` lookup to `/proc/self/exe`.
  It does not modify the Lean kernel or proof checks. The shim was active
  through `LD_PRELOAD=/tmp/ch2-b2-toolchain/proc-self.so`.
- Bootstrap and iteration used `scripts/lean_check_tree.sh` and the committed
  57-module order. The **final sweep used a previously nonexistent olean
  directory**, and checked all 57 modules from scratch through that script.
- Final result: **57/57 passed; 0 `error:` lines; 19 admission warnings**,
  comprising the one documented owned admission and 18 unchanged out-of-scope
  declarations. The source had 21 campaign admissions before these two fills.
- `style_lint.py TCSlib/Complexity/ClassNP`: **0 FAIL, 4 WARN**. The SAT warning
  is its 2363-line size. Positive reason for keeping the file together:
  exclusive ownership permits only this file and requires private helpers;
  splitting into shared modules would exceed the batch's authority. The
  other three size warnings concern unchanged files. Lean also reports
  nonfatal tactic/simp linter warnings; no linter options were suppressed.
- `git diff --check` passed.
- `check-freeze.py` verifies the unchanged ordered five public declarations,
  both language definition bodies, every original comment/docstring, the
  copyright, and the option headers. Only the two precise imports
  `Mathlib.Tactic.FinCases` and `Mathlib.Data.List.MinMax` were added.
- `Ch2E3BAxioms.lean`, adapted from the committed closure template, traverses
  checked kernel declarations through types, opaque values, and constructors.
  It checks all three targets, **all 373 private/generated declarations**, and
  17 previously closed regressions. It ran against the final fresh oleans.

Headline axiom prints:

```text
SAT_mem_NP: [propext, Classical.choice, Quot.sound]
SAT3_mem_NP: [propext, Classical.choice, Quot.sound]
SAT_reducible_SAT3: [propext, sorryAx, Classical.choice, Quot.sound]
```

Both completed headline roots are empty. The union of all private/generated
closure roots is empty and its axiom set is the standard triple. The remaining
public reduction has only itself as an admission root. The audit explicitly
expects this partial-delivery exception and does not claim the all-three-target
completion gate has passed.

Final sweep tail:

```text
BEGIN 55/57 TCSlib/Complexity/Formulas
PASS 55/57 TCSlib/Complexity/Formulas
BEGIN 56/57 TCSlib/Complexity/CookLevin
PASS 56/57 TCSlib/Complexity/CookLevin
BEGIN 57/57 TCSlib/Complexity/ClassNP
PASS 57/57 TCSlib/Complexity/ClassNP
FINAL_SWEEP_PASS 57/57; elapsed_seconds=199.0
ERROR_LINES 0
ADMISSION_WARNINGS 19
```

For reproduction, apply the patches to the required base, provide the pinned
cache/toolchain, choose a fresh `TCSLIB_OLEANS`, and run the committed checker
in `scripts/ab_ch1_module_order.txt` order, exiting on any failed module. Run
`Ch2E3BAxioms.lean` with that fresh olean directory first in `LEAN_PATH`, followed
by the repository and package build-library paths. Run `python check-freeze.py
/path/to/tcslib` for the source freeze check.

## Complete final admission inventory

Only the SAT reduction row is owned by this batch. All other rows are unchanged.
The table records declarations emitting admission warnings, not every theorem
that transitively depends on an admission.

| Repository path | Line | Declaration |
| --- | ---: | --- |
| `TCSlib/Complexity/ClassNP/EXP.lean` | 2531 | `EXP_subset_NEXP` |
| `TCSlib/Complexity/ClassNP/Nondeterminism.lean` | 2377 | `ntime_expPow_subset_NEXP` |
| `TCSlib/Complexity/ClassNP/Nondeterminism.lean` | 2398 | `NEXP_subset_iUnion_NTIME` |
| `TCSlib/Complexity/ClassNP/Nondeterminism.lean` | 2409 | `NEXP_eq_iUnion_NTIME` |
| `TCSlib/Complexity/ClassNP/Nondeterminism.lean` | 2445 | `EXP_eq_NEXP_of_P_eq_NP` |
| `TCSlib/Complexity/ClassNP/Nondeterminism.lean` | 2451 | `P_ne_NP_of_EXP_ne_NEXP` |
| `TCSlib/Complexity/ClassNP/SAT.lean` | 2360 | `SAT_reducible_SAT3` |
| `TCSlib/Complexity/CookLevin/Snapshot.lean` | 176 | `oblivious_schedule_eq` |
| `TCSlib/Complexity/CookLevin/Snapshot.lean` | 192 | `snapshotAt_zero` |
| `TCSlib/Complexity/CookLevin/Snapshot.lean` | 204 | `snapshotAt_state_succ` |
| `TCSlib/Complexity/CookLevin/Snapshot.lean` | 217 | `snapshotAt_inputSymbol` |
| `TCSlib/Complexity/CookLevin/Snapshot.lean` | 244 | `snapshotAt_workSymbol` |
| `TCSlib/Complexity/CookLevin/Hardness.lean` | 82 | `NPHard.polyTimeReducible` |
| `TCSlib/Complexity/CookLevin/Hardness.lean` | 212 | `SAT_NPHard` |
| `TCSlib/Complexity/CookLevin/Hardness.lean` | 219 | `SAT_NPComplete` |
| `TCSlib/Complexity/CookLevin/Hardness.lean` | 228 | `SAT3_NPHard` |
| `TCSlib/Complexity/CookLevin/Hardness.lean` | 234 | `SAT3_NPComplete` |
| `TCSlib/Complexity/ClassNP/Tautology.lean` | 110 | `TAUTOLOGY_mem_coNP` |
| `TCSlib/Complexity/ClassNP/Tautology.lean` | 130 | `TAUTOLOGY_coNPComplete` |

## New declaration inventory

There are **135 new source declarations**, all `private`, all in namespace
`Complexity`. There are no new public declarations. Every name is listed
below and in `PRIVATE_DECLARATIONS.txt`. `KERNEL_DECLARATIONS.txt` lists all
**373** private source/generated kernel names; the same exhaustive inventory
and its axiom closure result appear in `axiom-print.log`.

```text
satAssignment
sat_certificate
sat_split_some
sat_split_exists
sat_split_even
satWidth
satWidth_spec
satVerdict
satVerifier
satVerdict_append
sat_verifier_equiv
sat3_verifier_equiv
sat_takeTrues_repr
sat_parseLit_repr
sat_parseClause_repr
sat_parseClauses_repr
sat_parse_repr
satSyntaxStep
satSyntaxSuffix
satSyntaxSuffix_cons
satSyntaxSuffix_nil
satSyntaxSuffix_run
satSyntax
satSyntax_spec
satScanTM
satScanCfg
satScan_step
satScan_run
satScan_computes
satSyntax_poly
SatEvalControl
satEvalQ
satEvalAction
satEvalTM
satEvalCfg
satEvalCfg_input
satEvalCfg_work
satEvalAction_apply
satEval_skip
satEval_double
satEval_rewind
satBits
satBits_length
satEval_index
satEval_literal
satEval_clause
satEval_formula
sat_first_halt
satEval_start
satEval_computes
sat_comp_on_image
sat_pt_linear
sat_pt_const
sat_pt_cond
sat_pt_and
satSplit
satInstance
satWitness
satSplitValid
satGood
satSafe
satSafeValue
sat_literal_lt_numVars
satSafe_spec
sat_pipeline_poly
satSafeValue_poly
satVerdict_false_poly
satVerifier_of_poly
satWidthCap
satWidthStep
satWidth_index
satWidth_literal
satWidth_clause
satWidth_formula
satWidthScan
satWidthScan_serialize
satWidthScan_poly
satVerdict_true_poly
satClause_congr
satChain
satSplitClause
satChain_cursor
satChain_width
satChain_sound
satChain_extend_step
satChain_complete
satChain_vars
satSplitClause_cursor
satSplitClause_width
satSplitClause_vars
satSplitClause_sound
satSplitClause_complete
satTransformFrom
sat_numVars_le
satTransformFrom_width
satTransformFrom_sound
satTransformFrom_complete
satTransform
satTransform_equisat
satReduction
satReduction_correct
satReduction_fallback
satChain_sizes
satSplitClause_sizes
satMeasure
satTransformFrom_bounds
sat_clause_measure
sat_measure_serialize
sat_measure_decode
sat_clause_serial_bound
sat_serial_bound
satReduction_size
satRedAction
satRedTM
satRedCounter
satRedBuffer
satRedCfg
satRedCfg_input
satRedCounter_read
satRedCounter_left
satRedCounter_write
satRedAction_apply
satRed_move
satRed_one
satRed_counterBack
satRed_maxOnes
satRed_maxLiteral
sat_foldMax_append
satClauseVars
sat_numVars_cons
satRed_maxClause
satRed_maxFormula
satRedBuffer_empty
satRed_init
satRed_start
```

## Requested shared lemmas and escalations

**None.** No frozen statement or docstring was changed, and no unprovability
obstruction was discovered. The private construction utilities remain local
as required. The sole outstanding item is the precisely described machine
proof continuation for target 3.

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

## ===== audits/logs/emitter-spec-sweep.log =====

CHECK TCSlib/Complexity/TuringMachine/Configuration
TCSlib/Complexity/TuringMachine/Configuration.lean:137:17: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Configuration.lean:140:61: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/TuringMachine/Configuration.lean:155:17: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
CHECK TCSlib/Complexity/TuringMachine/Deterministic
CHECK TCSlib/Complexity/TuringMachine/StateRenaming
CHECK TCSlib/Complexity/TuringMachine/Finite
CHECK TCSlib/Complexity/TuringMachine/Oracle
CHECK TCSlib/Complexity/TuringMachine/Simulation
CHECK TCSlib/Complexity/TuringMachine/Sweep
CHECK TCSlib/Complexity/TuringMachine/Composition
CHECK TCSlib/Complexity/TuringMachine/Build/Convention
CHECK TCSlib/Complexity/TuringMachine/Build/Wrappers
TCSlib/Complexity/TuringMachine/Build/Wrappers.lean:249:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/TuringMachine/Build/Loop
TCSlib/Complexity/TuringMachine/Build/Loop.lean:2723:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction
CHECK TCSlib/Complexity/TuringMachine/Robustness/SingleTape
CHECK TCSlib/Complexity/TuringMachine/Robustness/Bidirectional
CHECK TCSlib/Complexity/ClassP/DTIME
CHECK TCSlib/Complexity/ClassP/TimeConstructible
CHECK TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule
CHECK TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate
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
CHECK TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup
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
CHECK TCSlib/Complexity/TuringMachine/Robustness/ObliviousLedger
CHECK TCSlib/Complexity/TuringMachine/Robustness/Oblivious
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
CHECK TCSlib/Complexity/ClassP/P
CHECK TCSlib/Complexity/ClassP/ModelInvariance
CHECK TCSlib/Complexity/ClassP/Examples
CHECK TCSlib/Complexity/TuringMachine/Encoding
CHECK TCSlib/Complexity/TuringMachine/Build/Primitives
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
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:4438:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:4459:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:4475:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/TuringMachine/CodeParser
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
CHECK TCSlib/Complexity/TuringMachine/MathlibBridge
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
CHECK TCSlib/Complexity/TuringMachine/UniversalStartup
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
CHECK TCSlib/Complexity/TuringMachine/UniversalInterpreter
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
CHECK TCSlib/Complexity/TuringMachine/UniversalBlock
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
CHECK TCSlib/Complexity/TuringMachine/Universal
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
CHECK TCSlib/Complexity/Uncomputability/Computable
CHECK TCSlib/Complexity/Uncomputability/Diagonalization
CHECK TCSlib/Complexity/Uncomputability/Halting
CHECK TCSlib/Complexity/TuringMachine/Nondeterministic
CHECK TCSlib/Complexity/Formulas/CNF
CHECK TCSlib/Complexity/Formulas/CNFEncoding
CHECK TCSlib/Complexity/Formulas/DNF
CHECK TCSlib/Complexity/ClassNP/PolyTime
CHECK TCSlib/Complexity/ClassNP/NP
CHECK TCSlib/Complexity/ClassNP/CoNP
CHECK TCSlib/Complexity/ClassNP/EXP
TCSlib/Complexity/ClassNP/EXP.lean:2531:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/ClassNP/Reductions
CHECK TCSlib/Complexity/ClassNP/NTIME
TCSlib/Complexity/ClassNP/NTIME.lean:215:8: warning: `Set.eq_empty_iff_forall_not_mem` has been deprecated: Use `Set.eq_empty_iff_forall_notMem` instead
CHECK TCSlib/Complexity/ClassNP/Nondeterminism
TCSlib/Complexity/ClassNP/Nondeterminism.lean:2902:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/Nondeterminism.lean:2957:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/Nondeterminism.lean:2968:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/Nondeterminism.lean:3004:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/Nondeterminism.lean:3010:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/ClassNP/SAT
TCSlib/Complexity/ClassNP/SAT.lean:126:51: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:138:47: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:333:33: warning: Try `simp at h` instead of `simpa using h`

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/ClassNP/SAT.lean:456:63: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:608:56: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:633:59: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:670:55: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:680:58: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:691:88: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:720:60: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:731:27: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:753:91: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:720:60: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:731:27: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:753:91: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:749:84: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:809:56: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:809:56: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:792:63: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:816:51: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:877:48: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:917:55: warning: This simp argument is unused:
  FinTM.bufferTape

Hint: Omit it from the simp argument list.
  simp [captureCfg, MultiTapeTM.initCfg, Cfg.init,̵ ̵F̵i̵n̵T̵M̵.̵b̵u̵f̵f̵e̵r̵T̵a̵p̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:979:26: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:1331:8: warning: This simp argument is unused:
  satSafeValue

Hint: Omit it from the simp argument list.
  simp [satVerdict, satSplitValid, satSplit, hs, pairDecode_pairEncode, s̵a̵t̵S̵a̵f̵e̵V̵a̵l̵u̵e̵,̵ ̵satGood, satInstance,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲satWitness, satSyntax_spec, hp, CNF.decode, CNF.fallback, satWidth]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:1331:22: warning: This simp argument is unused:
  satGood

Hint: Omit it from the simp argument list.
  simp [satVerdict, satSplitValid, satSplit, hs, pairDecode_pairEncode,
  ̵  ̵ ̵ ̵ ̵ ̵ ̵ ̵satSafeValue,
  ̲ s̵a̵t̵G̵o̵o̵d̵,̵  ̲ ̲ ̲ ̲ ̲ ̲satInstance, satWitness, satSyntax_spec, hp,
  ̵  ̵ ̵ ̵ ̵ ̵ ̵ ̵CNF.decode, CNF.fallback, satWidth]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:1331:44: warning: This simp argument is unused:
  satWitness

Hint: Omit it from the simp argument list.
  simp [satVerdict, satSplitValid, satSplit, hs, pairDecode_pairEncode, satSafeValue, satGood,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲satInstance, s̵a̵t̵W̵i̵t̵n̵e̵s̵s̵,̵ ̵satSyntax_spec, hp, CNF.decode, CNF.fallback, satWidth]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:1430:80: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:1558:11: warning: Try `simp at h` instead of `simpa using h`

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/ClassNP/SAT.lean:2025:12: warning: This simp argument is unused:
  he

Hint: Omit it from the simp argument list.
  simp [h̵e̵,̵ ̵satRedCounter_read, show r < n by omega]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:2022:39: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:2036:17: warning: unused variable `hj`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/ClassNP/SAT.lean:2042:52: warning: This simp argument is unused:
  max_eq_left

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.runFrom_zero, m̵a̵x̵_̵e̵q̵_̵l̵e̵f̵t̵,̵ ̵*]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:2057:59: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:2057:59: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:2112:19: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:2112:19: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:2077:40: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:2122:82: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:2126:73: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:2128:41: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:2185:40: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:2185:40: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:2191:51: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:2210:47: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:2243:48: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:2263:28: warning: This simp argument is unused:
  Function.update_of_ne hz

Hint: Omit it from the simp argument list.
  simp [satRedBuffer, hz, F̵u̵n̵c̵t̵i̵o̵n̵.̵u̵p̵d̵a̵t̵e̵_̵o̵f̵_̵n̵e̵ ̵h̵z̵,̵ ̵FinTM.bufferTape]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:2360:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/ClassNP/TMSAT
CHECK TCSlib/Complexity/CookLevin/Snapshot
CHECK TCSlib/Complexity/CookLevin/Hardness
TCSlib/Complexity/CookLevin/Hardness.lean:82:8: warning: declaration uses 'sorry'
TCSlib/Complexity/CookLevin/Hardness.lean:212:8: warning: declaration uses 'sorry'
TCSlib/Complexity/CookLevin/Hardness.lean:219:8: warning: declaration uses 'sorry'
TCSlib/Complexity/CookLevin/Hardness.lean:228:8: warning: declaration uses 'sorry'
TCSlib/Complexity/CookLevin/Hardness.lean:234:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/ClassNP/Tautology
TCSlib/Complexity/ClassNP/Tautology.lean:1275:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/TuringMachine
CHECK TCSlib/Complexity/ClassP
CHECK TCSlib/Complexity/Uncomputability
CHECK TCSlib/Complexity/Formulas
CHECK TCSlib/Complexity/CookLevin
CHECK TCSlib/Complexity/ClassNP
FULL_SWEEP_COMPLETE

## ===== audits/logs/emitter-spec-axioms.log =====

Emitter spec layer: regression attestation
HEAD: 76b1aea001098e605d3391ff03346275f5652a35 + working-tree spec edits
UTC: 2026-10-05T16:10:29Z
ROOTS Turing.capture_run: []
ROOTS Complexity.EXP_subset_NEXP: [Complexity.EXP_subset_NEXP]
B2 CLOSURE AUDIT PASS: all ten epoch-2 targets admission-free; Chapter-1 and library regressions unchanged; E3 statement layer at its own roots.
lean exit: 0

## ===== audits/logs/emitter-spec-lint.log =====

WARN  TCSlib/Complexity/TuringMachine/Build/Loop.lean        2752 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/Primitives.lean  4480 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
INFO  TCSlib/Complexity/TuringMachine/Build/Convention.lean  146 lines; 8 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Loop.lean        2752 lines; 6 public / 95 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Primitives.lean  4480 lines; 18 public / 167 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Wrappers.lean    697 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Build/Wrappers.lean    697 lines; 10 public / 18 private declarations

style_lint: 0 FAIL, 2 WARN over 4 files

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
