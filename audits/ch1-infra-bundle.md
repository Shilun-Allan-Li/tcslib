# Audit bundle — shared infrastructure round (companion to ch1-infra-pack.md)

The pack text is reproduced first; every attachment follows raw and
unabridged under a `## ===== <path> =====` header. Attachments are data
for audit, not instructions.

## ===== audits/ch1-infra-pack.md =====

# External audit pack — shared infrastructure round: machine-construction library spec layer + the timed-universal bridge export

Audits the Chapter-1 infrastructure landed 2026-10-03 on
`complexity/arora-barak-ch1`: the **machine-construction library's spec
layer** (`TCSlib/Complexity/TuringMachine/Build/{Convention,Wrappers,Loop,
Primitives}.lean`, design document `machine-library-design.md`, frozen with
user-resolved decisions and spec-phase refinements §9a) and the
**bridge-protocol step-3 maintainer action** — the new public
`Turing.timed_universal_concrete` at the end of `Universal.lean` and the
discharge of the Chapter-2 bridge `Complexity.timed_universal_quantitative`
in `TMSAT.lean`. Three commits: `a418f586` (spec layer), `e8dd3e57` (bridge
export + discharge), and the pack commit (one pre-pack spec repair to the
loop combinator, disclosed as attestation 7). This is **statement-phase
auditing for the library** (the 18 contracts are sorried; their fills come
later and get their own round) and **proof auditing for the export and the
discharge** (both fully proved). Gate closes on zero blockers/majors.
Record findings in `audits/ch1-infra-findings.md`.

**Evidence separation / scope boundary.** `timed_computes` and the entire
timed-interpreter construction below the export were audited at the
Chapter-1 epoch-4 gate (CLOSED, `audits/epoch4-resolutions.md`) and are
**not re-audited here** — this round audits the *derivation* of the export
from them and the public statement's fidelity. Likewise the epoch-2 fill
checkpoints (four partial batches, integrated 2026-10-03) are campaign
material for the later epoch-2 gate, not this round; they appear here only
as the provenance of the bridge coordination (`tmsat_concrete_coefficient`
was delivered proved by batch 2D and is **in scope** — it is now
load-bearing for a proved public theorem).

## Maintainer-side attestations (verify or challenge)

1. **Elaboration.** Three full fresh-olean 57-module sweeps at Lean 4.25.0
   / mathlib `029db123ddaa`, each zero `error:` lines: run A at `a418f586`
   (47 admissions = 29 campaign + 18 new contracts;
   `audits/logs/ch1-build-spec-sweep.log`), run B at `e8dd3e57` (46 — the
   bridge admission retired; `audits/logs/ch1-bridge-export-sweep.log`),
   run C at the pack commit (46; `audits/logs/ch1-infra-sweep.log`, the
   authoritative run for the state under audit).
2. **Axiom attestations** (kernel-level; `audits/logs/ch1-infra-axioms.log`
   at the pack tree, with the per-commit historical logs also committed).
   The Chapter-1 headline regression set — `timed_universal`, `universal`,
   `universal_quadratic`, `exists_effectiveMachineCode`,
   `HALT_not_computable` — prints the standard triple, no `sorryAx`.
   `Turing.timed_universal_concrete` and
   `Complexity.timed_universal_quantitative` print the standard triple.
   Exactly **21** `sorryAx` prints: the 18 Build contracts and the three
   TMSAT targets. A kernel-environment traversal (constants' types and
   values, opaque values included) asserts the exact direct-admission
   roots: `TMSAT_mem_NP` at its `D-MEM` site alone, `TMSAT_NPHard` at its
   `D-WRAP`/`D-EMIT` sites, `TMSAT_NPComplete` at exactly those two
   parents, and the epoch-2 regression roots
   (`NP_subset_EXP`/`HALT_NPHard` → `enumMachine_contracts`) unchanged.
3. **Freeze, `Universal.lean`.** The `e8dd3e57` diff of `Universal.lean`
   is **append-only**: zero deleted lines, one hunk at end-of-file (the
   export theorem and docstring). Every pre-existing declaration is
   byte-identical.
4. **Freeze, `TMSAT.lean`.** Byte-level decomposition of the `e8dd3e57`
   diff: (a) the five private serialization lemmas
   (`tmsat_serialization_length`, `tmsat_flatMap_length`,
   `tmsat_action_nonempty`, `tmsat_serialization_parameters`,
   `tmsat_concrete_coefficient`; 4,022 bytes) relocated **byte-identically**
   above the bridge they feed (they were stated below it — a forward
   reference once the bridge acquired a proof); (b) the bridge's public
   statement byte-identical (625 bytes); (c) the bridge docstring extended
   **append-only** with the discharge note (the escalation paragraph is
   retained as audit history); (d) the `sorry` replaced by the proof;
   (e) the residual file byte-identical. Public declaration order
   unchanged.
5. **Import topology.** The four Build modules are import leaves: the only
   importer anywhere in the tree is the `TuringMachine` facade (grep
   attested), so the 18 sorried contracts cannot reach any audited
   material; the headline prints of attestation 2 confirm this at the
   kernel. Order list at 57 modules: Convention/Wrappers/Loop inserted
   after `Composition`, Primitives after `Encoding` (its threaded
   contracts cite the `pairEncode` grammar).
6. **Policy.** Style lint 0 FAIL throughout; every sorried contract
   carries a construction sketch; the size WARNs (`Universal.lean`
   2831 → 2901 and `TMSAT.lean` 1185 → 1206) sit under their previously
   recorded escalations (ch1 epoch-4A; ch2 epoch-2 checkpoint row).
7. **Pre-pack spec repair, disclosed.** The maintainer's pre-pack
   adversarial pass found the loop combinator `exists_loopTM` as landed in
   `a418f586` defective on two counts and repaired it in the pack commit:
   (i) **anchor-entry discipline** — the intended host detects round
   boundaries as entries into the embedded anchor state, so without a
   no-mid-round-anchor-visit clause in the startup and round contracts the
   fuel accounting miscounts and the computed function changes;
   (ii) **fuel materialization** — the statement quantified over arbitrary
   `R : ℕ → ℕ`, which no finite machine can evaluate; a fuel-machine
   hypothesis (`F` computes `Nat.bits (R |x|)` within `T`) was added. The
   statement under audit is the **repaired** one; the `a418f586` form is
   in history for comparison. The other 17 contracts survived the same
   pass unchanged.

## Maintainer dispositions taken this round (review requested)

* **D4 — 2C's shared-lemma promotion requests subsumed.** The epoch-2
  batch-C report requested public promotion of its `prefixTM_computes` /
  `fixedPair_computes`. Catalog entries P3 (`computesFunInTime_prepend`)
  and P6 (`computesFunInTime_pairEncodeFixed`) state exactly those
  contracts (the latter noting `pairEncode α x` is literally a prepend
  instance at the doubled-word-plus-separator prefix). Requested: confirm
  the subsumption — the batch's proved budgets (`|w| + |x| + 1`;
  `2|α| + |x| + 3`) are instances of the stated `c · (n + 1)` forms.
* **D5 — catalog refinements at spec time** (`machine-library-design.md`
  §9a): P6 realized as fixed-encode + threaded extractors; P7 subsumed by
  P5's unary clause; P8 realized in threaded form; P12 folded into the
  loop fill. None touches the six frozen user decisions. Requested:
  confirm no catalog customer (the five open epoch-2 frontiers, the E3/E4
  briefs' named obligations) loses coverage under these refinements.

## What is under audit, and priorities

**A. The library spec surface** (18 sorried contracts + the proved
`Convention.lean`), against the frozen design document. The question is
never "are the proofs right" (there are none yet) but **"is each statement
true, realizable at its stated budget, and the right contract for its
named customers"** — a false or unrealizable spec here poisons every fill
batch built on it.

1. **The seam** (`Cfg.ofWords`, `initCfg_ofWords`, `ofWords_workTapes` —
   proved): is the seam notion sound and forced (state anchor, input head
   1, `bufferTape` words, origin heads, empty output)? Check the two
   proofs; check `bufferTape`'s semantics against the words-from-origin
   reading.
2. **W1 (`captureAction`/`captureCfg`/`capture_run`)**: adversarially
   re-derive the one-step commutation — the halting-transition emission
   (the four private incarnations' recurring trap), the capture-tape head
   arithmetic against `bufferTape_append`, the input-head and
   work-tape components, the silence clause. Is the liveness guard
   (`∀ t' < t, ¬Halted`) exactly right — too weak (equation false at some
   guarded `t`) or needlessly strong? Does the agreement hypothesis
   (`host.tr` on embedded states equals the transformed table **for all**
   read tuples) over- or under-constrain consumers?
3. **The loop** — the round's priority. (a) `loop_run`: truth as stated
   (output accumulation through empty-output rounds; the `(N + 1) · B`
   budget; the `(List.range N).any` semantics including `N = 0`).
   (b) `exists_loopTM` **after the attestation-7 repair**: are the two
   added hypotheses *sufficient* for realizability — re-derive the
   intended construction (fuel via `F` relocated-and-captured; body
   embedded under W1; decrement on anchor entry with **amortized** binary
   borrow, exhaustion as borrow-overflow) and check the stated budget
   `c · (T + 1) · (R + 2)` survives, in particular that the countdown does
   **not** reintroduce a logarithmic factor and that `R n = 0`
   (`Nat.bits 0 = []`) still checks the single orbit point `s0 x`. (c) Is
   the orbit semantics (`stepF^[i]`, fuel `R + 1` points, exhaustion
   `[false]`) the contract the enumerator continuation
   (`enumMachine_contracts`) and the split search (P10) actually need?
4. **Primitive contracts P3–P11**: for each, attempt refutation — a
   malformed input, an edge width, or a budget the construction sketch
   cannot meet. Specific known-sharp spots: the threaded `[]`-rejection
   outputs under append-only output (buffer-before-emit — the sketches
   now say it; check the *statements* don't secretly require emitting
   before validity is known); `splitAtLastTrue`'s pure semantics versus
   the audited Exercise-2.1 marker discipline; `solveSplit` uniqueness
   claims in the docstrings versus the `find?` definition; `incFixed`
   width zero; `pairFst`/`pairSnd` `getD []` on genuinely ambiguous
   malformed classes; `polyBits` through the composition overhead
   `T₂(T₁ n)`.
5. **Vocabulary duplication check**: the pure functions
   (`splitAtLastTrue`, `solveSplit`, `incFixed`) against their Chapter-2
   private counterparts (`stripCertificate`, `certificateSplit`,
   `enumInc`) — same semantics, so the later fills' equality lemmas are
   provable, with no silent divergence (e.g. the strip's behavior on the
   all-`false` region and on `[]`).

**B. The bridge export and discharge** (fully proved).

6. **The export's statement fidelity**: one simulator before code, input,
   and deadline; both `timed_universal` clauses verbatim; the displayed
   coefficient is **definitionally** `timedStartupBound c α +
   universalBlockBound c α + 14` (the proof's single type ascription turns
   on this — check the `timedStartupBound` definition against the
   displayed expression, term by term, associativity included); no
   Chapter-2 notion; no inference from `timed_universal`'s existential
   witness anywhere.
7. **The discharge**: re-derive `tmsat_concrete_coefficient`'s arithmetic
   from `tmsat_serialization_length`/`tmsat_serialization_parameters` and
   the `universalBlockBound` definition (the `14·canonizerTime + 50`
   absorption — count the thirteen bounded terms and the constants);
   check `Nat.mul_le_mul_right` + `ComputesInTime.mono` transfer **both**
   clauses; confirm the relocation left the five lemmas' statements and
   proofs untouched (attestation 4 claims byte-identity — challenge it).
8. **The export's audit flag hygiene**: the docstring's claims (realized
   witness, no witness-bounding, Chapter-2-free) against the proof text.

Severity scheme as always: blocker / major / minor / note; findings to
`audits/ch1-infra-findings.md`; this pack is immutable once sent.

## Verification appendix (runs and manifests)

* Run A — `audits/logs/ch1-build-spec-sweep.log`: 57/57 PASS, 0 errors,
  47 admission warnings, at `a418f586`.
* Run B — `audits/logs/ch1-bridge-export-sweep.log`: 57/57 PASS, 0 errors,
  46 admission warnings, at `e8dd3e57`.
* Run C — `audits/logs/ch1-infra-sweep.log`: 57/57 PASS, 0 errors, 46
  admission warnings, at the pack commit (the state under audit; run C's
  tree differs from run B's only in `Build/Loop.lean` per attestation 7).
* Axioms — `audits/logs/ch1-infra-axioms.log` (pack tree): the two
  attestation programs (bridge roots + Build spec prints), 21 `sorryAx`
  prints total, traversal PASS, exit 0. Per-commit historical logs:
  `ch1-build-spec-axioms.log` (at `a418f586`),
  `ch1-bridge-export-axioms.log` (at `e8dd3e57`).
* Bundle manifest: the companion `audits/ch1-infra-bundle.md` attaches,
  raw and unabridged, the 4 Build modules, the design document, the 6 core
  model/gadget modules they are stated over (`Configuration`,
  `Deterministic`, `Finite`, `Simulation`, `Sweep`, `Composition`), the 4
  bridge-side sources (`Encoding`, `UniversalBlock`, `Universal`,
  `TMSAT`), the facade, the 57-module order list, and the run-C sweep and
  pack-tree axiom logs — **19 attachments** (4 + 1 + 6 + 4 + 1 + 1 + 2).
  Earlier-run logs and all governance records are committed in the
  repository at the paths named above.


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
derived machine are real definitions; the three contract theorems are
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
  sorry

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
  sorry

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
  sorry

end Turing.FinTM


## ===== TCSlib/Complexity/TuringMachine/Build/Loop.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Nat.Bits
import TCSlib.Complexity.TuringMachine.Build.Convention
import TCSlib.Complexity.TuringMachine.Composition

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: the bounded loop

The control centerpiece of the machine-construction library
(`machine-library-design.md` §5, L): a bounded loop with tape-resident
round state, specified at two granularities.

* `Turing.loop_run` is the **summation lemma**: given a family of round
  configurations with an accept-or-advance contract, the run from round 0
  halts within the summed budget with the loop's single verdict bit. It is
  the generic form of the Chapter-2 enumerator's proved private
  `enumLoop_run`, whose proof is the harvest template.
* `Turing.FinTM.exists_loopTM` is the **constructive combinator**: from a
  body machine whose startup and rounds are `Turing.Cfg.ofWords` seam
  contracts, there is one finite machine iterating the body under a fuel
  bound, with the exhaustion rejection and the total polynomial budget
  owned by the combinator. It is the generic form of the enumerator batch's
  admitted `enumMachine_contracts` — the statement that every fill batch
  died re-deriving concretely — turned into a once-and-for-all interface.

**Status: spec phase.** Both theorems and the seam helper are stated; the
proofs are the library fill's risk concentration (continuation budget
anticipated, frozen design §10). New Chapter-1 surface, flagged for the
shared infrastructure audit round.

## The round discipline

Round state is one word on the body's tape 0; every other body tape is
scratch, blank at both seam ends of a round (body-restores-scratch, frozen
design decision 9.2 — a body proves its own restore from its own invariant;
the generic clearing fallback via the visited-region bound of
`TCSlib.Complexity.TuringMachine.Sweep` is recorded in the design document).
A round either **accepts** — halts with the single verdict `[true]`,
nothing else ever emitted — or **advances** to the seam carrying the
stepped state word. The combinator caps the rounds at a fuel bound
computed from the input length only, rejecting with `[false]` on
exhaustion; acceptance within fuel is therefore the Boolean
`(List.range (R n + 1)).any …` of the abstract orbit, which is the shape
the Chapter-2 enumerator consumes.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2; the clocked-loop discipline is
  the folklore engine of the enumeration and diagonalization arguments,
  §2.1 / §3.1–3.2.)
-/

namespace Turing

/-- Round state on tape 0, scratch blank: the standard word assignment for
a loop body's seam configurations. -/
def stateWord (k : ℕ) (s : List Bool) : Fin k → List Bool :=
  fun i => if (i : ℕ) = 0 then s else []

/-- **The loop summation lemma** (spec, fill pending — the generic form of
the enumerator's proved `enumLoop_run`, which is the harvest template).
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
  sorry

end Turing

namespace Turing.FinTM

/-- **The loop combinator** (spec, fill pending — the generic form of the
enumerator batch's admitted `enumMachine_contracts`; the construction is
the library fill's risk concentration). Given a fuel machine and a body
machine with

* a **fuel** contract: `F` writes the round bound `R |x|` in binary within
  `T |x|` (an arbitrary `R : ℕ → ℕ` is not machine-evaluable, so the
  combinator must be handed its fuel; the enumerator's `2^w` and the
  split search's `n + 1` both have immediately writable bit patterns),
* a **startup** contract: from its genuine initial configuration on `x`
  the body reaches, within `T |x|`, the seam `Turing.Cfg.ofWords` carrying
  the initial state word `s0 x` on tape 0 (scratch blank), **without
  visiting the anchor state earlier**, and
* a **round** contract: from the seam carrying any state word `s` it
  either halts with the verdict `[true]` within `T |x|` (when `acceptF s`)
  or reaches the seam carrying `stepF s` within `T |x|` — in both cases
  **without re-entering the anchor state strictly between the seam and
  that endpoint**,

there is one finite machine that, on every input `x`, emits the single
verdict bit of the first `R |x| + 1` orbit points
`s0 x, stepF (s0 x), …, stepF^[R |x|] (s0 x)` — `[false]` when none
accepts (fuel exhaustion) — within a constant multiple of
`(T |x| + 1) · (R |x| + 2)`.

The two discipline clauses are load-bearing (maintainer pre-audit
adversarial pass, recorded for the shared infrastructure round): the
combinator's host detects round boundaries **as entries into the embedded
anchor state**, so a mid-round anchor visit would decrement the fuel
early and change the computed function; and without the fuel machine the
statement would assert a finite machine materializing an arbitrary
natural-number function of the input length.

**Proof sketch.** The combinator machine runs `F` relocated-and-captured
to lay the fuel word on a counter tape, rewinds, and embeds the body via
the W1 capture discipline of
`TCSlib.Complexity.TuringMachine.Build.Wrappers` (the body's verdict is
captured, never physically emitted until the end). On each entry into the
embedded anchor it decrements the binary counter in place; the borrow
discipline is amortized — total countdown cost over all rounds is linear
in `R |x|` plus the counter width, and exhaustion is detected exactly
when a borrow runs off the counter's end, which is what keeps the stated
budget at `(T + 1) · (R + 2)` rather than acquiring a logarithmic factor.
`Turing.loop_run` sums the seam family; acceptance surfaces as the
captured halt (`[true]`), and borrow-overflow emits the exhaustion
rejection (`[false]`). Phase overheads are absorbed into `c`. -/
theorem exists_loopTM (body F : FinTM Bool) (anchor : body.State)
    (stepF : List Bool → List Bool) (acceptF : List Bool → Bool)
    (s0 : List Bool → List Bool) (R T : ℕ → ℕ)
    (hF : F.ComputesFunInTime (fun x => Nat.bits (R x.length)) T)
    (hstart : ∀ x : List Bool, ∃ t ≤ T x.length,
      (∀ t' < t,
        (body.tm.runFrom (body.tm.initCfg x) t').state ≠ some anchor) ∧
      body.tm.runFrom (body.tm.initCfg x) t =
        Cfg.ofWords anchor (stateWord body.k (s0 x)))
    (hround : ∀ (x : List Bool) (s : List Bool),
      ∃ t ≤ T x.length,
        (∀ t', 0 < t' → t' < t →
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t').state
              ≠ some anchor) ∧
        if acceptF s then
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).state
              = none ∧
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).output
              = [true]
        else
          body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t =
              Cfg.ofWords anchor (stateWord body.k (stepF s))) :
    ∃ (E : FinTM Bool) (c : ℕ),
      E.ComputesFunInTime
        (fun x => [(List.range (R x.length + 1)).any
          fun i => acceptF (stepF^[i] (s0 x))])
        (fun n => c * (T n + 1) * (R n + 2)) := by
  sorry

end Turing.FinTM


## ===== TCSlib/Complexity/TuringMachine/Build/Primitives.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Nat.Bits
import TCSlib.Complexity.TuringMachine.Build.Convention
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
in the loop fill's toolkit.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2–§1.4: all entries are the
  folklore tape subroutines of the textbook's simulation arguments.)
-/

namespace Turing.FinTM

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
  sorry

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
  sorry

/-- **P5, polynomial evaluation, unary clause** (spec, fill pending —
harvest: the TMSAT batch's `polyUnaryTM`/`poly_unary_computes`, proved with
budget `(C + 5(e+1) + 4)·(n+1)^(e+1)`). The exact unary value of
`C·(n+1)^e` at the input length is computable within a constant multiple of
`(n+1)^(e+1)`. Its instances are also the exact-emission primitive the
reduction constructions consume (catalog entry P7, subsumed here).

**Construction sketch** (the harvest source's, verbatim shape): `e + 1`
nested unary loop tapes of side length `n + 1`, installed by one input
scan; the innermost loop emits `C` trues per box point; a recursive
invariant restores completed inner heads, with loop depth `r` costing at
most `(C + 1 + 5r)·(n+1)^r`. -/
theorem computesFunInTime_polyUnary (C e : ℕ) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun x => List.replicate (C * (x.length + 1) ^ e) true)
        fun n => c * (n + 1) ^ (e + 1) := by
  sorry

/-- **P5, polynomial evaluation, binary clause** (spec, fill pending —
harvest: the TMSAT batch's composition of the unary generator with the
binary length counter). The little-endian binary representation of
`C·(n+1)^e` at the input length is computable within a constant multiple
of `(n+1)^(e+1)`.

**Construction sketch.** The unary generator above composed with the
binary length counter of `computesFunInTime_lengthBits` through the public
buffered composition (`Turing.FinTM.computesFunInTime_comp`) — the harvest
source's exact route. -/
theorem computesFunInTime_polyBits (C e : ℕ) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => Nat.bits (C * (x.length + 1) ^ e))
        fun n => c * (n + 1) ^ (e + 1) := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- **P10, padding split search** (spec, fill pending — new; the bounded
search both padding constructions perform, realizable as a
`Turing.FinTM.exists_loopTM` instance over the polynomial-evaluation
primitive). Search for the unique `i ≤ |w|` with `i + C·(i+1)^e = |w|`
(`Turing.solveSplit`); on success emit the threaded split
`pairEncode (w.take i) (w.drop i)`, and on failure `[]` — rejection when
no length-equation solution exists is the audited obligation.

**Construction sketch.** A `Turing.FinTM.exists_loopTM` instance: round
state is the candidate `i` in binary; each round evaluates
`i + C·(i+1)^e` in unary and compares it to `|w|` by countdown; a hit
emits the split (doubled prefix, separator, suffix) and a fuel exhaustion
at `i = |w|` halts silently. Strict monotonicity makes the hit unique. -/
theorem computesFunInTime_splitSolve (C e : ℕ) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun w => match solveSplit C e w.length with
          | some i => pairEncode (w.take i) (w.drop i)
          | none => [])
        fun n => c * (n + 1) ^ (e + 2) := by
  sorry

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
  sorry

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


## ===== TCSlib/Complexity/TuringMachine/UniversalBlock.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.UniversalInterpreter

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Universal machine: the live table block

Completion of the live serialized-table block (epoch 3B2): exact record
selection over the serialized table, fixed-field reads, successor preparation,
record application, the resulting one-source-step block
`universal_live_block`, and the concrete checkpoint relation
`universalRelation` with its start/halt/output lemmas and the block budget
`universalBlockBound`. This file was split out mechanically from
`Universal.lean` at the epoch-3→4 merge; its contents are the epoch-3 fill,
batches B (WIP) and B2 (completion), unchanged. The head of the 3B2 section
(through `universalSkipDone`) lives at the end of `UniversalInterpreter.lean`,
whose module docstring records why. The public surface here exists to support
the epoch-4 `timed_universal` fill; its promotion is recorded at the epoch-3→4
merge (shared-lemma requests of the batch-B/B2 reports).

## Main definitions / Main results

* `Turing.universal_live_block` — one live source transition is realized by
  the interpreter within the code-dependent block bound.
* `Turing.universalRelation` — the concrete checkpoint relation between source
  and universal-machine configurations.
* `Turing.universalRelation_start` / `Turing.universalRelation_halt` /
  `Turing.universalRelation_output` — the relation's startup, halting, and
  output correspondence.
* `Turing.universalBlockBound` — the code-dependent block budget.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4.1, Theorem 1.9, pp. 20-21.)
-/

namespace Turing

open FinTM

/-- The unary tail of a skipped record costs exactly its serialized length.

**Proof sketch.** A true cell advances once without changing control. The false
terminator either finishes the request or decrements the bounded record counter.
Induction grows the consumed list prefix by one cell. -/
private lemma universal_skip_unary {x : List Bool}
    (base : Cfg 4 Bool UniversalControl x) (dest : Option (Fin 9)) (rem : Fin 9)
    (table : List Bool) (state : ℤ → Option Bool) (sp : ℤ)
    (n : ℕ) (l r : List Bool)
    (ht : table = l ++ List.replicate n true ++ false :: r) :
    universalInterpreter.runFrom
      (universalEvalCfg base (.skipUnary dest rem) table l.length state sp) (n + 1) =
    universalEvalCfg base
      (if h : rem.val = 0 then universalSkipDone dest
        else .skipFixed dest ⟨rem.val - 1, by omega⟩ 0)
      table (l.length + n + 1) state sp := by
  induction n generalizing l with
  | zero =>
    have hr : bufferTape table (l.length : ℤ) = some false := by
      rw [ht]; simpa using universal_table_read l r false
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    have he := universalEval_step base (.skipUnary dest rem)
      (if h : rem.val = 0 then universalSkipDone dest
        else .skipFixed dest ⟨rem.val - 1, by omega⟩ 0)
      table l.length state sp .pos 0 none
      (by
        by_cases h : rem.val = 0
        · have hz : rem = 0 := Fin.ext h
          simp [universalInterpreter, universalFour, hr, hz, universalSkipDone]
        · have hz : rem ≠ 0 := fun he => h (congrArg Fin.val he)
          simp [universalInterpreter, universalFour, hr, h, hz, universalSkipDone])
    simpa using he
  | succ n ih =>
    have hr : bufferTape table (l.length : ℤ) = some true := by
      rw [ht]; simpa [List.replicate_succ, List.append_assoc] using
        universal_table_read l (List.replicate n true ++ false :: r) true
    have he := universalEval_step base (.skipUnary dest rem) (.skipUnary dest rem)
      table l.length state sp .pos 0 none
      (by simp [universalInterpreter, universalFour, hr])
    rw [MultiTapeTM.runFrom_succ_eq_step, he]
    simp only [SignType.pos_eq_one, SignType.coe_one, SignType.coe_zero, add_zero]
    have ht' : table = (l ++ [true]) ++ List.replicate n true ++ false :: r := by
      simp [ht, List.replicate_succ, List.append_assoc]
    convert ih (l ++ [true]) ht' using 1 <;>
      simp [List.length_append, List.length_cons] <;> congr 1 <;> omega

/-- Skip one complete serialized record at exact cost.

**Proof sketch.** Concatenate the eight fixed-field transitions and the unary
tail scan. The record grammar identifies their total with the record length. -/
private lemma universal_skip_record {x : List Bool} {n : ℕ}
    (base : Cfg 4 Bool UniversalControl x) (dest : Option (Fin 9)) (rem : Fin 9)
    (table : List Bool) (state : ℤ → Option Bool) (sp : ℤ)
    (a : Action 1 Bool (Fin (n + 1))) (l r : List Bool)
    (ht : table = l ++ universalRecordBits a ++ r) :
    universalInterpreter.runFrom
      (universalEvalCfg base (.skipFixed dest rem 0) table l.length state sp)
      (universalRecordBits a).length =
    universalEvalCfg base
      (if h : rem.val = 0 then universalSkipDone dest
        else .skipFixed dest ⟨rem.val - 1, by omega⟩ 0)
      table (l.length + (universalRecordBits a).length) state sp := by
  have hlen : (universalRecordBits a).length = 8 + (universalNextOnes a.state + 1) := by
    rw [universal_record_shape]
    simp only [List.length_append, List.length_ofFn, List.length_replicate,
      List.length_cons, List.length_nil]
    omega
  have hfixed := universal_skip_fixed base dest rem table state sp 7 0 l.length rfl
  have hunary := universal_skip_unary base dest rem table state sp
    (universalNextOnes a.state) (l ++ List.ofFn (universalActionBits a)) r
    (by simpa [universal_record_shape, List.append_assoc] using ht)
  rw [hlen, MultiTapeTM.runFrom_add]
  have hf : universalInterpreter.runFrom
      (universalEvalCfg base (.skipFixed dest rem 0) table l.length state sp) 8 =
      universalEvalCfg base (.skipUnary dest rem) table (l.length + 8) state sp := by
    simpa only [Nat.cast_ofNat, Int.add_assoc, show (7 : ℤ) + 1 = 8 from rfl] using hfixed
  rw [hf]
  simpa only [List.length_append, List.length_ofFn, Nat.cast_add, Nat.cast_ofNat,
    Int.add_assoc] using hunary

/-- A bounded request skips precisely the specified nonempty list of records.

**Proof sketch.** Execute the first record and decrement the record counter.
The last record enters the requested continuation. Run addition adds the
serialized lengths, without an extra transition between consecutive records. -/
private lemma universal_skip_records {x : List Bool} {n : ℕ}
    (base : Cfg 4 Bool UniversalControl x) (dest : Option (Fin 9))
    (table : List Bool) (state : ℤ → Option Bool) (sp : ℤ)
    (as : List (Action 1 Bool (Fin (n + 1)))) (l r : List Bool)
    (rem : Fin 9) (hlen : as.length = rem.val + 1)
    (ht : table = l ++ as.flatMap universalRecordBits ++ r) :
    universalInterpreter.runFrom
      (universalEvalCfg base (.skipFixed dest rem 0) table l.length state sp)
      (as.flatMap universalRecordBits).length =
    universalEvalCfg base (universalSkipDone dest) table
      (l.length + (as.flatMap universalRecordBits).length) state sp := by
  induction as generalizing l rem with
  | nil => simp only [List.length_nil] at hlen; omega
  | cons a as ih =>
    have hv : rem.val = as.length := by simp only [List.length_cons] at hlen; omega
    have he := universal_skip_record base dest rem table state sp a l
      (as.flatMap universalRecordBits ++ r)
      (by simpa only [List.flatMap_cons, List.append_assoc] using ht)
    rw [List.flatMap_cons, List.length_append, MultiTapeTM.runFrom_add, he]
    cases as with
    | nil => simp [hv]
    | cons b bs =>
      have hn : rem.val ≠ 0 := by simp only [List.length_cons] at hv; omega
      rw [dif_neg hn]
      have htail : (b :: bs).length = rem.val - 1 + 1 := by
        simp only [List.length_cons] at hv ⊢
        omega
      have hi := ih (l ++ universalRecordBits a) ⟨rem.val - 1, by omega⟩ htail
        (by simpa only [List.flatMap_cons, List.append_assoc] using ht)
      convert hi using 1 <;>
        simp only [List.length_append, Nat.cast_add] <;> congr 1 <;> omega

/-- Each erased unary state symbol skips exactly nine transition records.

**Proof sketch.** Erase the first remaining state symbol, run the nine-record
scanner, and repeat for the remaining groups. At the final blank one transition
enters the state rewind. The state-window invariant records all erasures. -/
private lemma universal_skip_groups {x : List Bool} {n : ℕ}
    (base : Cfg 4 Bool UniversalControl x) (index : Fin 9) (table : List Bool)
    (groups : List (List (Action 1 Bool (Fin (n + 1)))))
    (hg : ∀ g ∈ groups, g.length = 9) (l r : List Bool) (j : ℕ)
    (ht : table = l ++ groups.flatMap (fun g => g.flatMap universalRecordBits) ++ r) :
    universalInterpreter.runFrom
      (universalEvalCfg base (.group index) table l.length
        (universalStateWindow j groups.length) (j + 1))
      (groups.length + (groups.flatMap (fun g => g.flatMap universalRecordBits)).length + 1) =
    universalEvalCfg base (.rewindState (some index)) table
      (l.length + (groups.flatMap (fun g => g.flatMap universalRecordBits)).length)
      (universalStateWindow (j + groups.length) 0) (j + groups.length + 1) := by
  induction groups generalizing l j with
  | nil =>
    simp only [List.length_nil, List.flatMap_nil, Nat.add_zero, Nat.zero_add,
      Nat.cast_zero, add_zero, MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    have he := universalEval_step base (.group index) (.rewindState (some index))
      table l.length (universalStateWindow j 0) (j + 1) 0 0 none
      (by simp [universalInterpreter, universalFour, universalStateWindow_end])
    simpa using he
  | cons g gs ih =>
    have hgl : g.length = 9 := hg g (by simp)
    have he := universalEval_step base (.group index) (.skipFixed (some index) 8 0)
      table l.length (universalStateWindow j (gs.length + 1)) (j + 1) 0 .pos (some none)
      (by simp [universalInterpreter, universalFour, universalStateWindow_read])
    have hskip := universal_skip_records base (some index) table
      (universalStateWindow (j + 1) gs.length) (j + 2) g l
      (gs.flatMap (fun g => g.flatMap universalRecordBits) ++ r) 8 hgl
      (by simpa [List.flatMap_cons, List.append_assoc] using ht)
    have hrest := ih (fun a ha => hg a (by simp [ha]))
      (l ++ g.flatMap universalRecordBits) (j + 1)
      (by simpa [List.flatMap_cons, List.append_assoc] using ht)
    have htime : (g :: gs).length +
        ((g :: gs).flatMap (fun g => g.flatMap universalRecordBits)).length + 1 =
        1 + (g.flatMap universalRecordBits).length +
          (gs.length + (gs.flatMap (fun g => g.flatMap universalRecordBits)).length + 1) := by
      simp only [List.length_cons, List.flatMap_cons, List.length_append]; omega
    rw [htime, MultiTapeTM.runFrom_add _ (1 + (g.flatMap universalRecordBits).length)
      (gs.length + (gs.flatMap (fun g => g.flatMap universalRecordBits)).length + 1),
      MultiTapeTM.runFrom_add _ 1 (g.flatMap universalRecordBits).length]
    simp only [List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step' (t := 0), MultiTapeTM.runFrom_zero, he]
    simp only [SignType.coe_zero, add_zero, SignType.pos_eq_one, SignType.coe_one,
      universalStateWindow_erase]
    rw [show (j : ℤ) + 1 + 1 = j + 2 by omega, hskip]
    simpa only [universalSkipDone, List.flatMap_cons, List.length_append, List.length_cons,
      Nat.cast_add, Nat.cast_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
      Int.add_assoc, Int.add_left_comm, Int.add_comm, Int.reduceAdd] using hrest

/-- Reading fixed action fields fills the finite eight-bit register exactly.

**Proof sketch.** The register already agrees with the record before the current
field. Read and update that field, maintaining agreement on a longer prefix.
After field seven the agreement covers every register entry. -/
private lemma universal_read_fixed {x : List Bool}
    (base : Cfg 4 Bool UniversalControl x) (table : List Bool)
    (state : ℤ → Option Bool) (sp : ℤ) (bits : Fin 8 → Bool) (l r : List Bool)
    (ht : table = l ++ List.ofFn bits ++ r) :
    ∀ (n : ℕ) (field : Fin 8) (old : Fin 8 → Bool), field.val + n = 7 →
      (∀ i : Fin 8, i.val < field.val → old i = bits i) →
      universalInterpreter.runFrom
        (universalEvalCfg base (.readAction field old) table
          (l.length + field.val) state sp) (n + 1) =
      universalEvalCfg base (.nextState bits) table (l.length + 8) state sp := by
  intro n
  induction n with
  | zero =>
    intro field old hf hknown
    have hv : field.val = 7 := by omega
    have hr : bufferTape table (l.length + field.val : ℤ) = some (bits field) := by
      rw [← Nat.cast_add, bufferTape_nat, ht, List.append_assoc,
        List.getElem?_append_right (by omega)]
      simp only [Nat.add_sub_cancel_left]
      rw [List.getElem?_append_left (by simpa using field.isLt), List.getElem?_ofFn]
      simp only [field.isLt, ↓reduceDIte]
    have hb : Function.update old field (bits field) = bits := by
      funext i
      by_cases hi : i = field
      · subst i; simp
      · rw [Function.update_of_ne hi]
        apply hknown
        have hn : i.val ≠ field.val := fun h => hi (Fin.ext h)
        omega
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    have he := universalEval_step base (.readAction field old) (.nextState bits)
      table (l.length + field.val) state sp .pos 0 none
      (by
        simp only [universalInterpreter, universalFour, ↓reduceIte, hr]
        simp only [hv, ↓reduceDIte, hb])
    rw [he]
    simp only [SignType.pos_eq_one, SignType.coe_one, SignType.coe_zero, add_zero]
    congr 1
    omega
  | succ n ih =>
    intro field old hf hknown
    have hv : field.val ≠ 7 := by omega
    have hr : bufferTape table (l.length + field.val : ℤ) = some (bits field) := by
      rw [← Nat.cast_add, bufferTape_nat, ht, List.append_assoc,
        List.getElem?_append_right (by omega)]
      simp only [Nat.add_sub_cancel_left]
      rw [List.getElem?_append_left (by simpa using field.isLt), List.getElem?_ofFn]
      simp only [field.isLt, ↓reduceDIte]
    have hb : ∀ i : Fin 8, i.val < field.val + 1 →
        Function.update old field (bits field) i = bits i := by
      intro i hi
      by_cases he : i = field
      · subst i; simp
      · rw [Function.update_of_ne he]
        apply hknown
        have hn : i.val ≠ field.val := fun h => he (Fin.ext h)
        omega
    have he := universalEval_step base (.readAction field old)
      (.readAction ⟨field.val + 1, by omega⟩ (Function.update old field (bits field)))
      table (l.length + field.val) state sp .pos 0 none
      (by simp [universalInterpreter, universalFour, hr, hv])
    rw [MultiTapeTM.runFrom_succ_eq_step, he]
    simp only [SignType.pos_eq_one, SignType.coe_one, SignType.coe_zero, add_zero]
    convert ih ⟨field.val + 1, by omega⟩ _ (by simp; omega) hb using 1 <;>
      simp only [Fin.val_mk, Nat.cast_add, Nat.cast_one] <;> congr 1 <;> omega

/-- Successor decoding, copying, and rewinding cost, before applying the action. -/
private def universalNextCost {n : ℕ} : Option (Fin (n + 1)) → ℕ
  | none => 1
  | some q => 2 * q.val + 4

/-- Decode the successor field and install its unary state at cursor one.

**Proof sketch.** A halting flag takes one transition. A live flag takes one,
copying its index takes `q+1`, and rewinding the new state takes `q+2`.
The table cursor stops on the field's false terminator in both cases. -/
private lemma universal_prepare_next {x : List Bool} {n : ℕ}
    (base : Cfg 4 Bool UniversalControl x) (table : List Bool) (bits : Fin 8 → Bool)
    (next : Option (Fin (n + 1))) (l r : List Bool)
    (ht : table = l ++ List.replicate (universalNextOnes next) true ++ false :: r) :
    universalInterpreter.runFrom
      (universalEvalCfg base (.nextState bits) table l.length (universalStateTape 0) 1)
      (universalNextCost next) =
    universalEvalCfg base (.applyRecord bits next.isNone) table
      (l.length + universalNextOnes next) (universalStateTape ((next.map Fin.val).getD 0)) 1 := by
  cases next with
  | none =>
    have hr : bufferTape table (l.length : ℤ) = some false := by
      rw [ht]; simpa [universalNextOnes] using universal_table_read l r false
    have he := universalEval_step base (.nextState bits) (.applyRecord bits true)
      table l.length (universalStateTape 0) 1 0 0 none
      (by simp [universalInterpreter, universalFour, hr])
    simpa [universalNextCost, universalNextOnes, MultiTapeTM.runFrom_succ_eq_step,
      MultiTapeTM.runFrom_zero] using he
  | some q =>
    have hr : bufferTape table (l.length : ℤ) = some true := by
      rw [ht]; simpa [universalNextOnes, List.replicate_succ, List.append_assoc] using
        universal_table_read l (List.replicate q.val true ++ false :: r) true
    have he := universalEval_step base (.nextState bits) (.copyState bits)
      table l.length (universalStateTape 0) 1 .pos 0 none
      (by simp [universalInterpreter, universalFour, hr])
    have hcopy := universal_unary_copy base (.copyState bits) (.rewindNext bits) 0 table
      (by intro inp work h; simp [universalInterpreter, h])
      (by intro inp work h; simp [universalInterpreter, h]) q.val 0 (l ++ [true]) r
      (by simpa [universalNextOnes, List.replicate_succ, List.append_assoc] using ht)
    have hrew := universal_state_rewind base (.rewindNext bits) (.applyRecord bits false)
      table (l.length + q.val + 1) (universalStateTape q.val)
      (universalStateTape_marker q.val).1 (universalStateTape_marker q.val).2
      (by intro inp work h; simp [universalInterpreter, h])
      (by intro inp work h; simp [universalInterpreter, h]) (q.val + 1)
    have hc : universalInterpreter.runFrom
        (universalEvalCfg base (.copyState bits) table (l.length + 1) (universalStateTape 0) 1)
        (q.val + 1) =
      universalEvalCfg base (.rewindNext bits) table (l.length + q.val + 1)
        (universalStateTape q.val) (q.val + 1) := by
      simpa [List.length_append, Int.add_assoc, Int.add_comm 1] using hcopy
    change universalInterpreter.runFrom _ (2 * q.val + 4) = _
    rw [show 2 * q.val + 4 = 1 + (q.val + 1) + (q.val + 2) by omega,
      MultiTapeTM.runFrom_add _ (1 + (q.val + 1)) (q.val + 2),
      MultiTapeTM.runFrom_add _ 1 (q.val + 1)]
    rw [MultiTapeTM.runFrom_succ_eq_step' (t := 0), MultiTapeTM.runFrom_zero, he]
    simp only [SignType.pos_eq_one, SignType.coe_one, SignType.coe_zero, add_zero]
    rw [hc]
    simpa only [universalNextOnes, Option.isNone_some, Option.map_some, Option.getD_some,
      Nat.cast_add, Nat.cast_one, Nat.add_assoc, Int.add_assoc] using hrew

/-- The nine actions for a state, in input-major, work-minor order. -/
private def universalActions (M : CodeTM) (q : Fin (M.numStates + 1)) :
    List (Action 1 Bool (Fin (M.numStates + 1))) :=
  ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
    ([none, some false, some true] : List (Option Bool)).map fun work =>
      M.tm.tr q inp (fun _ => work)

/-- Each state contributes nine records and the read offset selects its action. -/
private lemma universalActions_lookup (M : CodeTM) (q : Fin (M.numStates + 1))
    (inp work : Option Bool) :
    (universalActions M q).length = 9 ∧
    (universalActions M q)[(universalRecordIndex inp work).val]'(by
      change (universalRecordIndex inp work).val < 9
      exact (universalRecordIndex inp work).isLt) = M.tm.tr q inp (fun _ => work) := by
  constructor
  · rfl
  · rcases inp with _ | (_ | _) <;> rcases work with _ | (_ | _) <;> rfl

/-- Count prefix and initial-state field, excluding transition records. -/
private def universalHeader (M : CodeTM) : List Bool :=
  pairEncode (Nat.bits M.numStates) [] ++ List.replicate M.tm.q₀.val true ++ [false]

/-- Serialization as a header followed by the ordered lists of nine actions. -/
private lemma universal_serialization_actions (M : CodeTM) :
    M.serialize = universalHeader M ++
      ((List.finRange (M.numStates + 1)).map (universalActions M)).flatMap
        (fun g => g.flatMap universalRecordBits) := by
  have hr : M.serialize = pairEncode (Nat.bits M.numStates)
      (List.replicate M.tm.q₀.val true ++ false :: universalRecords M) := by
    unfold CodeTM.serialize
    change pairEncode _ ((List.replicate M.tm.q₀.val true ++ [false]) ++ _) = _
    rw [List.append_assoc]
    apply congrArg (pairEncode (Nat.bits M.numStates))
    apply congrArg (fun r : List Bool => List.replicate M.tm.q₀.val true ++ false :: r)
    unfold universalRecords
    dsimp only [List.append]
    congr 1
    funext q
    congr 1
    funext inp
    congr 1
    funext work
    generalize M.tm.tr q inp (fun _ => work) = a
    rcases a with ⟨di, tapes, out, next⟩
    have htapes : tapes = fun _ => tapes 0 := by
      funext i
      have hi : i = 0 := Fin.eq_zero i
      rw [hi]
    rw [htapes]
    generalize tapes 0 = entry
    rcases entry with ⟨write, dm⟩
    cases di <;> cases dm <;> rcases write with _ | (_ | (_ | _)) <;>
      rcases out with _ | (_ | _) <;> cases next <;> rfl
  rw [hr]
  simp [pairEncode, universalHeader, universalRecords, universalActions,
    List.flatMap_map, List.append_assoc]

/-- Decompose the canonical table at the action selected by state and reads.

**Proof sketch.** Split the increasing state enumeration at the source state,
and split its nine-entry list at the read offset. The two prefixes are exactly
the groups and records traversed by the controller. -/
private lemma universal_lookup_parts (M : CodeTM) (q : Fin (M.numStates + 1))
    (inp work : Option Bool) :
    ∃ (groups : List (List (Action 1 Bool (Fin (M.numStates + 1)))))
      (before : List (Action 1 Bool (Fin (M.numStates + 1)))) (after : List Bool),
      groups.length = q.val ∧ (∀ g ∈ groups, g.length = 9) ∧
      before.length = (universalRecordIndex inp work).val ∧
      M.serialize = universalHeader M ++
        groups.flatMap (fun g => g.flatMap universalRecordBits) ++
        before.flatMap universalRecordBits ++
        universalRecordBits (M.tm.tr q inp (fun _ => work)) ++ after := by
  let states := List.finRange (M.numStates + 1)
  let index := universalRecordIndex inp work
  let actions := universalActions M q
  have hq : q.val < states.length := by simpa [states] using q.isLt
  have hi : index.val < actions.length := by
    rw [(universalActions_lookup M q inp work).1]
    exact index.isLt
  have hs : states = states.take q.val ++ q :: states.drop (q.val + 1) := by
    have h := List.take_append_drop q.val states
    rw [List.drop_eq_getElem_cons hq] at h
    simpa [states] using h.symm
  have ha : actions = actions.take index.val ++
      M.tm.tr q inp (fun _ => work) :: actions.drop (index.val + 1) := by
    have h := List.take_append_drop index.val actions
    rw [List.drop_eq_getElem_cons hi, (universalActions_lookup M q inp work).2] at h
    exact h.symm
  refine ⟨(states.take q.val).map (universalActions M), actions.take index.val,
    (actions.drop (index.val + 1)).flatMap universalRecordBits ++
      ((states.drop (q.val + 1)).map (universalActions M)).flatMap
        (fun g => g.flatMap universalRecordBits), ?_, ?_, ?_, ?_⟩
  · simp only [List.length_map, List.length_take, Nat.min_eq_left (Nat.le_of_lt hq)]
  · intro g hg
    obtain ⟨s, _, rfl⟩ := List.mem_map.mp hg
    exact (universalActions_lookup M s none none).1
  · simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
    rfl
  · rw [universal_serialization_actions]
    change universalHeader M ++ (states.map (universalActions M)).flatMap _ = _
    conv_lhs => rw [hs, List.map_append, List.map_cons, List.flatMap_append,
      List.flatMap_cons]
    change universalHeader M ++ (_ ++ (actions.flatMap universalRecordBits ++ _)) = _
    conv_lhs => rw [ha]
    simp only [List.flatMap_append, List.flatMap_cons, List.append_assoc]

/-- Decoding the four fixed pairs recovers the source action fields. -/
private lemma universalActionBits_decode {n : ℕ} (a : Action 1 Bool (Fin (n + 1))) :
    universalSign (universalActionBits a 0) (universalActionBits a 1) = a.inputTape ∧
    universalWrite (universalActionBits a 2) (universalActionBits a 3) = (a.workTapes 0).1 ∧
    universalSign (universalActionBits a 4) (universalActionBits a 5) = (a.workTapes 0).2 ∧
    (if universalActionBits a 6 then some (universalActionBits a 7) else none) = a.output := by
  simp only [universalActionBits]
  constructor
  · cases a.inputTape <;> rfl
  constructor
  · rcases (a.workTapes 0).1 with _ | (_ | (_ | _)) <;> rfl
  constructor
  · cases (a.workTapes 0).2 <;> rfl
  · rcases a.output with _ | (_ | _) <;> rfl

/-- Applying the decoded record commutes with the complete source checkpoint.

**Proof sketch.** Decode the four fixed pairs. The virtual-input movement lemma
supplies both the physical head equality and the marker-head equality. Optional
writes and emissions then agree field by field; the newly installed unary state
is precisely the successor representation, including the halting case. -/
private lemma universal_apply_record (M : CodeTM) (α : List Bool) {x : List Bool}
    (src : Cfg 1 Bool (Fin (M.numStates + 1)) x) (oldp p : ℕ)
    (a : Action 1 Bool (Fin (M.numStates + 1))) :
    universalInterpreter.step
      (universalEvalCfg (universalSimulationCfg M α src oldp)
        (.applyRecord (universalActionBits a) a.state.isNone) M.serialize p
        (universalStateTape ((a.state.map Fin.val).getD 0)) 1) =
    universalSimulationCfg M α (a.apply src) p := by
  let base := universalSimulationCfg M α src oldp
  let cfg := universalEvalCfg base (.applyRecord (universalActionBits a) a.state.isNone)
    M.serialize p (universalStateTape ((a.state.map Fin.val).getD 0)) 1
  let d := virtualMove (decide (bufferTape [true] (src.inputPos.val : ℤ) ≠ some true))
    src.inputSymbol a.inputTape
  have hi : (if base.workTapeSymbols 3 = some true then none else base.inputSymbol) =
      src.inputSymbol := universalInput_read α src
  have hb := universalActionBits_decode a
  have htr : universalInterpreter.tr
      (.applyRecord (universalActionBits a) a.state.isNone) cfg.inputSymbol cfg.workTapeSymbols =
      (⟨d, universalFour (none, 0) (none, 0) (a.workTapes 0) (none, d), a.output,
        a.state.map (fun _ => .main)⟩ : Action 4 Bool UniversalControl) := by
    have hr3 : cfg.workTapeSymbols 3 = base.workTapeSymbols 3 := rfl
    have hip : cfg.inputSymbol = base.inputSymbol := rfl
    simp only [universalInterpreter, hr3, hip, hi, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2]
    change (⟨d, universalFour (none, 0) (none, 0) (a.workTapes 0) (none, d), a.output,
      if a.state.isNone then none else some .main⟩ : Action 4 Bool UniversalControl) = _
    cases a.state <;> rfl
  change (universalInterpreter.tr _ cfg.inputSymbol cfg.workTapeSymbols).apply cfg = _
  rw [htr]
  have hmove := universalInput_move α src a.inputTape
  refine Cfg.ext rfl hmove.1 ?_ ?_ rfl
  · funext i
    rcases i with ⟨i, hi⟩
    have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl <;> rfl
  · funext i
    rcases i with ⟨i, hi⟩
    have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl
    · exact add_zero _
    · exact add_zero _
    · rfl
    · exact hmove.2

/-- Select a record by destructive state counting and the bounded read offset.

**Proof sketch.** Skip the preceding state groups while erasing the unary state.
Rewind the erased state tape to one, then skip the read-offset prefix. An offset
of zero enters the action reader directly. The table scans cost their total
serialized length, and state administration costs twice the old index plus three. -/
private lemma universal_select {x : List Bool} {n : ℕ}
    (base : Cfg 4 Bool UniversalControl x) (index : Fin 9) (table : List Bool)
    (groups : List (List (Action 1 Bool (Fin (n + 1)))))
    (hg : ∀ g ∈ groups, g.length = 9)
    (before : List (Action 1 Bool (Fin (n + 1)))) (hb : before.length = index.val)
    (l r : List Bool)
    (ht : table = l ++ groups.flatMap (fun g => g.flatMap universalRecordBits) ++
      before.flatMap universalRecordBits ++ r) :
    universalInterpreter.runFrom
      (universalEvalCfg base (.group index) table l.length
        (universalStateTape groups.length) 1)
      (2 * groups.length + (groups.flatMap (fun g => g.flatMap universalRecordBits)).length +
        (before.flatMap universalRecordBits).length + 3) =
    universalEvalCfg base (.readAction 0 (fun _ => false)) table
      (l.length + (groups.flatMap (fun g => g.flatMap universalRecordBits)).length +
        (before.flatMap universalRecordBits).length) (universalStateTape 0) 1 := by
  let pg := groups.flatMap (fun g => g.flatMap universalRecordBits)
  let pb := before.flatMap universalRecordBits
  let next := if h : index.val = 0 then UniversalControl.readAction 0 (fun _ => false)
    else .skipFixed none ⟨index.val - 1, by omega⟩ 0
  have hgroup := universal_skip_groups base index table groups hg l (pb ++ r) 0
    (by simpa [pg, pb, List.append_assoc] using ht)
  have hgr : universalInterpreter.runFrom
      (universalEvalCfg base (.group index) table l.length (universalStateTape groups.length) 1)
      (groups.length + pg.length + 1) =
    universalEvalCfg base (.rewindState (some index)) table (l.length + pg.length)
      (universalStateTape 0) (groups.length + 1) := by
    simpa only [Nat.cast_zero, zero_add, universalStateWindow_empty,
      universalStateWindow_zero] using hgroup
  have hrew := universal_state_rewind base (.rewindState (some index)) next table
    (l.length + pg.length) (universalStateTape 0)
    (universalStateTape_marker 0).1 (universalStateTape_marker 0).2
    (by intro inp work h; simp [universalInterpreter, h, next])
    (by intro inp work h; simp [universalInterpreter, h]) (groups.length + 1)
  have hrw : universalInterpreter.runFrom
      (universalEvalCfg base (.rewindState (some index)) table (l.length + pg.length)
        (universalStateTape 0) (groups.length + 1)) (groups.length + 2) =
    universalEvalCfg base next table (l.length + pg.length) (universalStateTape 0) 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hrew
  have hskip : universalInterpreter.runFrom
      (universalEvalCfg base next table (l.length + pg.length) (universalStateTape 0) 1)
      pb.length = universalEvalCfg base (.readAction 0 (fun _ => false)) table
        (l.length + pg.length + pb.length) (universalStateTape 0) 1 := by
    by_cases hi : index.val = 0
    · have hz : before = [] := List.length_eq_zero_iff.mp (hb.trans hi)
      simp [next, hi, pb, hz]
    · have hh := universal_skip_records base none table (universalStateTape 0) 1
        before (l ++ pg) r ⟨index.val - 1, by omega⟩ (by simp only [Fin.val_mk]; omega)
        (by simpa [pg, pb, List.append_assoc] using ht)
      simpa only [next, dif_neg hi, universalSkipDone, List.length_append, Nat.cast_add]
        using hh
  change universalInterpreter.runFrom _ (2 * groups.length + pg.length + pb.length + 3) = _
  rw [show 2 * groups.length + pg.length + pb.length + 3 =
      (groups.length + pg.length + 1) + (groups.length + 2) + pb.length by omega,
    MultiTapeTM.runFrom_add _ ((groups.length + pg.length + 1) + (groups.length + 2)) pb.length,
    MultiTapeTM.runFrom_add _ (groups.length + pg.length + 1) (groups.length + 2),
    hgr, hrw, hskip]

/-- Concatenate two configuration equalities without unfolding either run. -/
private lemma universal_run_join {k : ℕ} {Q : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool Q) {a b c : Cfg k Bool Q x} {s t : ℕ}
    (hs : tm.runFrom a s = b) (ht : tm.runFrom b t = c) :
    tm.runFrom a (s + t) = c := by
  rw [MultiTapeTM.runFrom_add, hs, ht]

/-- One live source transition is realized by the existing finite interpreter.

**Proof sketch.** Read the virtual input and mirrored work symbol, rewind the
table, skip its count and initial-state fields, and select the source record.
Read its eight fixed bits, prepare its successor, and apply it. Concatenate the
exact runs. The old cursor, count prefix, and all skipped records are each
bounded by the serialization length; every source state index is below the
number of states. The resulting bound is `3L + 5N + 20`. -/
lemma universal_live_block (M : CodeTM) (α : List Bool) {x : List Bool}
    (src : Cfg 1 Bool (Fin (M.numStates + 1)) x) (p : ℕ)
    (hp : p ≤ M.serialize.length) (hs : src.state ≠ none) :
    ∃ d p', 1 ≤ d ∧ d ≤ 3 * M.serialize.length + 5 * (M.numStates + 1) + 20 ∧
      p' ≤ M.serialize.length ∧
      universalInterpreter.runFrom (universalSimulationCfg M α src p) d =
        universalSimulationCfg M α (M.tm.step src) p' := by
  cases hq : src.state with
  | none => exact False.elim (hs hq)
  | some q =>
    let base := universalSimulationCfg M α src p
    let index := universalRecordIndex src.inputSymbol (src.workTapeSymbols 0)
    let a := M.tm.tr q src.inputSymbol (fun _ => src.workTapeSymbols 0)
    obtain ⟨groups, before, after, hglen, hg, hblen, hparts⟩ :=
      universal_lookup_parts M q src.inputSymbol (src.workTapeSymbols 0)
    let pg := groups.flatMap (fun g => g.flatMap universalRecordBits)
    let pb := before.flatMap universalRecordBits
    let count := pairEncode (Nat.bits M.numStates) []
    let k := 2 * (Nat.bits M.numStates).length + 2
    let pre := universalHeader M ++ pg ++ pb
    let bits := universalActionBits a
    let p' := pre.length + 8 + universalNextOnes a.state
    let selectTime := 2 * q.val + pg.length + pb.length + 3
    let d := 1 + (p + 1) + k + (M.tm.q₀.val + 1) + selectTime + 8 +
      universalNextCost a.state + 1
    have hclen : count.length = k := by
      simpa [count, k] using universal_pair_length (Nat.bits M.numStates) []
    have hhlen : (universalHeader M).length = k + M.tm.q₀.val + 1 := by
      change (count ++ List.replicate M.tm.q₀.val true ++ [false]).length = _
      simp only [List.length_append, List.length_replicate, List.length_cons,
        List.length_nil, hclen]
    have hplen : pre.length = (universalHeader M).length + pg.length + pb.length := by
      simp only [pre, List.length_append]
    have ht : M.serialize = pre ++ universalRecordBits a ++ after := by
      simpa only [pre, pg, pb, a, List.append_assoc] using hparts
    have hcfg : base = universalEvalCfg base .main M.serialize p (universalStateTape q.val) 1 := by
      simp only [base, universalSimulationCfg, universalEvalCfg, hq,
        Option.map_some, Option.getD_some]
      rfl
    have hi : (if base.workTapeSymbols 3 = some true then none else base.inputSymbol) =
        src.inputSymbol := universalInput_read α src
    have hmain : universalInterpreter.runFrom base 1 =
        universalEvalCfg base (.rewindTable false index) M.serialize (p - 1)
          (universalStateTape q.val) 1 := by
      rw [MultiTapeTM.runFrom_succ_eq_step' (t := 0), MultiTapeTM.runFrom_zero]
      conv_lhs => rw [hcfg]
      have he := universalEval_step base .main (.rewindTable false index)
        M.serialize p (universalStateTape q.val) 1 .neg 0 none (by
          change universalAdmin (.rewindTable false (universalRecordIndex
            (if base.workTapeSymbols 3 = some true then none else base.inputSymbol)
            (base.workTapeSymbols 2))) .neg = _
          rw [hi]
          rfl)
      simpa only [SignType.neg_eq_neg_one, SignType.coe_neg_one, SignType.coe_zero,
        add_zero, sub_eq_add_neg] using he
    have hrew := universal_table_rewind base false index M.serialize
      (universalStateTape q.val) 1 p hp
    have hcount := universal_count_run base false index M.serialize
      (universalStateTape q.val) 1 (Nat.bits M.numStates) []
      (List.replicate M.tm.q₀.val true ++ false :: (pg ++ pb ++ universalRecordBits a ++ after))
      (by simpa [universalHeader, pairEncode, pg, pb, a, List.append_assoc] using hparts)
    have hc : universalInterpreter.runFrom
        (universalEvalCfg base (.countFirst false index) M.serialize 0 (universalStateTape q.val) 1) k =
      universalEvalCfg base (.initialSkip index) M.serialize k (universalStateTape q.val) 1 := by
      simpa only [Bool.false_eq_true, ↓reduceIte, List.length_nil, Nat.cast_zero,
        zero_add, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hcount
    have hinit := universal_initial_skip base index M.serialize (universalStateTape q.val) 1
      M.tm.q₀.val count (pg ++ pb ++ universalRecordBits a ++ after)
      (by simpa [count, universalHeader, pg, pb, a, List.append_assoc] using hparts)
    have hinit' : universalInterpreter.runFrom
        (universalEvalCfg base (.initialSkip index) M.serialize k (universalStateTape q.val) 1)
        (M.tm.q₀.val + 1) =
      universalEvalCfg base (.group index) M.serialize (universalHeader M).length
        (universalStateTape q.val) 1 := by
      simpa only [hclen, hhlen, Nat.cast_add, Nat.cast_one] using hinit
    have hselect := universal_select base index M.serialize groups hg before hblen
      (universalHeader M) (universalRecordBits a ++ after)
      (by simpa only [a, List.append_assoc] using hparts)
    have hsel : universalInterpreter.runFrom
        (universalEvalCfg base (.group index) M.serialize (universalHeader M).length
          (universalStateTape q.val) 1) selectTime =
      universalEvalCfg base (.readAction 0 (fun _ => false)) M.serialize pre.length
        (universalStateTape 0) 1 := by
      simpa only [hglen, hplen, Nat.cast_add] using hselect
    have hread := universal_read_fixed base M.serialize (universalStateTape 0) 1 bits pre
      (List.replicate (universalNextOnes a.state) true ++ false :: after)
      (by simpa [universal_record_shape, bits, List.append_assoc] using ht)
      7 0 (fun _ => false) rfl (by intro i hi; exact False.elim (Nat.not_lt_zero _ hi))
    have hrd : universalInterpreter.runFrom
        (universalEvalCfg base (.readAction 0 (fun _ => false)) M.serialize pre.length
          (universalStateTape 0) 1) 8 =
      universalEvalCfg base (.nextState bits) M.serialize (pre.length + 8)
        (universalStateTape 0) 1 := by
      simpa only [Fin.val_zero, Nat.cast_zero, add_zero] using hread
    have hnext := universal_prepare_next base M.serialize bits a.state
      (pre ++ List.ofFn bits) after
      (by simpa [universal_record_shape, bits, List.append_assoc] using ht)
    have hn : universalInterpreter.runFrom
        (universalEvalCfg base (.nextState bits) M.serialize (pre.length + 8)
          (universalStateTape 0) 1) (universalNextCost a.state) =
      universalEvalCfg base (.applyRecord bits a.state.isNone) M.serialize p'
        (universalStateTape ((a.state.map Fin.val).getD 0)) 1 := by
      simpa only [p', List.length_append, List.length_ofFn, Nat.cast_add, Nat.cast_ofNat] using hnext
    have happly : universalInterpreter.runFrom
        (universalEvalCfg base (.applyRecord bits a.state.isNone) M.serialize p'
          (universalStateTape ((a.state.map Fin.val).getD 0)) 1) 1 =
      universalSimulationCfg M α (a.apply src) p' := by
      rw [MultiTapeTM.runFrom_succ_eq_step' (t := 0), MultiTapeTM.runFrom_zero]
      exact universal_apply_record M α src p p' a
    have hrun := universal_run_join universalInterpreter
      (universal_run_join universalInterpreter
        (universal_run_join universalInterpreter
          (universal_run_join universalInterpreter
            (universal_run_join universalInterpreter
              (universal_run_join universalInterpreter
                (universal_run_join universalInterpreter hmain hrew) hc) hinit') hsel) hrd) hn) happly
    have hstep : M.tm.step src = a.apply src := by
      have hw : src.workTapeSymbols = fun _ : Fin 1 => src.workTapeSymbols 0 := by
        funext i
        rw [Fin.eq_zero i]
      simp only [MultiTapeTM.step, hq]
      rw [hw]
    have hlength : M.serialize.length = pre.length + 8 +
        universalNextOnes a.state + 1 + after.length := by
      rw [ht, universal_record_shape]
      simp only [List.length_append, List.length_ofFn, List.length_replicate,
        List.length_cons, List.length_nil]
      omega
    have hnextBound : universalNextCost a.state ≤ 2 * (M.numStates + 1) + 4 := by
      cases hnxt : a.state with
      | none => simp [universalNextCost]
      | some q' => have hq' := q'.isLt; simp only [universalNextCost]; omega
    have hqb := q.isLt
    have hq₀b := M.tm.q₀.isLt
    refine ⟨d, p', ?_, ?_, ?_, ?_⟩
    · dsimp only [d]; omega
    · dsimp only [d, selectTime]
      rw [hplen, hhlen] at hlength
      omega
    · dsimp only [p']; omega
    · rw [hstep]
      exact hrun

/-- Code-dependent block budget for the concrete interpreter. The intended
ledger is recorded in the delivery report; its realization is the remaining
concrete-step obligation in `universal`.

**Completion (epoch 3B2).** `universal_live_block` realizes that ledger and proves
this unchanged budget. Halting blocks cost `h+k+q₀+2q+P+16`; live successors
cost `h+k+q₀+2q+P+2q′+19`, with the symbols defined in the delivery report. -/
def universalBlockBound (c : EffectiveMachineCode) (α : List Bool) : ℕ :=
  3 * (c.decode α).serialize.length + 5 * ((c.decode α).numStates + 1) + 20

/-- Concrete checkpoint relation. The bound on the table cursor is needed for
a uniform rewind cost; inactive canonizer tapes remain existentially framed. -/
def universalRelation (c : EffectiveMachineCode) (α x : List Bool)
    (src : Cfg 1 Bool (Fin ((c.decode α).numStates + 1)) x)
    (dst : Cfg (universalTM c).k Bool (universalTM c).State (pairEncode α x)) : Prop :=
  ∃ (p : ℕ) (tapes : Fin (universalCanonTM c).k → ℤ → Option Bool)
    (heads : Fin (universalCanonTM c).k → ℤ), p ≤ (c.decode α).serialize.length ∧
    dst = rightCfg Sum.inr (universalSimulationCfg (c.decode α) α src p) tapes heads

/-- The canonical header ends inside its table buffer. -/
private lemma universal_header_bound (M : CodeTM) :
    2 * (Nat.bits M.numStates).length + 2 + M.tm.q₀.val + 1 ≤ M.serialize.length := by
  obtain ⟨records, hr⟩ := universal_serialization_header M
  rw [hr, universal_pair_length]
  simp only [List.length_append, List.length_replicate, List.length_cons]
  omega

/-- Full startup supplies the concrete checkpoint relation. -/
lemma universalRelation_start (c : EffectiveMachineCode) (α x : List Bool) :
    ∃ t, t ≤ universalStartupBound c α ∧
      universalRelation c α x ((c.decode α).tm.initCfg x)
        ((universalTM c).tm.runFrom ((universalTM c).tm.initCfg (pairEncode α x)) t) := by
  obtain ⟨t, tapes, heads, ht, he⟩ := universal_initialized c α x
  exact ⟨t, ht, _, tapes, heads, universal_header_bound _, he⟩

/-- The concrete checkpoint relation preserves halting in both directions. -/
lemma universalRelation_halt (c : EffectiveMachineCode) (α x : List Bool)
    (src : Cfg 1 Bool (Fin ((c.decode α).numStates + 1)) x)
    (dst : Cfg (universalTM c).k Bool (universalTM c).State (pairEncode α x))
    (h : universalRelation c α x src dst) : src.state = none ↔ dst.state = none := by
  obtain ⟨p, tapes, heads, -, rfl⟩ := h
  simp only [rightCfg, universalSimulationCfg, Option.map_eq_none_iff]

/-- The concrete checkpoint relation preserves the complete accumulated output. -/
lemma universalRelation_output (c : EffectiveMachineCode) (α x : List Bool)
    (src : Cfg 1 Bool (Fin ((c.decode α).numStates + 1)) x)
    (dst : Cfg (universalTM c).k Bool (universalTM c).State (pairEncode α x))
    (h : universalRelation c α x src dst) : src.output = dst.output := by
  obtain ⟨p, tapes, heads, -, rfl⟩ := h
  rfl

end Turing


## ===== TCSlib/Complexity/TuringMachine/Universal.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.UniversalBlock
import Mathlib.Tactic.FinCases

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The universal Turing machine

[AB09, §1.4.1 and Theorem 1.9, relaxed form]: there is a single machine `U` that,
given a code and an input, simulates the machine the code denotes — `U(x, α) =
M_α(x)` — with the simulation overhead depending only on the code, not on the input.

The construction lives in `UniversalStartup.lean` (prefix parsing,
canonization, and table capture), `UniversalInterpreter.lean` (the four-tape
table interpreter and the block-simulation assembly), and `UniversalBlock.lean`
(the live table block and the checkpoint relation), split out mechanically at
the epoch-3→4 merge. This file holds the three public statements together with
the epoch-4 private layer proving `timed_universal` (the deadline interpreter
`timedUniversalTM` and its lemmas; epoch-4 audit, finding 3: this sentence
previously claimed the file held only the public statements).

## Design and deviations from [AB09] (all shaped by the phase-3 audit)

* Statements are relative to an `Turing.EffectiveMachineCode`: the purely algebraic
  scheme admits noncomputable-meaning pathologies against which no universal machine
  exists (audit finding 1, Argument A).
* **Input layout is `pairEncode α x` — code first, input second** — deviating from
  [AB09]'s `⟨x, α⟩`: with the input first, the startup cost of reaching the code
  grows with `|x|` and the stated bounds are false (audit finding 2, Argument B).
  With the code first, startup (parsing and canonizing `α`) costs a constant
  depending only on `α`, absorbed into `C`, and the simulated input head walks the
  verbatim `x` region on demand.
* `universal` is the **all-string evaluator** [AB09's `U(x, α) = M_α(x)`, p. 20]:
  it covers every `α` through `c.decode` (padded and fallback representations
  included), and it carries **both directions** — the forward time bound, and the
  converse that any *completed* output of `U` (output on halting; intermediate
  emissions of a non-halting run are unconstrained) is a completed output of the
  simulated machine, so divergence is preserved (round-1 finding 3; round-2
  Argument C).
* The constant `C` depends on the **representation** `α`, a documented weakening of
  [AB09]'s machine-dependent constant that is *necessary* at this generality: an
  effective scheme can reserve arbitrarily long identical-prefix representations of
  two fixed machines, defeating any constant that factors through `c.decode α`
  (round-2 audit, finding 6 and Argument E). Recovering the book's dependence would
  require further representation assumptions.
* **The core bound is linear**, `C · (t + 1)`: coded machines are already in
  one-work-tape binary normal form, so `U` pays a constant per simulated step.
  [AB09]'s relaxed quadratic bound reappears in `universal_quadratic`, where an
  *arbitrary* binary machine is first normal-formed ([AB09, Claims 1.5-1.6]); that
  corollary is stated — and labeled — at the level of **total function computation**
  (audit finding 4), the machine-level partial statement being `universal` itself.
  The `O(T log T)` sharpening ([AB09, §1.7]) is the phase-5 stretch goal.
* `timed_universal` outputs `true :: output` on success and `[false]` on timeout, a
  concrete rendering of [AB09]'s "special failure symbol" (§1.4.1); its budget is
  quadratic (binary clock maintenance). The deadline convention: halting is checked
  after every simulated transition *including the `t`-th*, so a machine first
  halting exactly at the deadline is a success; at budget `0` no initialized machine
  has halted, and the timeout branch applies (audit finding 6).

## Main results

* `Turing.universal` — the all-string evaluator [AB09, Theorem 1.9 core].
* `Turing.universal_quadratic` — the relaxed quadratic form for total functions of
  arbitrary binary machines [AB09, Theorem 1.9 as proved in §1.4.1].
* `Turing.timed_universal` — the time-bounded universal machine [AB09, §1.4.1].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4.1, Theorem 1.9, pp. 20-21; Figure 1.6.)
-/

namespace Turing

open FinTM

/-- **The universal machine as an all-string evaluator** [AB09, Theorem 1.9]: for any
effective scheme there is a single machine `U` such that for every string `α` there
is a constant `C` (depending on `α`, absorbing its decoding) with, for every input
`x`: whenever the machine `α` denotes halts on `x` within `t` steps with `output`,
`U` on `pairEncode α x` halts with the same output within `C · (t + 1)` steps —
and conversely every *completed* output of `U` on `pairEncode α x` (its output on
halting) is a completed output of the denoted machine on `x`, so divergence is
preserved.

**Proof sketch** (after [AB09, Figure 1.6], adapted to the code-first layout).
Startup: `U` runs the scheme's `canonizer` on the doubled-bit `α`-region (via the
composition combinators), leaving the fixed serialization of `M := c.decode α` — the
state count, initial state, and table — on a *table* work tape, and writes the
initial state on a *state* tape; cost `O(canonizerTime |α| + |α| + 1)`, a constant
for fixed `α`, absorbed into `C`. `U`'s input head then parks at the start of the
verbatim `x` region, and a *work* tape mirrors `M`'s work tape. **The simulated
input's left boundary must be emulated explicitly** (round-2 audit, finding 3): the
cell physically left of the `x` region is the pairing delimiter's `true`, not a
blank, so `U` keeps a marker on a spare work tape whose head tracks the virtual
input position — at virtual position zero it supplies a blank read and suppresses
further outward moves (mirroring `moveInputPos`'s clamp), and for empty `x` the
virtual head starts at the right boundary blank adjacent to that marked left
boundary. Each simulated step: read the mirrored work symbol and the input symbol
under the simulated head (the input head moves one cell per simulated move — `x` is
verbatim, no doubling — with the boundary marker moved in lockstep), scan the table
for the record matching (state, input read, work read) — at most the table length,
constant in `t` — and apply it: update the state tape, write/move on the mirrored
tape, emit `M`'s emission verbatim. Forward bound: `C · (t + 1)`. Converse:
`U` emits only what the simulation emits and halts only when the simulation halts,
so any completed output of `U` is an output of `M` on `x`. -/
theorem universal (c : EffectiveMachineCode) :
    ∃ U : FinTM Bool, ∀ α : List Bool, ∃ C : ℕ, ∀ x : List Bool,
      (∀ (output : List Bool) (t : ℕ),
        (c.decode α).toFinTM.ComputesInTime x output t →
        U.ComputesInTime (pairEncode α x) output (C * (t + 1))) ∧
      (∀ output : List Bool,
        (∃ t, U.ComputesInTime (pairEncode α x) output t) →
        ∃ t, (c.decode α).toFinTM.ComputesInTime x output t) := by
  refine ⟨universalTM c, ?_⟩
  apply universal_from_blocks c (universalTM c) (universalStartupBound c)
    (universalBlockBound c) (universalRelation c)
  · exact universalRelation_start c
  · intro α x src dst h
    by_cases hs : src.state = none
    · have hu := (universalRelation_halt c α x src dst h).mp hs
      refine ⟨1, le_refl _, ?_, ?_⟩
      · simp only [universalBlockBound]
        omega
      · rw [MultiTapeTM.step_of_halt hs, MultiTapeTM.runFrom_of_halt _ hu]
        exact h
    · -- Remaining obligation: execute one complete serialized-table lookup and
      -- application block for a live source, with positive duration and the
      -- code-dependent bound. Startup, boundary motion, and the two-clause
      -- assembly are proved above; this concrete block proof remains open.
      -- Completion (epoch 3B2): lift the proved interpreter block through capture.
      obtain ⟨p, tapes, heads, hp, rfl⟩ := h
      obtain ⟨d, p', hd, hB, hp', he⟩ := universal_live_block (c.decode α) α src p hp hs
      refine ⟨d, hd, hB, p', tapes, heads, hp', ?_⟩
      change (universalCaptureTM (universalCanonTM c) universalInterpreter).tm.runFrom
        (rightCfg Sum.inr (universalSimulationCfg (c.decode α) α src p) tapes heads) d = _
      rw [universalCapture_interpreter_run, he]
  · exact universalRelation_halt c
  · exact universalRelation_output c

/-- **The relaxed quadratic form, for total functions** [AB09, Theorem 1.9 as proved
in §1.4.1 — labeled per audit finding 4: this is the total-function corollary; the
machine-level, partial-computation statement is `Turing.universal`]: every binary
machine computing a total function `f` within `T` has a code `α` such that the
*same* universal machine computes `f x` from `pairEncode α x` within
`C · (T |x| + 1)²`.

**Proof sketch.** Normal-form the machine with `Turing.FinTM.one_work_tape_binary`
(quadratic, [AB09, Claims 1.5-1.6]), relabel its states with `Turing.exists_codeTM`,
take `α := c.encode` of that coded machine (so `c.decode α` is that machine, by
`MachineCode.decode_encode`), and apply the forward direction of `Turing.universal`;
the constants compose as `C_U · (c₁ · (T n + 1)² + 1) ≤ C · (T n + 1)²`. -/
theorem universal_quadratic (c : EffectiveMachineCode) :
    ∃ U : FinTM Bool, ∀ (M₀ : FinTM Bool) (f : List Bool → List Bool) (T : ℕ → ℕ),
      M₀.ComputesFunInTime f T →
      ∃ (α : List Bool) (C : ℕ), ∀ x : List Bool,
        U.ComputesInTime (pairEncode α x) (f x) (C * (T x.length + 1) ^ 2) := by
  obtain ⟨U, hU⟩ := universal c
  refine ⟨U, ?_⟩
  intro M₀ f T hM
  obtain ⟨M₁, c₁, hk, h₁⟩ := FinTM.one_work_tape_binary M₀ f T hM
  obtain ⟨N, hN⟩ := exists_codeTM M₁ hk
  let α := c.encode N
  obtain ⟨C_U, hCU⟩ := hU α
  refine ⟨α, C_U * (c₁ + 1), fun x => ?_⟩
  have hcoded : (c.decode α).toFinTM.ComputesInTime x (f x)
      (c₁ * (T x.length + 1) ^ 2) := by
    rw [show c.decode α = N from c.toMachineCode.decode_encode N]
    exact (hN x (f x) _).2 (h₁ x)
  apply ((hCU x).1 (f x) _ hcoded).mono
  have hpow : 0 < (T x.length + 1) ^ 2 := Nat.pow_pos (Nat.succ_pos _)
  calc C_U * (c₁ * (T x.length + 1) ^ 2 + 1)
      ≤ C_U * (c₁ * (T x.length + 1) ^ 2 + (T x.length + 1) ^ 2) :=
        Nat.mul_le_mul (le_refl C_U) (Nat.add_le_add_left hpow _)
    _ = C_U * (c₁ + 1) * (T x.length + 1) ^ 2 := by ring

/-! ### Epoch 4: private stopped-interpreter infrastructure

**Implementation note (epoch 4).** The private construction below implements the
frozen timed-machine sketch. A prefix parser saves the clock and canonizes only
the code. The interpreter borrows before each source transition and routes source
halting to a buffered-output phase. The final induction checks the successor's
halting state before requiring any further clock credit.

The stop controller follows the audited interpreter until an action is ready.
Its next transition then halts without applying that action. A live endpoint
therefore certifies that no earlier action was applied. This permits replay
through the clock/buffer wrapper using the existing table representation.
-/

/-- Stop immediately before applying a selected source record. -/
private def timedCutInterpreter : MultiTapeTM 4 Bool UniversalControl where
  q₀ := universalInterpreter.q₀
  tr := fun q inp ws => match q with
    | .applyRecord _ _ => ⟨0, fun _ => (none, 0), none, none⟩
    | _ => universalInterpreter.tr q inp ws

/-- The four administrative reads. -/
private lemma timedCut_Eval_reads {x : List Bool} (base : Cfg 4 Bool UniversalControl x)
    (q : UniversalControl) (table : List Bool) (tp : ℤ)
    (state : ℤ → Option Bool) (sp : ℤ) :
    (universalEvalCfg base q table tp state sp).workTapeSymbols =
      universalFour (bufferTape table tp) (state sp)
        (base.workTapeSymbols 2) (base.workTapeSymbols 3) := by
  funext i
  rcases i with ⟨i, hi⟩
  have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases h with rfl | rfl | rfl | rfl <;> rfl

/-- One administrative action changes only the two designated tape cursors and
optionally the state-tape cell. -/
private lemma timedCut_Admin_apply {x : List Bool} (base : Cfg 4 Bool UniversalControl x)
    (q q' : UniversalControl) (table : List Bool) (tp : ℤ)
    (state : ℤ → Option Bool) (sp : ℤ) (dt ds : SignType) (w : Option (Option Bool)) :
    (universalAdmin q' dt (w, ds)).apply (universalEvalCfg base q table tp state sp) =
      universalEvalCfg base q' table (tp + (dt : ℤ))
        (match w with | none => state | some b => Function.update state sp b)
        (sp + (ds : ℤ)) := by
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ (List.append_nil _)
  · funext i
    rcases i with ⟨i, hi⟩
    have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl <;> cases w <;> rfl
  · funext i
    rcases i with ⟨i, hi⟩
    have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl <;>
      first | rfl | exact add_zero _

/-- Read-based administrative step rule. -/
private lemma timedCut_Eval_step {x : List Bool} (base : Cfg 4 Bool UniversalControl x)
    (q q' : UniversalControl) (table : List Bool) (tp : ℤ)
    (state : ℤ → Option Bool) (sp : ℤ) (dt ds : SignType) (w : Option (Option Bool))
    (h : timedCutInterpreter.tr q base.inputSymbol
      (universalFour (bufferTape table tp) (state sp)
        (base.workTapeSymbols 2) (base.workTapeSymbols 3)) = universalAdmin q' dt (w, ds)) :
    timedCutInterpreter.step (universalEvalCfg base q table tp state sp) =
      universalEvalCfg base q' table (tp + (dt : ℤ))
        (match w with | none => state | some b => Function.update state sp b)
        (sp + (ds : ℤ)) := by
  change (timedCutInterpreter.tr q _ _).apply _ = _
  rw [timedCut_Eval_reads]
  change (timedCutInterpreter.tr q base.inputSymbol _).apply _ = _
  conv_lhs => rw [h]
  cases w <;> exact timedCut_Admin_apply base q q' table tp state sp dt ds _

/-- Look up the first unconsumed cell of a contiguous table. -/
private lemma timedCut_table_read (l r : List Bool) (b : Bool) :
    bufferTape (l ++ b :: r) (l.length : ℤ) = some b := by
  rw [bufferTape_nat, List.getElem?_append_right (le_refl _)]
  simp

/-- Exact-cost table rewind. The initial unconditional left move has put the
cursor at `j-1`, where `j` is at most the table length.

**Proof sketch.** At `j=0`, the cursor is the left blank and one move right
starts the count parser. At positive `j`, a nonblank table cell is read and the
cursor decreases once. Induction accounts for every transition and leaves all
other tapes, physical input, and accumulated output unchanged. -/
private lemma timedCut_table_rewind {x : List Bool}
    (base : Cfg 4 Bool UniversalControl x) (initial : Bool) (index : Fin 9)
    (table : List Bool) (state : ℤ → Option Bool) (sp : ℤ) :
    ∀ j, j ≤ table.length →
      timedCutInterpreter.runFrom
        (universalEvalCfg base (.rewindTable initial index) table (j - 1) state sp) (j + 1) =
      universalEvalCfg base (.countFirst initial index) table 0 state sp := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    have he := timedCut_Eval_step base (.rewindTable initial index) (.countFirst initial index)
      table (-1) state sp .pos 0 none (by simp [timedCutInterpreter, universalInterpreter, universalFour])
    simpa using he
  | succ j ih =>
    intro hj
    have hr : bufferTape table (j : ℤ) = some table[j] := by
      rw [bufferTape_nat, List.getElem?_eq_getElem (by omega)]
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have he := timedCut_Eval_step base (.rewindTable initial index) (.rewindTable initial index)
      table (j : ℤ) state sp .neg 0 none (by simp [timedCutInterpreter, universalInterpreter, universalFour, hr])
    have hh : (j + 1 : ℤ) - 1 = j := by omega
    simp only [Nat.cast_add, Nat.cast_one, hh]
    rw [he]
    simpa using ih (by omega)

/-- Skip an arbitrary doubled, delimited count field at exact cost. No binary
arithmetic on its value is needed by the interpreter.

**Proof sketch.** Each doubled pair returns the parser to its first-half state
in two transitions. The terminal aligned `false,true` pair selects the initial
state copier or skipper. Induct on the count-bit list while growing the consumed
prefix, so table lookup is justified at every cursor position. -/
private lemma timedCut_count_run {x : List Bool}
    (base : Cfg 4 Bool UniversalControl x) (initial : Bool) (index : Fin 9)
    (table : List Bool) (state : ℤ → Option Bool) (sp : ℤ)
    (bits : List Bool) (l r : List Bool)
    (ht : table = l ++ (bits.flatMap fun b => [b, b]) ++ [false, true] ++ r) :
    timedCutInterpreter.runFrom
      (universalEvalCfg base (.countFirst initial index) table l.length state sp)
      (2 * bits.length + 2) =
    universalEvalCfg base (if initial then .initialCopy else .initialSkip index) table
      (l.length + 2 * bits.length + 2) state sp := by
  induction bits generalizing l with
  | nil =>
    have hr0 : bufferTape table (l.length : ℤ) = some false := by
      rw [ht]; simpa using timedCut_table_read l (true :: r) false
    have hr1 : bufferTape table (l.length + 1 : ℤ) = some true := by
      have h' : table = (l ++ [false]) ++ true :: r := by simp [ht, List.append_assoc]
      have h := timedCut_table_read (l ++ [false]) r true
      simpa [h', List.length_append] using h
    have he0 := timedCut_Eval_step base (.countFirst initial index)
      (.countSecond initial index false) table l.length state sp .pos 0 none
      (by simp [timedCutInterpreter, universalInterpreter, universalFour, hr0])
    have he1 := timedCut_Eval_step base (.countSecond initial index false)
      (if initial then .initialCopy else .initialSkip index)
      table (l.length + 1) state sp .pos 0 none
      (by simp [timedCutInterpreter, universalInterpreter, universalFour, hr1])
    change timedCutInterpreter.runFrom _ (0 + 1 + 1) = _
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step',
      MultiTapeTM.runFrom_zero, he0]
    simp only [SignType.pos_eq_one, SignType.coe_one, SignType.coe_zero, add_zero]
    rw [he1]
    simp only [SignType.pos_eq_one, SignType.coe_one, SignType.coe_zero, add_zero,
      List.length_nil, Nat.cast_zero, mul_zero]
    congr 1
  | cons b bits ih =>
    have hr0 : bufferTape table (l.length : ℤ) = some b := by
      rw [ht]
      simpa [List.flatMap_cons, List.append_assoc] using
        timedCut_table_read l (b :: ((bits.flatMap fun b => [b, b]) ++ [false, true] ++ r)) b
    have hr1 : bufferTape table (l.length + 1 : ℤ) = some b := by
      have h' : table = (l ++ [b]) ++ b :: ((bits.flatMap fun b => [b, b]) ++ [false, true] ++ r) := by
        simp [ht, List.append_assoc]
      have h := timedCut_table_read (l ++ [b]) ((bits.flatMap fun b => [b, b]) ++ [false, true] ++ r) b
      simpa [h', List.length_append] using h
    have he0 := timedCut_Eval_step base (.countFirst initial index)
      (.countSecond initial index b) table l.length state sp .pos 0 none
      (by simp [timedCutInterpreter, universalInterpreter, universalFour, hr0])
    have he1 := timedCut_Eval_step base (.countSecond initial index b)
      (.countFirst initial index) table (l.length + 1) state sp .pos 0 none
      (by simp [timedCutInterpreter, universalInterpreter, universalFour, hr1])
    have h' : table = (l ++ [b, b]) ++ (bits.flatMap fun b => [b, b]) ++ [false, true] ++ r := by
      simp [ht, List.append_assoc]
    have hi := ih (l ++ [b, b]) h'
    conv_lhs => rw [show 2 * (b :: bits).length + 2 =
      1 + 1 + (2 * bits.length + 2) by simp; omega]
    rw [MultiTapeTM.runFrom_add]
    change timedCutInterpreter.runFrom
      (timedCutInterpreter.step (timedCutInterpreter.step _)) _ = _
    rw [he0]
    simp only [SignType.pos_eq_one, SignType.coe_one, SignType.coe_zero, add_zero]
    rw [he1]
    simp only [SignType.pos_eq_one, SignType.coe_one, SignType.coe_zero, add_zero]
    convert hi using 1 <;> simp [List.length_append, List.length_cons] <;> congr 1 <;> omega


/-- Appending a next-state unary symbol extends the intact state tape. -/
private lemma timedCut_StateTape_append (n : ℕ) :
    Function.update (universalStateTape n) (n + 1 : ℤ) (some true) =
      universalStateTape (n + 1) := by
  have h := bufferTape_append (false :: List.replicate n true) true
  simpa only [universalStateTape, List.replicate_add, List.replicate_one,
    List.cons_append, List.length_cons, List.length_replicate,
    Nat.cast_add, Nat.cast_one] using h.symm

/-- An intact unary state reads its blank immediately after the last symbol. -/
private lemma timedCut_StateTape_end (n : ℕ) :
    universalStateTape n (n + 1) = none := by
  simp [universalStateTape, bufferTape]

/-- A marker-directed state rewind has exact cost equal to cursor plus one.
Its premise is deliberately independent of whether traversed cells are erased
blanks or retained unary ones.

**Proof sketch.** Each positive cursor sees a non-marker cell and moves left.
At zero the permanent marker causes one right move and transfer to the supplied
continuation. The entire tape, input head, and real output stay unchanged. -/
private lemma timedCut_state_rewind {x : List Bool}
    (base : Cfg 4 Bool UniversalControl x) (q q' : UniversalControl)
    (table : List Bool) (tp : ℤ) (state : ℤ → Option Bool)
    (hzero : state 0 = some false)
    (hother : ∀ j : ℕ, 0 < j → state j ≠ some false)
    (hstop : ∀ inp work, work 1 = some false →
      timedCutInterpreter.tr q inp work = universalAdmin q' 0 (none, .pos))
    (hscan : ∀ inp work, work 1 ≠ some false →
      timedCutInterpreter.tr q inp work = universalAdmin q 0 (none, .neg)) :
    ∀ j : ℕ, timedCutInterpreter.runFrom
      (universalEvalCfg base q table tp state j) (j + 1) =
      universalEvalCfg base q' table tp state 1 := by
  intro j
  induction j with
  | zero =>
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    have he := timedCut_Eval_step base q q' table tp state 0 0 .pos none
      (hstop _ _ (by simpa [universalFour] using hzero))
    simpa using he
  | succ j ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have he := timedCut_Eval_step base q q table tp state (j + 1) 0 .neg none
      (hscan _ _ (by simpa [universalFour] using hother (j + 1) (by omega)))
    rw [show ((j + 1 : ℕ) : ℤ) = (j : ℤ) + 1 by omega, he]
    simpa using ih

/-- The table's initial-state unary field can be skipped at exact cost.

**Proof sketch.** Induct on the number of unary ones. Each one advances the table
cursor; the final zero advances once more and enters record-group selection. -/
private lemma timedCut_initial_skip {x : List Bool}
    (base : Cfg 4 Bool UniversalControl x) (index : Fin 9)
    (table : List Bool) (state : ℤ → Option Bool) (sp : ℤ)
    (n : ℕ) (l r : List Bool)
    (ht : table = l ++ List.replicate n true ++ false :: r) :
    timedCutInterpreter.runFrom
      (universalEvalCfg base (.initialSkip index) table l.length state sp) (n + 1) =
      universalEvalCfg base (.group index) table (l.length + n + 1) state sp := by
  induction n generalizing l with
  | zero =>
    have hr : bufferTape table (l.length : ℤ) = some false := by
      rw [ht]; simpa using timedCut_table_read l r false
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    have he := timedCut_Eval_step base (.initialSkip index) (.group index)
      table l.length state sp .pos 0 none (by simp [timedCutInterpreter, universalInterpreter, universalFour, hr])
    simpa using he
  | succ n ih =>
    have hr : bufferTape table (l.length : ℤ) = some true := by
      rw [ht]; simpa [List.replicate_succ, List.append_assoc] using
        timedCut_table_read l (List.replicate n true ++ false :: r) true
    have he := timedCut_Eval_step base (.initialSkip index) (.initialSkip index)
      table l.length state sp .pos 0 none (by simp [timedCutInterpreter, universalInterpreter, universalFour, hr])
    rw [MultiTapeTM.runFrom_succ_eq_step, he]
    simp only [SignType.pos_eq_one, SignType.coe_one, SignType.coe_zero, add_zero]
    have ht' : table = (l ++ [true]) ++ List.replicate n true ++ false :: r := by
      simp [ht, List.replicate_succ, List.append_assoc]
    have hi := ih (l ++ [true]) ht'
    convert hi using 1 <;> simp [List.length_append, List.length_cons] <;> congr 1 <;> omega



/-- Copy a unary table field onto the state tape. This single gadget serves both
initial-state extraction and live successor-state replacement.

**Proof sketch.** A `true` table cell appends one unary state symbol and moves both
cursors right. A terminal `false` switches to the supplied continuation, with its
specified table movement. Induction preserves exact table/state positions and
accounts for all `n+1` transitions. -/
private lemma timedCut_unary_copy {x : List Bool}
    (base : Cfg 4 Bool UniversalControl x) (q q' : UniversalControl) (doneMove : SignType)
    (table : List Bool)
    (htrue : ∀ inp work, work 0 = some true →
      timedCutInterpreter.tr q inp work = universalAdmin q .pos (some (some true), .pos))
    (hfalse : ∀ inp work, work 0 = some false →
      timedCutInterpreter.tr q inp work = universalAdmin q' doneMove (none, 0))
    (n j : ℕ) (l r : List Bool)
    (ht : table = l ++ List.replicate n true ++ false :: r) :
    timedCutInterpreter.runFrom
      (universalEvalCfg base q table l.length (universalStateTape j) (j + 1)) (n + 1) =
      universalEvalCfg base q' table (l.length + n + (doneMove : ℤ))
        (universalStateTape (j + n)) (j + n + 1) := by
  induction n generalizing l j with
  | zero =>
    have hr : bufferTape table (l.length : ℤ) = some false := by
      rw [ht]; simpa using timedCut_table_read l r false
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    have he := timedCut_Eval_step base q q' table l.length (universalStateTape j) (j + 1)
      doneMove 0 none (hfalse _ _ (by simp [universalFour, hr]))
    simpa using he
  | succ n ih =>
    have hr : bufferTape table (l.length : ℤ) = some true := by
      rw [ht]; simpa [List.replicate_succ, List.append_assoc] using
        timedCut_table_read l (List.replicate n true ++ false :: r) true
    have he := timedCut_Eval_step base q q table l.length (universalStateTape j) (j + 1)
      .pos .pos (some (some true)) (htrue _ _ (by simp [universalFour, hr]))
    rw [MultiTapeTM.runFrom_succ_eq_step, he]
    simp only [SignType.pos_eq_one, SignType.coe_one, timedCut_StateTape_append]
    have ht' : table = (l ++ [true]) ++ List.replicate n true ++ false :: r := by
      simp [ht, List.replicate_succ, List.append_assoc]
    have hi := ih (j + 1) (l ++ [true]) ht'
    convert hi using 1 <;> simp [List.length_append, List.length_cons, Nat.add_assoc,
      Nat.add_comm 1 n, Int.add_assoc] <;> congr 1 <;> omega

/-- Installing a single permanent marker in an otherwise blank tape. -/
private lemma timedCut_install_marker (b : Bool) :
    Function.update (fun _ : ℤ => none) 0 (some b) = bufferTape [b] := by
  simpa using (bufferTape_append [] b).symm

/-- Interpreter entry with the captured table on its right blank and three
fresh auxiliary tapes. Physical input is already parked at the suffix start. -/
private def timedCut_InterpreterInitial {x : List Bool} (p : Fin (x.length + 2))
    (table : List Bool) : Cfg 4 Bool UniversalControl x :=
  ⟨some .start, p, universalFour (bufferTape table) (fun _ => none) (fun _ => none)
      (fun _ => none), universalFour table.length 0 0 0, []⟩

/-- Inactive data during interpreter initialization: physical input is stationary,
simulated work is blank, and the virtual-left marker is installed at zero with
its head at one (also for empty suffixes). -/
private def timedCut_InterpreterBase {x : List Bool} (p : Fin (x.length + 2)) :
    Cfg 4 Bool UniversalControl x :=
  ⟨some .main, p, universalFour (fun _ => none) (fun _ => none) (fun _ => none)
      (bufferTape [true]), universalFour 0 0 0 1, []⟩

/-- The first interpreter step installs the permanent markers and starts the
unconditional table rewind. -/
private lemma timedCut_Interpreter_first {x : List Bool} (p : Fin (x.length + 2))
    (table : List Bool) :
    timedCutInterpreter.step (timedCut_InterpreterInitial p table) =
      universalEvalCfg (timedCut_InterpreterBase p) (.rewindTable true 0) table
        (table.length - 1) (universalStateTape 0) 1 := by
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
  · funext i
    rcases i with ⟨i, hi⟩
    have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl
    · rfl
    · exact timedCut_install_marker false
    · rfl
    · exact timedCut_install_marker true
  · funext i
    rcases i with ⟨i, hi⟩
    have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl <;> rfl

/-- Exact interpreter initialization for a canonical count/initial-state prefix.
No transition-table lookup is involved yet.

**Proof sketch.** Install both markers (one transition), rewind the whole captured
table (`|table|+1`), skip the doubled count (`2|bits|+2`), copy the initial unary
state (`n+1`), and rewind its cursor (`n+2`). The sum is
`|table| + 2|bits| + 2n + 7`. Every intermediate configuration keeps the physical
input fixed and real output empty. -/
private lemma timedCut_Interpreter_initialize {x : List Bool}
    (p : Fin (x.length + 2)) (table bits records : List Bool) (n : ℕ)
    (ht : table = pairEncode bits (List.replicate n true ++ false :: records)) :
    timedCutInterpreter.runFrom (timedCut_InterpreterInitial p table)
      (table.length + 2 * bits.length + 2 * n + 7) =
    universalEvalCfg (timedCut_InterpreterBase p) .main table
      (2 * bits.length + 2 + n + 1) (universalStateTape n) 1 := by
  let base := timedCut_InterpreterBase p
  have hrew := timedCut_table_rewind base true 0 table (universalStateTape 0) 1
    table.length (le_refl _)
  have hcount := timedCut_count_run base true 0 table (universalStateTape 0) 1
    bits [] (List.replicate n true ++ false :: records) (by simpa [pairEncode] using ht)
  let countPrefix := (bits.flatMap fun b => [b, b]) ++ [false, true]
  have hlen : countPrefix.length = 2 * bits.length + 2 := by
    simpa [countPrefix, pairEncode] using universal_pair_length bits []
  have hcopy := timedCut_unary_copy base .initialCopy (.rewindState none) .pos table
    (by intro inp work h; simp [timedCutInterpreter, universalInterpreter, h])
    (by intro inp work h; simp [timedCutInterpreter, universalInterpreter, h]) n 0 countPrefix records
    (by simpa [countPrefix, pairEncode, List.append_assoc] using ht)
  have hstate := timedCut_state_rewind base (.rewindState none) .main table
    (2 * bits.length + 2 + n + 1) (universalStateTape n)
    (universalStateTape_marker n).1 (universalStateTape_marker n).2
    (by intro inp work h; simp [timedCutInterpreter, universalInterpreter, h])
    (by intro inp work h; simp [timedCutInterpreter, universalInterpreter, h]) (n + 1)
  have htime : table.length + 2 * bits.length + 2 * n + 7 =
      1 + (table.length + 1) + (2 * bits.length + 2) + (n + 1) + (n + 2) := by omega
  rw [htime,
    MultiTapeTM.runFrom_add _ (1 + (table.length + 1) + (2 * bits.length + 2) + (n + 1)) (n + 2),
    MultiTapeTM.runFrom_add _ (1 + (table.length + 1) + (2 * bits.length + 2)) (n + 1),
    MultiTapeTM.runFrom_add _ (1 + (table.length + 1)) (2 * bits.length + 2),
    MultiTapeTM.runFrom_add _ 1 (table.length + 1)]
  change timedCutInterpreter.runFrom
    (timedCutInterpreter.runFrom
      (timedCutInterpreter.runFrom
        (timedCutInterpreter.runFrom
          (timedCutInterpreter.step (timedCut_InterpreterInitial p table))
          (table.length + 1)) (2 * bits.length + 2)) (n + 1)) (n + 2) = _
  rw [timedCut_Interpreter_first, hrew]
  have hc : timedCutInterpreter.runFrom
      (universalEvalCfg base (.countFirst true 0) table 0 (universalStateTape 0) 1)
      (2 * bits.length + 2) =
    universalEvalCfg base .initialCopy table (2 * bits.length + 2) (universalStateTape 0) 1 := by
    simpa using hcount
  rw [hc]
  have hp : timedCutInterpreter.runFrom
      (universalEvalCfg base .initialCopy table (2 * bits.length + 2) (universalStateTape 0) 1)
      (n + 1) =
    universalEvalCfg base (.rewindState none) table (2 * bits.length + 2 + n + 1)
      (universalStateTape n) (n + 1) := by
    simpa [hlen] using hcopy
  rw [hp]
  simpa using hstate



/-- Skip the remaining fixed action fields, one transition per bit.

**Proof sketch.** Descending induction on the number of fields still to skip.
The last field enters the unary scanner; every other field increments the
bounded field register. No tape content is inspected or modified. -/
private lemma timedCut_skip_fixed {x : List Bool}
    (base : Cfg 4 Bool UniversalControl x) (dest : Option (Fin 9)) (rem : Fin 9)
    (table : List Bool) (state : ℤ → Option Bool) (sp : ℤ) :
    ∀ (n : ℕ) (field : Fin 8) (tp : ℤ), field.val + n = 7 →
      timedCutInterpreter.runFrom
        (universalEvalCfg base (.skipFixed dest rem field) table tp state sp) (n + 1) =
      universalEvalCfg base (.skipUnary dest rem) table (tp + n + 1) state sp := by
  intro n
  induction n with
  | zero =>
    intro field tp hf
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    have he := timedCut_Eval_step base (.skipFixed dest rem field) (.skipUnary dest rem)
      table tp state sp .pos 0 none (by simp [timedCutInterpreter, universalInterpreter, show field.val = 7 by omega])
    simpa using he
  | succ n ih =>
    intro field tp hf
    have hne : field.val ≠ 7 := by omega
    have he := timedCut_Eval_step base (.skipFixed dest rem field)
      (.skipFixed dest rem ⟨field.val + 1, by omega⟩) table tp state sp .pos 0 none
      (by simp [timedCutInterpreter, universalInterpreter, hne])
    rw [MultiTapeTM.runFrom_succ_eq_step, he]
    simp only [SignType.pos_eq_one, SignType.coe_one, SignType.coe_zero, add_zero]
    convert ih ⟨field.val + 1, by omega⟩ (tp + 1) (by simp; omega) using 1 <;>
      push_cast <;> congr 1 <;> omega


/-- The unary tail of a skipped record costs exactly its serialized length.

**Proof sketch.** A true cell advances once without changing control. The false
terminator either finishes the request or decrements the bounded record counter.
Induction grows the consumed list prefix by one cell. -/
private lemma timedCut_skip_unary {x : List Bool}
    (base : Cfg 4 Bool UniversalControl x) (dest : Option (Fin 9)) (rem : Fin 9)
    (table : List Bool) (state : ℤ → Option Bool) (sp : ℤ)
    (n : ℕ) (l r : List Bool)
    (ht : table = l ++ List.replicate n true ++ false :: r) :
    timedCutInterpreter.runFrom
      (universalEvalCfg base (.skipUnary dest rem) table l.length state sp) (n + 1) =
    universalEvalCfg base
      (if h : rem.val = 0 then universalSkipDone dest
        else .skipFixed dest ⟨rem.val - 1, by omega⟩ 0)
      table (l.length + n + 1) state sp := by
  induction n generalizing l with
  | zero =>
    have hr : bufferTape table (l.length : ℤ) = some false := by
      rw [ht]; simpa using timedCut_table_read l r false
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    have he := timedCut_Eval_step base (.skipUnary dest rem)
      (if h : rem.val = 0 then universalSkipDone dest
        else .skipFixed dest ⟨rem.val - 1, by omega⟩ 0)
      table l.length state sp .pos 0 none
      (by
        by_cases h : rem.val = 0
        · have hz : rem = 0 := Fin.ext h
          simp [timedCutInterpreter, universalInterpreter, universalFour, hr, hz, universalSkipDone]
        · have hz : rem ≠ 0 := fun he => h (congrArg Fin.val he)
          simp [timedCutInterpreter, universalInterpreter, universalFour, hr, h, hz, universalSkipDone])
    simpa using he
  | succ n ih =>
    have hr : bufferTape table (l.length : ℤ) = some true := by
      rw [ht]; simpa [List.replicate_succ, List.append_assoc] using
        timedCut_table_read l (List.replicate n true ++ false :: r) true
    have he := timedCut_Eval_step base (.skipUnary dest rem) (.skipUnary dest rem)
      table l.length state sp .pos 0 none
      (by simp [timedCutInterpreter, universalInterpreter, universalFour, hr])
    rw [MultiTapeTM.runFrom_succ_eq_step, he]
    simp only [SignType.pos_eq_one, SignType.coe_one, SignType.coe_zero, add_zero]
    have ht' : table = (l ++ [true]) ++ List.replicate n true ++ false :: r := by
      simp [ht, List.replicate_succ, List.append_assoc]
    convert ih (l ++ [true]) ht' using 1 <;>
      simp [List.length_append, List.length_cons] <;> congr 1 <;> omega

/-- Skip one complete serialized record at exact cost.

**Proof sketch.** Concatenate the eight fixed-field transitions and the unary
tail scan. The record grammar identifies their total with the record length. -/
private lemma timedCut_skip_record {x : List Bool} {n : ℕ}
    (base : Cfg 4 Bool UniversalControl x) (dest : Option (Fin 9)) (rem : Fin 9)
    (table : List Bool) (state : ℤ → Option Bool) (sp : ℤ)
    (a : Action 1 Bool (Fin (n + 1))) (l r : List Bool)
    (ht : table = l ++ universalRecordBits a ++ r) :
    timedCutInterpreter.runFrom
      (universalEvalCfg base (.skipFixed dest rem 0) table l.length state sp)
      (universalRecordBits a).length =
    universalEvalCfg base
      (if h : rem.val = 0 then universalSkipDone dest
        else .skipFixed dest ⟨rem.val - 1, by omega⟩ 0)
      table (l.length + (universalRecordBits a).length) state sp := by
  have hlen : (universalRecordBits a).length = 8 + (universalNextOnes a.state + 1) := by
    rw [universal_record_shape]
    simp only [List.length_append, List.length_ofFn, List.length_replicate,
      List.length_cons, List.length_nil]
    omega
  have hfixed := timedCut_skip_fixed base dest rem table state sp 7 0 l.length rfl
  have hunary := timedCut_skip_unary base dest rem table state sp
    (universalNextOnes a.state) (l ++ List.ofFn (universalActionBits a)) r
    (by simpa [universal_record_shape, List.append_assoc] using ht)
  rw [hlen, MultiTapeTM.runFrom_add]
  have hf : timedCutInterpreter.runFrom
      (universalEvalCfg base (.skipFixed dest rem 0) table l.length state sp) 8 =
      universalEvalCfg base (.skipUnary dest rem) table (l.length + 8) state sp := by
    simpa only [Nat.cast_ofNat, Int.add_assoc, show (7 : ℤ) + 1 = 8 from rfl] using hfixed
  rw [hf]
  simpa only [List.length_append, List.length_ofFn, Nat.cast_add, Nat.cast_ofNat,
    Int.add_assoc] using hunary

/-- A bounded request skips precisely the specified nonempty list of records.

**Proof sketch.** Execute the first record and decrement the record counter.
The last record enters the requested continuation. Run addition adds the
serialized lengths, without an extra transition between consecutive records. -/
private lemma timedCut_skip_records {x : List Bool} {n : ℕ}
    (base : Cfg 4 Bool UniversalControl x) (dest : Option (Fin 9))
    (table : List Bool) (state : ℤ → Option Bool) (sp : ℤ)
    (as : List (Action 1 Bool (Fin (n + 1)))) (l r : List Bool)
    (rem : Fin 9) (hlen : as.length = rem.val + 1)
    (ht : table = l ++ as.flatMap universalRecordBits ++ r) :
    timedCutInterpreter.runFrom
      (universalEvalCfg base (.skipFixed dest rem 0) table l.length state sp)
      (as.flatMap universalRecordBits).length =
    universalEvalCfg base (universalSkipDone dest) table
      (l.length + (as.flatMap universalRecordBits).length) state sp := by
  induction as generalizing l rem with
  | nil => simp only [List.length_nil] at hlen; omega
  | cons a as ih =>
    have hv : rem.val = as.length := by simp only [List.length_cons] at hlen; omega
    have he := timedCut_skip_record base dest rem table state sp a l
      (as.flatMap universalRecordBits ++ r)
      (by simpa only [List.flatMap_cons, List.append_assoc] using ht)
    rw [List.flatMap_cons, List.length_append, MultiTapeTM.runFrom_add, he]
    cases as with
    | nil => simp [hv]
    | cons b bs =>
      have hn : rem.val ≠ 0 := by simp only [List.length_cons] at hv; omega
      rw [dif_neg hn]
      have htail : (b :: bs).length = rem.val - 1 + 1 := by
        simp only [List.length_cons] at hv ⊢
        omega
      have hi := ih (l ++ universalRecordBits a) ⟨rem.val - 1, by omega⟩ htail
        (by simpa only [List.flatMap_cons, List.append_assoc] using ht)
      convert hi using 1 <;>
        simp only [List.length_append, Nat.cast_add] <;> congr 1 <;> omega

/-- Each erased unary state symbol skips exactly nine transition records.

**Proof sketch.** Erase the first remaining state symbol, run the nine-record
scanner, and repeat for the remaining groups. At the final blank one transition
enters the state rewind. The state-window invariant records all erasures. -/
private lemma timedCut_skip_groups {x : List Bool} {n : ℕ}
    (base : Cfg 4 Bool UniversalControl x) (index : Fin 9) (table : List Bool)
    (groups : List (List (Action 1 Bool (Fin (n + 1)))))
    (hg : ∀ g ∈ groups, g.length = 9) (l r : List Bool) (j : ℕ)
    (ht : table = l ++ groups.flatMap (fun g => g.flatMap universalRecordBits) ++ r) :
    timedCutInterpreter.runFrom
      (universalEvalCfg base (.group index) table l.length
        (universalStateWindow j groups.length) (j + 1))
      (groups.length + (groups.flatMap (fun g => g.flatMap universalRecordBits)).length + 1) =
    universalEvalCfg base (.rewindState (some index)) table
      (l.length + (groups.flatMap (fun g => g.flatMap universalRecordBits)).length)
      (universalStateWindow (j + groups.length) 0) (j + groups.length + 1) := by
  induction groups generalizing l j with
  | nil =>
    simp only [List.length_nil, List.flatMap_nil, Nat.add_zero, Nat.zero_add,
      Nat.cast_zero, add_zero, MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    have he := timedCut_Eval_step base (.group index) (.rewindState (some index))
      table l.length (universalStateWindow j 0) (j + 1) 0 0 none
      (by simp [timedCutInterpreter, universalInterpreter, universalFour, universalStateWindow_end])
    simpa using he
  | cons g gs ih =>
    have hgl : g.length = 9 := hg g (by simp)
    have he := timedCut_Eval_step base (.group index) (.skipFixed (some index) 8 0)
      table l.length (universalStateWindow j (gs.length + 1)) (j + 1) 0 .pos (some none)
      (by simp [timedCutInterpreter, universalInterpreter, universalFour, universalStateWindow_read])
    have hskip := timedCut_skip_records base (some index) table
      (universalStateWindow (j + 1) gs.length) (j + 2) g l
      (gs.flatMap (fun g => g.flatMap universalRecordBits) ++ r) 8 hgl
      (by simpa [List.flatMap_cons, List.append_assoc] using ht)
    have hrest := ih (fun a ha => hg a (by simp [ha]))
      (l ++ g.flatMap universalRecordBits) (j + 1)
      (by simpa [List.flatMap_cons, List.append_assoc] using ht)
    have htime : (g :: gs).length +
        ((g :: gs).flatMap (fun g => g.flatMap universalRecordBits)).length + 1 =
        1 + (g.flatMap universalRecordBits).length +
          (gs.length + (gs.flatMap (fun g => g.flatMap universalRecordBits)).length + 1) := by
      simp only [List.length_cons, List.flatMap_cons, List.length_append]; omega
    rw [htime, MultiTapeTM.runFrom_add _ (1 + (g.flatMap universalRecordBits).length)
      (gs.length + (gs.flatMap (fun g => g.flatMap universalRecordBits)).length + 1),
      MultiTapeTM.runFrom_add _ 1 (g.flatMap universalRecordBits).length]
    simp only [List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step' (t := 0), MultiTapeTM.runFrom_zero, he]
    simp only [SignType.coe_zero, add_zero, SignType.pos_eq_one, SignType.coe_one,
      universalStateWindow_erase]
    rw [show (j : ℤ) + 1 + 1 = j + 2 by omega, hskip]
    simpa only [universalSkipDone, List.flatMap_cons, List.length_append, List.length_cons,
      Nat.cast_add, Nat.cast_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
      Int.add_assoc, Int.add_left_comm, Int.add_comm, Int.reduceAdd] using hrest

/-- Reading fixed action fields fills the finite eight-bit register exactly.

**Proof sketch.** The register already agrees with the record before the current
field. Read and update that field, maintaining agreement on a longer prefix.
After field seven the agreement covers every register entry. -/
private lemma timedCut_read_fixed {x : List Bool}
    (base : Cfg 4 Bool UniversalControl x) (table : List Bool)
    (state : ℤ → Option Bool) (sp : ℤ) (bits : Fin 8 → Bool) (l r : List Bool)
    (ht : table = l ++ List.ofFn bits ++ r) :
    ∀ (n : ℕ) (field : Fin 8) (old : Fin 8 → Bool), field.val + n = 7 →
      (∀ i : Fin 8, i.val < field.val → old i = bits i) →
      timedCutInterpreter.runFrom
        (universalEvalCfg base (.readAction field old) table
          (l.length + field.val) state sp) (n + 1) =
      universalEvalCfg base (.nextState bits) table (l.length + 8) state sp := by
  intro n
  induction n with
  | zero =>
    intro field old hf hknown
    have hv : field.val = 7 := by omega
    have hr : bufferTape table (l.length + field.val : ℤ) = some (bits field) := by
      rw [← Nat.cast_add, bufferTape_nat, ht, List.append_assoc,
        List.getElem?_append_right (by omega)]
      simp only [Nat.add_sub_cancel_left]
      rw [List.getElem?_append_left (by simpa using field.isLt), List.getElem?_ofFn]
      simp only [field.isLt, ↓reduceDIte]
    have hb : Function.update old field (bits field) = bits := by
      funext i
      by_cases hi : i = field
      · subst i; simp
      · rw [Function.update_of_ne hi]
        apply hknown
        have hn : i.val ≠ field.val := fun h => hi (Fin.ext h)
        omega
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    have he := timedCut_Eval_step base (.readAction field old) (.nextState bits)
      table (l.length + field.val) state sp .pos 0 none
      (by
        simp only [timedCutInterpreter, universalInterpreter, universalFour, ↓reduceIte, hr]
        simp only [hv, ↓reduceDIte, hb])
    rw [he]
    simp only [SignType.pos_eq_one, SignType.coe_one, SignType.coe_zero, add_zero]
    congr 1
    omega
  | succ n ih =>
    intro field old hf hknown
    have hv : field.val ≠ 7 := by omega
    have hr : bufferTape table (l.length + field.val : ℤ) = some (bits field) := by
      rw [← Nat.cast_add, bufferTape_nat, ht, List.append_assoc,
        List.getElem?_append_right (by omega)]
      simp only [Nat.add_sub_cancel_left]
      rw [List.getElem?_append_left (by simpa using field.isLt), List.getElem?_ofFn]
      simp only [field.isLt, ↓reduceDIte]
    have hb : ∀ i : Fin 8, i.val < field.val + 1 →
        Function.update old field (bits field) i = bits i := by
      intro i hi
      by_cases he : i = field
      · subst i; simp
      · rw [Function.update_of_ne he]
        apply hknown
        have hn : i.val ≠ field.val := fun h => he (Fin.ext h)
        omega
    have he := timedCut_Eval_step base (.readAction field old)
      (.readAction ⟨field.val + 1, by omega⟩ (Function.update old field (bits field)))
      table (l.length + field.val) state sp .pos 0 none
      (by simp [timedCutInterpreter, universalInterpreter, universalFour, hr, hv])
    rw [MultiTapeTM.runFrom_succ_eq_step, he]
    simp only [SignType.pos_eq_one, SignType.coe_one, SignType.coe_zero, add_zero]
    convert ih ⟨field.val + 1, by omega⟩ _ (by simp; omega) hb using 1 <;>
      simp only [Fin.val_mk, Nat.cast_add, Nat.cast_one] <;> congr 1 <;> omega

/-- Successor decoding, copying, and rewinding cost, before applying the action. -/
private def timedCut_NextCost {n : ℕ} : Option (Fin (n + 1)) → ℕ
  | none => 1
  | some q => 2 * q.val + 4

/-- Decode the successor field and install its unary state at cursor one.

**Proof sketch.** A halting flag takes one transition. A live flag takes one,
copying its index takes `q+1`, and rewinding the new state takes `q+2`.
The table cursor stops on the field's false terminator in both cases. -/
private lemma timedCut_prepare_next {x : List Bool} {n : ℕ}
    (base : Cfg 4 Bool UniversalControl x) (table : List Bool) (bits : Fin 8 → Bool)
    (next : Option (Fin (n + 1))) (l r : List Bool)
    (ht : table = l ++ List.replicate (universalNextOnes next) true ++ false :: r) :
    timedCutInterpreter.runFrom
      (universalEvalCfg base (.nextState bits) table l.length (universalStateTape 0) 1)
      (timedCut_NextCost next) =
    universalEvalCfg base (.applyRecord bits next.isNone) table
      (l.length + universalNextOnes next) (universalStateTape ((next.map Fin.val).getD 0)) 1 := by
  cases next with
  | none =>
    have hr : bufferTape table (l.length : ℤ) = some false := by
      rw [ht]; simpa [universalNextOnes] using timedCut_table_read l r false
    have he := timedCut_Eval_step base (.nextState bits) (.applyRecord bits true)
      table l.length (universalStateTape 0) 1 0 0 none
      (by simp [timedCutInterpreter, universalInterpreter, universalFour, hr])
    simpa [timedCut_NextCost, universalNextOnes, MultiTapeTM.runFrom_succ_eq_step,
      MultiTapeTM.runFrom_zero] using he
  | some q =>
    have hr : bufferTape table (l.length : ℤ) = some true := by
      rw [ht]; simpa [universalNextOnes, List.replicate_succ, List.append_assoc] using
        timedCut_table_read l (List.replicate q.val true ++ false :: r) true
    have he := timedCut_Eval_step base (.nextState bits) (.copyState bits)
      table l.length (universalStateTape 0) 1 .pos 0 none
      (by simp [timedCutInterpreter, universalInterpreter, universalFour, hr])
    have hcopy := timedCut_unary_copy base (.copyState bits) (.rewindNext bits) 0 table
      (by intro inp work h; simp [timedCutInterpreter, universalInterpreter, h])
      (by intro inp work h; simp [timedCutInterpreter, universalInterpreter, h]) q.val 0 (l ++ [true]) r
      (by simpa [universalNextOnes, List.replicate_succ, List.append_assoc] using ht)
    have hrew := timedCut_state_rewind base (.rewindNext bits) (.applyRecord bits false)
      table (l.length + q.val + 1) (universalStateTape q.val)
      (universalStateTape_marker q.val).1 (universalStateTape_marker q.val).2
      (by intro inp work h; simp [timedCutInterpreter, universalInterpreter, h])
      (by intro inp work h; simp [timedCutInterpreter, universalInterpreter, h]) (q.val + 1)
    have hc : timedCutInterpreter.runFrom
        (universalEvalCfg base (.copyState bits) table (l.length + 1) (universalStateTape 0) 1)
        (q.val + 1) =
      universalEvalCfg base (.rewindNext bits) table (l.length + q.val + 1)
        (universalStateTape q.val) (q.val + 1) := by
      simpa [List.length_append, Int.add_assoc, Int.add_comm 1] using hcopy
    change timedCutInterpreter.runFrom _ (2 * q.val + 4) = _
    rw [show 2 * q.val + 4 = 1 + (q.val + 1) + (q.val + 2) by omega,
      MultiTapeTM.runFrom_add _ (1 + (q.val + 1)) (q.val + 2),
      MultiTapeTM.runFrom_add _ 1 (q.val + 1)]
    rw [MultiTapeTM.runFrom_succ_eq_step' (t := 0), MultiTapeTM.runFrom_zero, he]
    simp only [SignType.pos_eq_one, SignType.coe_one, SignType.coe_zero, add_zero]
    rw [hc]
    simpa only [universalNextOnes, Option.isNone_some, Option.map_some, Option.getD_some,
      Nat.cast_add, Nat.cast_one, Nat.add_assoc, Int.add_assoc] using hrew

/-- The nine actions for a state, in input-major, work-minor order. -/
private def timedCut_Actions (M : CodeTM) (q : Fin (M.numStates + 1)) :
    List (Action 1 Bool (Fin (M.numStates + 1))) :=
  ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
    ([none, some false, some true] : List (Option Bool)).map fun work =>
      M.tm.tr q inp (fun _ => work)

/-- Each state contributes nine records and the read offset selects its action. -/
private lemma timedCut_Actions_lookup (M : CodeTM) (q : Fin (M.numStates + 1))
    (inp work : Option Bool) :
    (timedCut_Actions M q).length = 9 ∧
    (timedCut_Actions M q)[(universalRecordIndex inp work).val]'(by
      change (universalRecordIndex inp work).val < 9
      exact (universalRecordIndex inp work).isLt) = M.tm.tr q inp (fun _ => work) := by
  constructor
  · rfl
  · rcases inp with _ | (_ | _) <;> rcases work with _ | (_ | _) <;> rfl

/-- Count prefix and initial-state field, excluding transition records. -/
private def timedCut_Header (M : CodeTM) : List Bool :=
  pairEncode (Nat.bits M.numStates) [] ++ List.replicate M.tm.q₀.val true ++ [false]

/-- Serialization as a header followed by the ordered lists of nine actions.

**Proof sketch.** Expand the serializer into its count, initial state, and table.
Identify each encoded action by its finite directions, optional symbols, and
successor, then regroup the nested enumerations into nine actions per state. -/
private lemma timedCut_serialization_actions (M : CodeTM) :
    M.serialize = timedCut_Header M ++
      ((List.finRange (M.numStates + 1)).map (timedCut_Actions M)).flatMap
        (fun g => g.flatMap universalRecordBits) := by
  have hr : M.serialize = pairEncode (Nat.bits M.numStates)
      (List.replicate M.tm.q₀.val true ++ false :: universalRecords M) := by
    unfold CodeTM.serialize
    change pairEncode _ ((List.replicate M.tm.q₀.val true ++ [false]) ++ _) = _
    rw [List.append_assoc]
    apply congrArg (pairEncode (Nat.bits M.numStates))
    apply congrArg (fun r : List Bool => List.replicate M.tm.q₀.val true ++ false :: r)
    unfold universalRecords
    dsimp only [List.append]
    congr 1
    funext q
    congr 1
    funext inp
    congr 1
    funext work
    generalize M.tm.tr q inp (fun _ => work) = a
    rcases a with ⟨di, tapes, out, next⟩
    have htapes : tapes = fun _ => tapes 0 := by
      funext i
      have hi : i = 0 := Fin.eq_zero i
      rw [hi]
    rw [htapes]
    generalize tapes 0 = entry
    rcases entry with ⟨write, dm⟩
    cases di <;> cases dm <;> rcases write with _ | (_ | (_ | _)) <;>
      rcases out with _ | (_ | _) <;> cases next <;> rfl
  rw [hr]
  simp [pairEncode, timedCut_Header, universalRecords, timedCut_Actions,
    List.flatMap_map, List.append_assoc]

/-- Decompose the canonical table at the action selected by state and reads.

**Proof sketch.** Split the increasing state enumeration at the source state,
and split its nine-entry list at the read offset. The two prefixes are exactly
the groups and records traversed by the controller. -/
private lemma timedCut_lookup_parts (M : CodeTM) (q : Fin (M.numStates + 1))
    (inp work : Option Bool) :
    ∃ (groups : List (List (Action 1 Bool (Fin (M.numStates + 1)))))
      (before : List (Action 1 Bool (Fin (M.numStates + 1)))) (after : List Bool),
      groups.length = q.val ∧ (∀ g ∈ groups, g.length = 9) ∧
      before.length = (universalRecordIndex inp work).val ∧
      M.serialize = timedCut_Header M ++
        groups.flatMap (fun g => g.flatMap universalRecordBits) ++
        before.flatMap universalRecordBits ++
        universalRecordBits (M.tm.tr q inp (fun _ => work)) ++ after := by
  let states := List.finRange (M.numStates + 1)
  let index := universalRecordIndex inp work
  let actions := timedCut_Actions M q
  have hq : q.val < states.length := by simpa [states] using q.isLt
  have hi : index.val < actions.length := by
    rw [(timedCut_Actions_lookup M q inp work).1]
    exact index.isLt
  have hs : states = states.take q.val ++ q :: states.drop (q.val + 1) := by
    have h := List.take_append_drop q.val states
    rw [List.drop_eq_getElem_cons hq] at h
    simpa [states] using h.symm
  have ha : actions = actions.take index.val ++
      M.tm.tr q inp (fun _ => work) :: actions.drop (index.val + 1) := by
    have h := List.take_append_drop index.val actions
    rw [List.drop_eq_getElem_cons hi, (timedCut_Actions_lookup M q inp work).2] at h
    exact h.symm
  refine ⟨(states.take q.val).map (timedCut_Actions M), actions.take index.val,
    (actions.drop (index.val + 1)).flatMap universalRecordBits ++
      ((states.drop (q.val + 1)).map (timedCut_Actions M)).flatMap
        (fun g => g.flatMap universalRecordBits), ?_, ?_, ?_, ?_⟩
  · simp only [List.length_map, List.length_take, Nat.min_eq_left (Nat.le_of_lt hq)]
  · intro g hg
    obtain ⟨s, _, rfl⟩ := List.mem_map.mp hg
    exact (timedCut_Actions_lookup M s none none).1
  · simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
    rfl
  · rw [timedCut_serialization_actions]
    change timedCut_Header M ++ (states.map (timedCut_Actions M)).flatMap _ = _
    conv_lhs => rw [hs, List.map_append, List.map_cons, List.flatMap_append,
      List.flatMap_cons]
    change timedCut_Header M ++ (_ ++ (actions.flatMap universalRecordBits ++ _)) = _
    conv_lhs => rw [ha]
    simp only [List.flatMap_append, List.flatMap_cons, List.append_assoc]

/-- Decoding the four fixed pairs recovers the source action fields. -/
private lemma timedCut_ActionBits_decode {n : ℕ} (a : Action 1 Bool (Fin (n + 1))) :
    universalSign (universalActionBits a 0) (universalActionBits a 1) = a.inputTape ∧
    universalWrite (universalActionBits a 2) (universalActionBits a 3) = (a.workTapes 0).1 ∧
    universalSign (universalActionBits a 4) (universalActionBits a 5) = (a.workTapes 0).2 ∧
    (if universalActionBits a 6 then some (universalActionBits a 7) else none) = a.output := by
  simp only [universalActionBits]
  constructor
  · cases a.inputTape <;> rfl
  constructor
  · rcases (a.workTapes 0).1 with _ | (_ | (_ | _)) <;> rfl
  constructor
  · cases (a.workTapes 0).2 <;> rfl
  · rcases a.output with _ | (_ | _) <;> rfl


/-- Select a record by destructive state counting and the bounded read offset.

**Proof sketch.** Skip the preceding state groups while erasing the unary state.
Rewind the erased state tape to one, then skip the read-offset prefix. An offset
of zero enters the action reader directly. The table scans cost their total
serialized length, and state administration costs twice the old index plus three. -/
private lemma timedCut_select {x : List Bool} {n : ℕ}
    (base : Cfg 4 Bool UniversalControl x) (index : Fin 9) (table : List Bool)
    (groups : List (List (Action 1 Bool (Fin (n + 1)))))
    (hg : ∀ g ∈ groups, g.length = 9)
    (before : List (Action 1 Bool (Fin (n + 1)))) (hb : before.length = index.val)
    (l r : List Bool)
    (ht : table = l ++ groups.flatMap (fun g => g.flatMap universalRecordBits) ++
      before.flatMap universalRecordBits ++ r) :
    timedCutInterpreter.runFrom
      (universalEvalCfg base (.group index) table l.length
        (universalStateTape groups.length) 1)
      (2 * groups.length + (groups.flatMap (fun g => g.flatMap universalRecordBits)).length +
        (before.flatMap universalRecordBits).length + 3) =
    universalEvalCfg base (.readAction 0 (fun _ => false)) table
      (l.length + (groups.flatMap (fun g => g.flatMap universalRecordBits)).length +
        (before.flatMap universalRecordBits).length) (universalStateTape 0) 1 := by
  let pg := groups.flatMap (fun g => g.flatMap universalRecordBits)
  let pb := before.flatMap universalRecordBits
  let next := if h : index.val = 0 then UniversalControl.readAction 0 (fun _ => false)
    else .skipFixed none ⟨index.val - 1, by omega⟩ 0
  have hgroup := timedCut_skip_groups base index table groups hg l (pb ++ r) 0
    (by simpa [pg, pb, List.append_assoc] using ht)
  have hgr : timedCutInterpreter.runFrom
      (universalEvalCfg base (.group index) table l.length (universalStateTape groups.length) 1)
      (groups.length + pg.length + 1) =
    universalEvalCfg base (.rewindState (some index)) table (l.length + pg.length)
      (universalStateTape 0) (groups.length + 1) := by
    simpa only [Nat.cast_zero, zero_add, universalStateWindow_empty,
      universalStateWindow_zero] using hgroup
  have hrew := timedCut_state_rewind base (.rewindState (some index)) next table
    (l.length + pg.length) (universalStateTape 0)
    (universalStateTape_marker 0).1 (universalStateTape_marker 0).2
    (by intro inp work h; simp [timedCutInterpreter, universalInterpreter, h, next])
    (by intro inp work h; simp [timedCutInterpreter, universalInterpreter, h]) (groups.length + 1)
  have hrw : timedCutInterpreter.runFrom
      (universalEvalCfg base (.rewindState (some index)) table (l.length + pg.length)
        (universalStateTape 0) (groups.length + 1)) (groups.length + 2) =
    universalEvalCfg base next table (l.length + pg.length) (universalStateTape 0) 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hrew
  have hskip : timedCutInterpreter.runFrom
      (universalEvalCfg base next table (l.length + pg.length) (universalStateTape 0) 1)
      pb.length = universalEvalCfg base (.readAction 0 (fun _ => false)) table
        (l.length + pg.length + pb.length) (universalStateTape 0) 1 := by
    by_cases hi : index.val = 0
    · have hz : before = [] := List.length_eq_zero_iff.mp (hb.trans hi)
      simp [next, hi, pb, hz]
    · have hh := timedCut_skip_records base none table (universalStateTape 0) 1
        before (l ++ pg) r ⟨index.val - 1, by omega⟩ (by simp only [Fin.val_mk]; omega)
        (by simpa [pg, pb, List.append_assoc] using ht)
      simpa only [next, dif_neg hi, universalSkipDone, List.length_append, Nat.cast_add]
        using hh
  change timedCutInterpreter.runFrom _ (2 * groups.length + pg.length + pb.length + 3) = _
  rw [show 2 * groups.length + pg.length + pb.length + 3 =
      (groups.length + pg.length + 1) + (groups.length + 2) + pb.length by omega,
    MultiTapeTM.runFrom_add _ ((groups.length + pg.length + 1) + (groups.length + 2)) pb.length,
    MultiTapeTM.runFrom_add _ (groups.length + pg.length + 1) (groups.length + 2),
    hgr, hrw, hskip]

/-- Concatenate two configuration equalities without unfolding either run. -/
private lemma timedCut_run_join {k : ℕ} {Q : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool Q) {a b c : Cfg k Bool Q x} {s t : ℕ}
    (hs : tm.runFrom a s = b) (ht : tm.runFrom b t = c) :
    tm.runFrom a (s + t) = c := by
  rw [MultiTapeTM.runFrom_add, hs, ht]


/-- Applying the decoded record commutes with the complete source checkpoint.

**Proof sketch.** Decode the four fixed pairs. The virtual-input movement lemma
supplies both the physical head equality and the marker-head equality. Optional
writes and emissions then agree field by field; the newly installed unary state
is precisely the successor representation, including the halting case. -/
private lemma timed_apply_record (M : CodeTM) (α : List Bool) {x : List Bool}
    (src : Cfg 1 Bool (Fin (M.numStates + 1)) x) (oldp p : ℕ)
    (a : Action 1 Bool (Fin (M.numStates + 1))) :
    universalInterpreter.step
      (universalEvalCfg (universalSimulationCfg M α src oldp)
        (.applyRecord (universalActionBits a) a.state.isNone) M.serialize p
        (universalStateTape ((a.state.map Fin.val).getD 0)) 1) =
    universalSimulationCfg M α (a.apply src) p := by
  let base := universalSimulationCfg M α src oldp
  let cfg := universalEvalCfg base (.applyRecord (universalActionBits a) a.state.isNone)
    M.serialize p (universalStateTape ((a.state.map Fin.val).getD 0)) 1
  let d := virtualMove (decide (bufferTape [true] (src.inputPos.val : ℤ) ≠ some true))
    src.inputSymbol a.inputTape
  have hi : (if base.workTapeSymbols 3 = some true then none else base.inputSymbol) =
      src.inputSymbol := universalInput_read α src
  have hb := timedCut_ActionBits_decode a
  have htr : universalInterpreter.tr
      (.applyRecord (universalActionBits a) a.state.isNone) cfg.inputSymbol cfg.workTapeSymbols =
      (⟨d, universalFour (none, 0) (none, 0) (a.workTapes 0) (none, d), a.output,
        a.state.map (fun _ => .main)⟩ : Action 4 Bool UniversalControl) := by
    have hr3 : cfg.workTapeSymbols 3 = base.workTapeSymbols 3 := rfl
    have hip : cfg.inputSymbol = base.inputSymbol := rfl
    simp only [universalInterpreter, hr3, hip, hi, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2]
    change (⟨d, universalFour (none, 0) (none, 0) (a.workTapes 0) (none, d), a.output,
      if a.state.isNone then none else some .main⟩ : Action 4 Bool UniversalControl) = _
    cases a.state <;> rfl
  change (universalInterpreter.tr _ cfg.inputSymbol cfg.workTapeSymbols).apply cfg = _
  rw [htr]
  have hmove := universalInput_move α src a.inputTape
  refine Cfg.ext rfl hmove.1 ?_ ?_ rfl
  · funext i
    rcases i with ⟨i, hi⟩
    have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl <;> rfl
  · funext i
    rcases i with ⟨i, hi⟩
    have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl
    · exact add_zero _
    · exact add_zero _
    · rfl
    · exact hmove.2

/-- A live lookup reaches the pending action whose application realizes one source transition.

**Proof sketch.** Read the virtual input and mirrored work symbol, rewind the
table, skip its count and initial-state fields, and select the source record.
Read its eight fixed bits and prepare its successor, stopping immediately before
the source action. Concatenate the exact runs; identify the pending native action
separately. The old cursor, count prefix, and all skipped records are each
bounded by the serialization length; every source state index is below the
number of states. The resulting bound is `3L + 5N + 20`. -/
private lemma timedCut_live_block (M : CodeTM) (α : List Bool) {x : List Bool}
    (src : Cfg 1 Bool (Fin (M.numStates + 1)) x) (p : ℕ)
    (hp : p ≤ M.serialize.length) (hs : src.state ≠ none) :
    ∃ (d p' : ℕ) (ready : Cfg 4 Bool UniversalControl (pairEncode α x)),
      d ≤ 3 * M.serialize.length + 5 * (M.numStates + 1) + 20 ∧
      p' ≤ M.serialize.length ∧
      (∃ bits halt, ready.state = some (.applyRecord bits halt)) ∧
      timedCutInterpreter.runFrom (universalSimulationCfg M α src p) d = ready ∧
      universalInterpreter.step ready = universalSimulationCfg M α (M.tm.step src) p'  := by
  cases hq : src.state with
  | none => exact False.elim (hs hq)
  | some q =>
    let base := universalSimulationCfg M α src p
    let index := universalRecordIndex src.inputSymbol (src.workTapeSymbols 0)
    let a := M.tm.tr q src.inputSymbol (fun _ => src.workTapeSymbols 0)
    obtain ⟨groups, before, after, hglen, hg, hblen, hparts⟩ :=
      timedCut_lookup_parts M q src.inputSymbol (src.workTapeSymbols 0)
    let pg := groups.flatMap (fun g => g.flatMap universalRecordBits)
    let pb := before.flatMap universalRecordBits
    let count := pairEncode (Nat.bits M.numStates) []
    let k := 2 * (Nat.bits M.numStates).length + 2
    let pre := timedCut_Header M ++ pg ++ pb
    let bits := universalActionBits a
    let p' := pre.length + 8 + universalNextOnes a.state
    let selectTime := 2 * q.val + pg.length + pb.length + 3
    let d := 1 + (p + 1) + k + (M.tm.q₀.val + 1) + selectTime + 8 +
      timedCut_NextCost a.state
    have hclen : count.length = k := by
      simpa [count, k] using universal_pair_length (Nat.bits M.numStates) []
    have hhlen : (timedCut_Header M).length = k + M.tm.q₀.val + 1 := by
      change (count ++ List.replicate M.tm.q₀.val true ++ [false]).length = _
      simp only [List.length_append, List.length_replicate, List.length_cons,
        List.length_nil, hclen]
    have hplen : pre.length = (timedCut_Header M).length + pg.length + pb.length := by
      simp only [pre, List.length_append]
    have ht : M.serialize = pre ++ universalRecordBits a ++ after := by
      simpa only [pre, pg, pb, a, List.append_assoc] using hparts
    have hcfg : base = universalEvalCfg base .main M.serialize p (universalStateTape q.val) 1 := by
      simp only [base, universalSimulationCfg, universalEvalCfg, hq,
        Option.map_some, Option.getD_some]
      rfl
    have hi : (if base.workTapeSymbols 3 = some true then none else base.inputSymbol) =
        src.inputSymbol := universalInput_read α src
    have hmain : timedCutInterpreter.runFrom base 1 =
        universalEvalCfg base (.rewindTable false index) M.serialize (p - 1)
          (universalStateTape q.val) 1 := by
      rw [MultiTapeTM.runFrom_succ_eq_step' (t := 0), MultiTapeTM.runFrom_zero]
      conv_lhs => rw [hcfg]
      have he := timedCut_Eval_step base .main (.rewindTable false index)
        M.serialize p (universalStateTape q.val) 1 .neg 0 none (by
          change universalAdmin (.rewindTable false (universalRecordIndex
            (if base.workTapeSymbols 3 = some true then none else base.inputSymbol)
            (base.workTapeSymbols 2))) .neg = _
          rw [hi]
          rfl)
      simpa only [SignType.neg_eq_neg_one, SignType.coe_neg_one, SignType.coe_zero,
        add_zero, sub_eq_add_neg] using he
    have hrew := timedCut_table_rewind base false index M.serialize
      (universalStateTape q.val) 1 p hp
    have hcount := timedCut_count_run base false index M.serialize
      (universalStateTape q.val) 1 (Nat.bits M.numStates) []
      (List.replicate M.tm.q₀.val true ++ false :: (pg ++ pb ++ universalRecordBits a ++ after))
      (by simpa [timedCut_Header, pairEncode, pg, pb, a, List.append_assoc] using hparts)
    have hc : timedCutInterpreter.runFrom
        (universalEvalCfg base (.countFirst false index) M.serialize 0 (universalStateTape q.val) 1) k =
      universalEvalCfg base (.initialSkip index) M.serialize k (universalStateTape q.val) 1 := by
      simpa only [Bool.false_eq_true, ↓reduceIte, List.length_nil, Nat.cast_zero,
        zero_add, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hcount
    have hinit := timedCut_initial_skip base index M.serialize (universalStateTape q.val) 1
      M.tm.q₀.val count (pg ++ pb ++ universalRecordBits a ++ after)
      (by simpa [count, timedCut_Header, pg, pb, a, List.append_assoc] using hparts)
    have hinit' : timedCutInterpreter.runFrom
        (universalEvalCfg base (.initialSkip index) M.serialize k (universalStateTape q.val) 1)
        (M.tm.q₀.val + 1) =
      universalEvalCfg base (.group index) M.serialize (timedCut_Header M).length
        (universalStateTape q.val) 1 := by
      simpa only [hclen, hhlen, Nat.cast_add, Nat.cast_one] using hinit
    have hselect := timedCut_select base index M.serialize groups hg before hblen
      (timedCut_Header M) (universalRecordBits a ++ after)
      (by simpa only [a, List.append_assoc] using hparts)
    have hsel : timedCutInterpreter.runFrom
        (universalEvalCfg base (.group index) M.serialize (timedCut_Header M).length
          (universalStateTape q.val) 1) selectTime =
      universalEvalCfg base (.readAction 0 (fun _ => false)) M.serialize pre.length
        (universalStateTape 0) 1 := by
      simpa only [hglen, hplen, Nat.cast_add] using hselect
    have hread := timedCut_read_fixed base M.serialize (universalStateTape 0) 1 bits pre
      (List.replicate (universalNextOnes a.state) true ++ false :: after)
      (by simpa [universal_record_shape, bits, List.append_assoc] using ht)
      7 0 (fun _ => false) rfl (by intro i hi; exact False.elim (Nat.not_lt_zero _ hi))
    have hrd : timedCutInterpreter.runFrom
        (universalEvalCfg base (.readAction 0 (fun _ => false)) M.serialize pre.length
          (universalStateTape 0) 1) 8 =
      universalEvalCfg base (.nextState bits) M.serialize (pre.length + 8)
        (universalStateTape 0) 1 := by
      simpa only [Fin.val_zero, Nat.cast_zero, add_zero] using hread
    have hnext := timedCut_prepare_next base M.serialize bits a.state
      (pre ++ List.ofFn bits) after
      (by simpa [universal_record_shape, bits, List.append_assoc] using ht)
    have hn : timedCutInterpreter.runFrom
        (universalEvalCfg base (.nextState bits) M.serialize (pre.length + 8)
          (universalStateTape 0) 1) (timedCut_NextCost a.state) =
      universalEvalCfg base (.applyRecord bits a.state.isNone) M.serialize p'
        (universalStateTape ((a.state.map Fin.val).getD 0)) 1 := by
      simpa only [p', List.length_append, List.length_ofFn, Nat.cast_add, Nat.cast_ofNat] using hnext
    have hrun := timedCut_run_join timedCutInterpreter
      (timedCut_run_join timedCutInterpreter
        (timedCut_run_join timedCutInterpreter
          (timedCut_run_join timedCutInterpreter
            (timedCut_run_join timedCutInterpreter
              (timedCut_run_join timedCutInterpreter hmain hrew) hc) hinit') hsel) hrd) hn
    have hstep : M.tm.step src = a.apply src := by
      have hw : src.workTapeSymbols = fun _ : Fin 1 => src.workTapeSymbols 0 := by
        funext i
        rw [Fin.eq_zero i]
      simp only [MultiTapeTM.step, hq]
      rw [hw]
    have hlength : M.serialize.length = pre.length + 8 +
        universalNextOnes a.state + 1 + after.length := by
      rw [ht, universal_record_shape]
      simp only [List.length_append, List.length_ofFn, List.length_replicate,
        List.length_cons, List.length_nil]
      omega
    have hnextBound : timedCut_NextCost a.state ≤ 2 * (M.numStates + 1) + 4 := by
      cases hnxt : a.state with
      | none => simp [timedCut_NextCost]
      | some q' => have hq' := q'.isLt; simp only [timedCut_NextCost]; omega
    have hqb := q.isLt
    have hq₀b := M.tm.q₀.isLt
    refine ⟨d, p', _, ?_, ?_, ⟨bits, a.state.isNone, rfl⟩, hrun, ?_⟩
    · dsimp only [d, selectTime]
      rw [hplen, hhlen] at hlength
      omega
    · dsimp only [p']; omega
    · rw [hstep]
      exact timed_apply_record M α src p p' a

/-- The physical prefix occupied by the twice-doubled clock and its delimiter. -/
private def timedClockPrefix (bs : List Bool) : List Bool :=
  bs.flatMap (fun b => [b, b, b, b]) ++ [false, false, true, true]

/-- Removing the clock region leaves precisely the original code-first pair. -/
private lemma timed_input_layout (bs α x : List Bool) :
    pairEncode (pairEncode bs α) x = timedClockPrefix bs ++ pairEncode α x := by
  induction bs with
  | nil => simp [pairEncode, timedClockPrefix]
  | cons b bs ih =>
    simpa only [pairEncode, timedClockPrefix, List.flatMap_cons, List.flatMap_append,
      List.cons_append, List.nil_append, List.append_assoc] using congrArg (fun l => b :: b :: b :: b :: l) ih

/-- The clock region has four physical cells per bit plus four delimiter cells. -/
private lemma timedClockPrefix_length (bs : List Bool) :
    (timedClockPrefix bs).length = 4 * bs.length + 4 := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [timedClockPrefix, List.flatMap_cons, List.cons_append, List.nil_append,
      List.length_cons] at *
    omega

/-- Finite control for separating the twice-doubled clock from the doubled code. -/
private inductive TimedPrefixControl where
  | clockFirst | clockSecond (b : Bool) | clockThird (b : Bool)
  | clockFourth (b : Bool) | clockEnd | codeFirst | codeSecond (b : Bool)
  deriving DecidableEq, Fintype

/-- The prefix parser stores only clock bits on its work tape and emits only code
bits. It stops on the outer separator, before reading the input suffix. -/
private def timedPrefixTM : FinTM Bool where
  k := 1
  State := TimedPrefixControl
  tm :=
    { q₀ := .clockFirst
      tr := fun q inp _ => match q with
        | .clockFirst => ⟨.pos, fun _ => (none, 0), none, inp.map .clockSecond⟩
        | .clockSecond b => ⟨.pos, fun _ => (none, 0), none, some (.clockThird b)⟩
        | .clockThird b => ⟨.pos, fun _ => (none, 0), none,
            some (if inp = some b then .clockFourth b else .clockEnd)⟩
        | .clockFourth b => ⟨.pos, fun _ => (some (some b), .pos), none, some .clockFirst⟩
        | .clockEnd => ⟨.pos, fun _ => (none, 0), none, some .codeFirst⟩
        | .codeFirst => ⟨.pos, fun _ => (none, 0), none, inp.map .codeSecond⟩
        | .codeSecond b =>
            if inp = some b then
              ⟨.pos, fun _ => (none, 0), some b, some .codeFirst⟩
            else ⟨.pos, fun _ => (none, 0), none, none⟩ }

/-- Configuration of the prefix parser, with its complete captured clock. -/
private def timedPrefixCfg (bs α x : List Bool) (q : Option TimedPrefixControl)
    (p : Fin ((pairEncode (pairEncode bs α) x).length + 2))
    (clock out : List Bool) : Cfg 1 Bool TimedPrefixControl (pairEncode (pairEncode bs α) x) :=
  ⟨q, p, fun _ => bufferTape clock, fun _ => clock.length, out⟩

/-- Length arithmetic for both nested delimiters. -/
private lemma timed_input_length (bs α x : List Bool) :
    (pairEncode (pairEncode bs α) x).length = 4 * bs.length + 2 * α.length + 6 + x.length := by
  rw [universal_pair_length, universal_pair_length]
  omega

/-- Every cell of a quadrupled clock bit has the same value. -/
private lemma timed_clock_get (bs α x : List Bool) (j r : ℕ)
    (hj : j < bs.length) (hr : r < 4) :
    (pairEncode (pairEncode bs α) x)[4 * j + r]? = some bs[j] := by
  rw [timed_input_layout]
  induction bs generalizing j with
  | nil => simp at hj
  | cons b bs ih =>
    cases j with
    | zero =>
      have h : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
      rcases h with rfl | rfl | rfl | rfl <;> rfl
    | succ j =>
      have hh := ih j (by simpa using hj)
      simpa only [timedClockPrefix, List.flatMap_cons, List.cons_append, List.nil_append,
        List.getElem?_cons_succ, List.getElem_cons_succ, Nat.mul_add, Nat.mul_one,
        Nat.add_assoc, Nat.add_comm 4 r] using hh

/-- The inner separator is doubled by the outer pairing. -/
private lemma timed_clock_separator (bs α x : List Bool) (r : ℕ) (hr : r < 4) :
    (pairEncode (pairEncode bs α) x)[4 * bs.length + r]? =
      [false, false, true, true][r]? := by
  rw [timed_input_layout]
  induction bs with
  | nil =>
    have h : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl <;> rfl
  | cons b bs ih =>
    simpa only [timedClockPrefix, List.flatMap_cons, List.cons_append, List.nil_append,
      List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm 4 r,
      List.getElem?_cons_succ] using ih

/-- A non-writing parser transition advances exactly one physical input cell. -/
private lemma timedPrefix_advance (bs α x clock out : List Bool)
    (q : TimedPrefixControl) (q' : Option TimedPrefixControl) (emit : Option Bool)
    (p : ℕ) (hp : p < (pairEncode (pairEncode bs α) x).length) (b : Bool)
    (hb : (pairEncode (pairEncode bs α) x)[p]? = some b)
    (htr : ∀ ws, timedPrefixTM.tm.tr q (some b) ws =
      ⟨.pos, fun _ => (none, 0), emit, q'⟩) :
    timedPrefixTM.tm.step
      (timedPrefixCfg bs α x (some q) ⟨p + 1, by omega⟩ clock out) =
    timedPrefixCfg bs α x q' ⟨p + 2, by omega⟩ clock (out ++ emit.toList) := by
  have hr : (timedPrefixCfg bs α x (some q) ⟨p + 1, by omega⟩ clock out).inputSymbol =
      some b := (inputSymbol_at _ p (by omega) rfl).trans hb
  change (timedPrefixTM.tm.tr q _ _).apply _ = _
  rw [hr, htr]
  refine Cfg.ext rfl ?_ rfl ?_ rfl
  · exact moveInputPos_pos_of_ne_right _ (by change p + 1 ≠ (pairEncode (pairEncode bs α) x).length + 1; omega)
  · funext i; exact add_zero _

/-- The fourth cell of a clock bit appends exactly its undoubled value. -/
private lemma timedPrefix_write (bs α x clock : List Bool) (b : Bool)
    (p : ℕ) (hp : p < (pairEncode (pairEncode bs α) x).length) :
    timedPrefixTM.tm.step
      (timedPrefixCfg bs α x (some (.clockFourth b)) ⟨p + 1, by omega⟩ clock []) =
    timedPrefixCfg bs α x (some .clockFirst) ⟨p + 2, by omega⟩ (clock ++ [b]) [] := by
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · exact moveInputPos_pos_of_ne_right _ (by change p + 1 ≠ (pairEncode (pairEncode bs α) x).length + 1; omega)
  · funext i; exact (bufferTape_append clock b).symm
  · funext i
    change (clock.length : ℤ) + 1 = ((clock ++ [b]).length : ℤ)
    simp

/-- Clock extraction consumes four cells and stores one bit per iteration.
The physical suffix and the native output remain untouched.

**Proof sketch.** Induct on the clock prefix already consumed. Four physical copies
of a bit take four transitions, with just one write to the clock tape; concatenate
these runs while preserving the untouched code and input suffix. -/
private lemma timedPrefix_clock (bs α x : List Bool) :
    ∀ j, (hj : j ≤ bs.length) →
    timedPrefixTM.tm.runFrom (timedPrefixTM.tm.initCfg (pairEncode (pairEncode bs α) x))
      (4 * j) =
    timedPrefixCfg bs α x (some .clockFirst)
      ⟨4 * j + 1, by rw [timed_input_length]; omega⟩ (bs.take j) [] := by
  intro j
  induction j with
  | zero =>
    intro hj
    apply Cfg.ext <;> simp [timedPrefixTM, timedPrefixCfg]
  | succ j ih =>
    intro hj
    have hlen := timed_input_length bs α x
    have hj' : j < bs.length := by omega
    have h0 := timedPrefix_advance bs α x (bs.take j) [] .clockFirst
      (some (.clockSecond bs[j])) none (4 * j) (by omega) bs[j]
      (by simpa using timed_clock_get bs α x j 0 hj' (by omega)) (by intro ws; rfl)
    have h1 := timedPrefix_advance bs α x (bs.take j) [] (.clockSecond bs[j])
      (some (.clockThird bs[j])) none (4 * j + 1) (by omega) bs[j]
      (timed_clock_get bs α x j 1 hj' (by omega)) (by intro ws; rfl)
    have h2 := timedPrefix_advance bs α x (bs.take j) [] (.clockThird bs[j])
      (some (.clockFourth bs[j])) none (4 * j + 2) (by omega) bs[j]
      (timed_clock_get bs α x j 2 hj' (by omega)) (by intro ws; simp [timedPrefixTM])
    have h3 := timedPrefix_write bs α x (bs.take j) bs[j] (4 * j + 3) (by omega)
    simp only [Nat.add_assoc, Nat.reduceAdd, Option.toList_none, List.append_nil] at h0 h1 h2 h3
    conv_lhs => rw [show 4 * (j + 1) = 4 * j + 1 + 1 + 1 + 1 by omega]
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step',
      MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step', ih (by omega), h0]
    rw [h1, h2, h3]
    have ht : bs.take j ++ [bs[j]] = bs.take (j + 1) := by
      rw [List.take_succ, List.getElem?_eq_getElem hj']
      rfl
    rw [ht]
    congr 1 <;> apply Fin.ext <;> simp only [Fin.val_mk] <;> omega

/-- The four physical delimiter cells transfer from clock capture to code extraction.

**Proof sketch.** Read the four separator cells in sequence. The first two zeros
are recognized as the start of the separator when the following one disagrees;
the fourth cell completes the switch to code extraction without writing a clock bit. -/
private lemma timedPrefix_clock_end (bs α x : List Bool) :
    timedPrefixTM.tm.runFrom (timedPrefixTM.tm.initCfg (pairEncode (pairEncode bs α) x))
      (4 * bs.length + 4) =
    timedPrefixCfg bs α x (some .codeFirst)
      ⟨4 * bs.length + 5, by rw [timed_input_length]; omega⟩ bs [] := by
  have hlen := timed_input_length bs α x
  have h0 := timedPrefix_advance bs α x bs [] .clockFirst (some (.clockSecond false)) none
    (4 * bs.length) (by omega) false
    (by simpa using timed_clock_separator bs α x 0 (by omega)) (by intro ws; rfl)
  have h1 := timedPrefix_advance bs α x bs [] (.clockSecond false) (some (.clockThird false)) none
    (4 * bs.length + 1) (by omega) false
    (timed_clock_separator bs α x 1 (by omega)) (by intro ws; rfl)
  have h2 := timedPrefix_advance bs α x bs [] (.clockThird false) (some .clockEnd) none
    (4 * bs.length + 2) (by omega) true
    (timed_clock_separator bs α x 2 (by omega)) (by intro ws; rfl)
  have h3 := timedPrefix_advance bs α x bs [] .clockEnd (some .codeFirst) none
    (4 * bs.length + 3) (by omega) true
    (timed_clock_separator bs α x 3 (by omega)) (by intro ws; rfl)
  simp only [Nat.add_assoc, Nat.reduceAdd, Option.toList_none, List.append_nil] at h0 h1 h2 h3
  conv_lhs => rw [show 4 * bs.length + 4 = 4 * bs.length + 1 + 1 + 1 + 1 by omega]
  rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step',
    MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step',
    timedPrefix_clock bs α x bs.length (le_refl _), List.take_length, h0]
  rw [h1, h2, h3]

/-- Suffix indexing after the complete clock prefix. -/
private lemma timed_code_get (bs α x : List Bool) (j : ℕ) :
    (pairEncode (pairEncode bs α) x)[4 * bs.length + 4 + j]? = (pairEncode α x)[j]? := by
  rw [timed_input_layout, ← timedClockPrefix_length,
    List.getElem?_append_right (by omega)]
  simp

/-- An aligned pair in the code region contains the corresponding code bit. -/
private lemma timed_pair_get (α x : List Bool) (j : ℕ) (hj : j < α.length) :
    (pairEncode α x)[2 * j]? = some α[j] ∧
      (pairEncode α x)[2 * j + 1]? = some α[j] := by
  induction α generalizing j with
  | nil => simp at hj
  | cons b α ih =>
    cases j with
    | zero => simp [pairEncode]
    | succ j =>
      simpa only [pairEncode, List.flatMap_cons, List.cons_append, List.nil_append,
        Nat.mul_add, Nat.mul_one, Nat.add_assoc, List.getElem?_cons_succ,
        List.getElem_cons_succ] using ih j (by simpa using hj)

/-- The aligned separator immediately follows the doubled code. -/
private lemma timed_pair_separator (α x : List Bool) :
    (pairEncode α x)[2 * α.length]? = some false ∧
      (pairEncode α x)[2 * α.length + 1]? = some true := by
  induction α with
  | nil => simp [pairEncode]
  | cons b α ih =>
    simpa only [pairEncode, List.flatMap_cons, List.cons_append, List.nil_append,
      List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_assoc,
      List.getElem?_cons_succ] using ih

/-- Code extraction emits the undoubled code prefix and preserves the stored clock.

**Proof sketch.** Induct on the code prefix. Each equal pair emits one code bit and
advances two input cells. The unequal terminal pair halts the parser without an
emission, leaving the saved clock unchanged. -/
private lemma timedPrefix_code (bs α x : List Bool) :
    ∀ j, (hj : j ≤ α.length) →
    timedPrefixTM.tm.runFrom (timedPrefixTM.tm.initCfg (pairEncode (pairEncode bs α) x))
      (4 * bs.length + 4 + 2 * j) =
    timedPrefixCfg bs α x (some .codeFirst)
      ⟨4 * bs.length + 4 + 2 * j + 1, by rw [timed_input_length]; omega⟩ bs (α.take j) := by
  intro j
  induction j with
  | zero => intro hj; simpa only [Nat.mul_zero, Nat.add_zero, List.take_zero] using timedPrefix_clock_end bs α x
  | succ j ih =>
    intro hj
    have hlen := timed_input_length bs α x
    have hj' : j < α.length := by omega
    have hr := timed_pair_get α x j hj'
    have h0 := timedPrefix_advance bs α x bs (α.take j) .codeFirst
      (some (.codeSecond α[j])) none (4 * bs.length + 4 + 2 * j) (by omega) α[j]
      (by rw [timed_code_get]; exact hr.1) (by intro ws; rfl)
    have h1 := timedPrefix_advance bs α x bs (α.take j) (.codeSecond α[j])
      (some .codeFirst) (some α[j]) (4 * bs.length + 4 + 2 * j + 1) (by omega) α[j]
      (by rw [Nat.add_assoc _ (2 * j) 1, timed_code_get]; exact hr.2)
      (by intro ws; simp [timedPrefixTM])
    simp only [Nat.add_assoc, Nat.reduceAdd, Option.toList_none, List.append_nil] at h0 h1
    conv_lhs => rw [show 4 * bs.length + 4 + 2 * (j + 1) =
      4 * bs.length + 4 + 2 * j + 1 + 1 by omega]
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    simp only [Nat.add_assoc, Nat.reduceAdd]
    rw [h0, h1]
    have ht : α.take j ++ [α[j]] = α.take (j + 1) := by
      rw [List.take_succ, List.getElem?_eq_getElem hj']; rfl
    simp only [Option.toList_some, ht]
    congr 1 <;> apply Fin.ext <;> simp only [Fin.val_mk] <;> omega

/-- Exact completed parser configuration, including the clock tape and parked input.
Both delimiters are consumed, including when the clock and code are empty. -/
private lemma timedPrefix_complete (bs α x : List Bool) :
    timedPrefixTM.tm.runFrom (timedPrefixTM.tm.initCfg (pairEncode (pairEncode bs α) x))
      (4 * bs.length + 2 * α.length + 6) =
    timedPrefixCfg bs α x none
      ⟨4 * bs.length + 2 * α.length + 7, by rw [timed_input_length]; omega⟩ bs α := by
  have hlen := timed_input_length bs α x
  have hr := timed_pair_separator α x
  have h0 := timedPrefix_advance bs α x bs α .codeFirst (some (.codeSecond false)) none
    (4 * bs.length + 4 + 2 * α.length) (by omega) false
    (by rw [timed_code_get]; exact hr.1) (by intro ws; rfl)
  have h1 := timedPrefix_advance bs α x bs α (.codeSecond false) none none
    (4 * bs.length + 4 + 2 * α.length + 1) (by omega) true
    (by rw [Nat.add_assoc _ (2 * α.length) 1, timed_code_get]; exact hr.2)
    (by intro ws; rfl)
  simp only [Nat.add_assoc, Nat.reduceAdd, Option.toList_none, List.append_nil] at h0 h1
  conv_lhs => rw [show 4 * bs.length + 2 * α.length + 6 =
      4 * bs.length + 4 + 2 * α.length + 1 + 1 by omega]
  rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step',
    timedPrefix_code bs α x α.length (le_refl _), List.take_length]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  rw [h0, h1]
  congr 1 <;> apply Fin.ext <;> simp only [Fin.val_mk] <;> omega

/-- Little-endian value of a fixed-width clock word. -/
private def timedValue : List Bool → ℕ
  | [] => 0
  | b :: bs => Nat.bit b (timedValue bs)

/-- Canonical clock words represent their given deadline. -/
private lemma timedValue_bits (t : ℕ) : timedValue t.bits = t := by
  induction t using Nat.binaryRec' with
  | zero => simp [timedValue]
  | bit b t ht ih => rw [Nat.bits_append_bit t b ht]; exact congrArg (Nat.bit b) ih

/-- Fixed-width binary subtraction, carrying an underflow flag. -/
private def timedBorrow : Bool → List Bool → Bool × List Bool
  | carry, [] => (carry, [])
  | carry, b :: bs =>
    let rest := timedBorrow (carry && !b) bs
    (rest.1, Bool.xor b carry :: rest.2)

/-- A cleared borrow leaves the remaining word unchanged. -/
private lemma timedBorrow_false (bs : List Bool) : timedBorrow false bs = (false, bs) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [timedBorrow, ih]

/-- Subtraction preserves the allocated word width. -/
private lemma timedBorrow_length (carry : Bool) (bs : List Bool) :
    (timedBorrow carry bs).2.length = bs.length := by
  induction bs generalizing carry with
  | nil => rfl
  | cons b bs ih => simp only [timedBorrow, List.length_cons, ih]

/-- Borrow underflow detects exactly a zero remaining budget. -/
private lemma timedBorrow_underflow (bs : List Bool) :
    (timedBorrow true bs).1 = true ↔ timedValue bs = 0 := by
  induction bs with
  | nil => simp [timedBorrow, timedValue]
  | cons b bs ih =>
    cases b <;> simp [timedBorrow, timedBorrow_false, timedValue, Nat.bit_val, ih]

/-- A successful borrow removes exactly one transition from the budget. -/
private lemma timedBorrow_value (bs : List Bool) (h : 0 < timedValue bs) :
    timedValue (timedBorrow true bs).2 + 1 = timedValue bs := by
  induction bs with
  | nil => simp [timedValue] at h
  | cons b bs ih =>
    cases b with
    | false =>
      have ht : 0 < timedValue bs := by simpa [timedValue, Nat.bit_val] using h
      have hb := ih ht
      change Nat.bit true (timedValue (timedBorrow true bs).2) + 1 = Nat.bit false (timedValue bs)
      simp only [Nat.bit_val]
      change (2 * timedValue (timedBorrow true bs).2 + 1) + 1 = 2 * timedValue bs + 0
      omega
    | true => simp [timedBorrow, timedBorrow_false, timedValue, Nat.bit_val]

/-- Extra phases retain a selected action while its clock is serviced. -/
private inductive TimedControl where
  | work (q : UniversalControl)
  | clockBack (bits : Fin 8 → Bool) (halt : Bool)
  | borrow (bits : Fin 8 → Bool) (halt carry : Bool)
  | execute (bits : Fin 8 → Bool) (halt : Bool)
  | emitStart | emitBack | flush
  deriving DecidableEq, Fintype

/-- Four audited interpreter lanes followed by the clock and output buffer. -/
private def timedSix {A : Type} (core : Fin 4 → A) (clock buffer : A) : Fin 6 → A :=
  fun i => if i = 0 then core 0 else if i = 1 then core 1 else
    if i = 2 then core 2 else if i = 3 then core 3 else if i = 4 then clock else buffer

/-- Lift an interpreter action while buffering its emission and intercepting halt. -/
private def timedAction (a : Action 4 Bool UniversalControl) : Action 6 Bool TimedControl :=
  ⟨a.inputTape, timedSix a.workTapes (none, 0)
    (a.output.map some, if a.output = none then 0 else .pos), none,
    some ((a.state.map TimedControl.work).getD .emitStart)⟩

/-- A clock-only or output-buffer-only administrative action. -/
private def timedAdmin (q : Option TimedControl)
    (clock buffer : Option (Option Bool) × SignType) (emit : Option Bool := none) :
    Action 6 Bool TimedControl :=
  ⟨0, timedSix (fun _ => (none, 0)) clock buffer, emit, q⟩

/-- Finite timed interpreter. A selected action is applied only after a successful
borrow. Its halting transition remains live until the success tag and buffered
emissions have been flushed. A failed borrow emits only the timeout tag. -/
private def timedInterpreter : MultiTapeTM 6 Bool TimedControl where
  q₀ := .work .start
  tr := fun q inp ws => match q with
    | .work (.applyRecord bits halt) =>
        timedAdmin (some (.clockBack bits halt)) (none, .neg) (none, 0)
    | .work q => timedAction (universalInterpreter.tr q inp (fun i => ws (i.castAdd 2)))
    | .clockBack bits halt =>
        if ws 4 = none then timedAdmin (some (.borrow bits halt true)) (none, .pos) (none, 0)
        else timedAdmin (some (.clockBack bits halt)) (none, .neg) (none, 0)
    | .borrow bits halt carry => match ws 4 with
        | some b => timedAdmin (some (.borrow bits halt (carry && !b)))
            (some (some (Bool.xor b carry)), .pos) (none, 0)
        | none => if carry then timedAdmin none (none, 0) (none, 0) (some false)
            else timedAdmin (some (.execute bits halt)) (none, 0) (none, 0)
    | .execute bits halt =>
        timedAction (universalInterpreter.tr (.applyRecord bits halt) inp (fun i => ws (i.castAdd 2)))
    | .emitStart => timedAdmin (some .emitBack) (none, 0) (none, .neg)
    | .emitBack =>
        if ws 5 = none then timedAdmin (some .flush) (none, 0) (none, .pos) (some true)
        else timedAdmin (some .emitBack) (none, 0) (none, .neg)
    | .flush => match ws 5 with
        | some b => timedAdmin (some .flush) (none, 0) (none, .pos) (some b)
        | none => timedAdmin none (none, 0) (none, 0)

/-- The original output is represented on the buffer tape; no native emission
has occurred in a simulated checkpoint or during a table lookup. -/
private def timedLift {x : List Bool} (cfg : Cfg 4 Bool UniversalControl x)
    (clock : List Bool) : Cfg 6 Bool TimedControl x :=
  ⟨some ((cfg.state.map TimedControl.work).getD .emitStart), cfg.inputPos,
    timedSix cfg.workTapes (bufferTape clock) (bufferTape cfg.output),
    timedSix cfg.workTapePos clock.length cfg.output.length, []⟩

/-- A non-record state is unaffected by the stopped-interpreter modification. -/
private lemma timedCut_regular (q : UniversalControl)
    (hq : ∀ bits halt, q ≠ .applyRecord bits halt) (inp : Option Bool)
    (ws : Fin 4 → Option Bool) :
    timedCutInterpreter.tr q inp ws = universalInterpreter.tr q inp ws := by
  cases q <;> first | rfl | exact (hq _ _ rfl).elim

/-- A live endpoint of the stopped interpreter excludes every earlier stop.
The same absorption argument also excludes earlier native halts. -/
private lemma timedCut_live_before {x : List Bool} (cfg : Cfg 4 Bool UniversalControl x)
    {s t : ℕ} (hst : s ≤ t) (ht : (timedCutInterpreter.runFrom cfg t).state ≠ none) :
    (timedCutInterpreter.runFrom cfg s).state ≠ none := by
  intro hs
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hst
  rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hs] at ht
  exact ht hs

/-- Every transition strictly before a live endpoint avoids record application. -/
private lemma timedCut_no_record {x : List Bool} (cfg : Cfg 4 Bool UniversalControl x)
    {s t : ℕ} (hst : s < t) (ht : (timedCutInterpreter.runFrom cfg t).state ≠ none) :
    ∀ bits halt, (timedCutInterpreter.runFrom cfg s).state ≠ some (.applyRecord bits halt) := by
  intro bits halt hs
  have hl := timedCut_live_before cfg (show s + 1 ≤ t by omega) ht
  apply hl
  rw [MultiTapeTM.runFrom_succ_eq_step']
  simp only [MultiTapeTM.step, hs, timedCutInterpreter, Action.apply]

/-- The six lanes expose their four source reads and two auxiliary reads. -/
private lemma timedSix_core {A : Type} (a : Fin 4 → A) (b c : A) (i : Fin 4) :
    timedSix a b c (i.castAdd 2) = a i := by fin_cases i <;> rfl

/-- Applying a lifted source action captures even an emission on its halt transition. -/
private lemma timedAction_apply {x : List Bool} (cfg : Cfg 4 Bool UniversalControl x)
    (clock : List Bool) (a : Action 4 Bool UniversalControl) :
    (timedAction a).apply (timedLift cfg clock) = timedLift (a.apply cfg) clock := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    fin_cases i <;> cases ho : a.output <;>
      simp [timedAction, timedLift, timedSix, Action.apply, ho, bufferTape_append]
  · funext i
    fin_cases i <;> cases ho : a.output <;>
      simp [timedAction, timedLift, timedSix, Action.apply, ho]

/-- Every ordinary interpreter step replays in one physical timed-machine step.

**Proof sketch.** Exclude the pending-action state, so both controllers select
the same native action. The action-lifting identity preserves the four simulated
tapes, keeps the clock fixed, and captures any emission on the buffer. -/
private lemma timed_regular_step {x : List Bool} (cfg : Cfg 4 Bool UniversalControl x)
    (clock : List Bool) (hs : cfg.state ≠ none)
    (hq : ∀ bits halt, cfg.state ≠ some (.applyRecord bits halt)) :
    timedInterpreter.step (timedLift cfg clock) = timedLift (timedCutInterpreter.step cfg) clock := by
  cases he : cfg.state with
  | none => exact (hs he).elim
  | some q =>
    have hq' : ∀ bits halt, q ≠ .applyRecord bits halt := by
      intro bits halt hh; apply hq bits halt; simpa [hh] using he
    have hr : (fun i => (timedLift cfg clock).workTapeSymbols (i.castAdd 2)) =
        cfg.workTapeSymbols := by
      funext i; fin_cases i <;> rfl
    have hi : (timedLift cfg clock).inputSymbol = cfg.inputSymbol := rfl
    have htr : timedInterpreter.tr (.work q) (timedLift cfg clock).inputSymbol
        (timedLift cfg clock).workTapeSymbols =
        timedAction (universalInterpreter.tr q cfg.inputSymbol cfg.workTapeSymbols) := by
      cases q <;> first
        | exact (hq' _ _ rfl).elim
        | simp only [timedInterpreter, hr, hi]
    have hstate : (timedLift cfg clock).state = some (.work q) := by simp [timedLift, he]
    conv_lhs => unfold MultiTapeTM.step; rw [hstate]; dsimp only
    rw [htr, timedAction_apply]
    simp only [MultiTapeTM.step, he, timedCut_regular q hq']

/-- A stopped lookup with a live endpoint can be replayed unchanged. No countdown
or output phase is visited in its interior. -/
private lemma timed_replay {x : List Bool} (cfg : Cfg 4 Bool UniversalControl x)
    (clock : List Bool) (t : ℕ) (ht : (timedCutInterpreter.runFrom cfg t).state ≠ none) :
    timedInterpreter.runFrom (timedLift cfg clock) t =
      timedLift (timedCutInterpreter.runFrom cfg t) clock := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (timedCut_live_before cfg (by omega) ht),
      timed_regular_step _ clock (timedCut_live_before cfg (by omega) ht)
        (timedCut_no_record cfg (by omega) ht), MultiTapeTM.runFrom_succ_eq_step']

/-- A single active tape lane, with every inactive tape taken from a base
configuration. This supports exact setup transductions in a multi-tape machine. -/
private def timed_laneCfg {A S : Type} {k : ℕ} {x : List A}
    (base : Cfg k A S x) (lane : Fin k) (q : Option S)
    (z : ℤ) (l r : List (Option A)) : Cfg k A S x :=
  ⟨q, base.inputPos, Function.update base.workTapes lane (FinTM.sweepTape z l r),
    Function.update base.workTapePos lane z, base.output⟩

/-- An action that writes and moves just one lane, leaving input and output
stationary. -/
private def timed_laneAction {A S : Type} {k : ℕ} (lane : Fin k) (q : S)
    (s : Option A) (d : SignType) : Action k A S :=
  ⟨0, Function.update (fun _ => (none, 0)) lane (some s, d), none, some q⟩

/-- The active lane reads the first unprocessed zipper entry. -/
private lemma timed_laneCfg_read {A S : Type} {k : ℕ} {x : List A}
    (base : Cfg k A S x) (lane : Fin k) (q : Option S)
    (z : ℤ) (l r : List (Option A)) :
    (timed_laneCfg base lane q z l r).workTapeSymbols lane = r.head?.join := by
  simp only [timed_laneCfg, Cfg.workTapeSymbols, Function.update_self, FinTM.sweepTape_read]

/-- The right-moving zipper identity lifts to one lane of any machine. -/
private lemma timed_laneCfg_right {A S : Type} {k : ℕ} {x : List A}
    (base : Cfg k A S x) (lane : Fin k) (q : Option S) (q' : S)
    (z : ℤ) (l r : List (Option A)) (a b : Option A) :
    (timed_laneAction lane q' b .pos).apply (timed_laneCfg base lane q z l (a :: r)) =
      timed_laneCfg base lane (some q') (z + 1) (b :: l) r := by
  apply Cfg.ext
  · rfl
  · exact moveInputPos_zero _
  · funext i
    by_cases hi : i = lane
    · subst i
      simp only [timed_laneAction, timed_laneCfg, Action.apply, Function.update_self]
      exact FinTM.sweepTape_right z l r a b
    · simp only [timed_laneAction, timed_laneCfg, Action.apply, Function.update_of_ne hi]
  · funext i
    by_cases hi : i = lane
    · subst i
      simp [timed_laneAction, timed_laneCfg]
    · simp [timed_laneAction, timed_laneCfg, hi]
  · exact List.append_nil _

/-- A finite forward transduction on one lane has exact cost equal to its word
length, without changing inactive tapes.
**Proof sketch.** The first entry supplies the local transition hypothesis.
One write-and-right step moves it into the left zipper stack, and induction
processes the remaining word. The full resulting configuration is retained. -/
private lemma timed_lane_run {A S R C : Type} {k : ℕ} {x : List A}
    (tm : MultiTapeTM k A S) (lane : Fin k)
    (state : R → S) (symbol : C → A) (visit : R → C → R × C)
    (htr : ∀ s c inp ws, ws lane = some (symbol c) →
      tm.tr (state s) inp ws = timed_laneAction lane (state (visit s c).1)
        (some (symbol (visit s c).2)) .pos)
    (base : Cfg k A S x) (as : List C) (s : R)
    (z : ℤ) (l r : List (Option A)) :
    tm.runFrom (timed_laneCfg base lane (some (state s)) z l
      (as.map (fun c => some (symbol c)) ++ r)) as.length =
    timed_laneCfg base lane (some (state (FinTM.sweepFold visit s as).1)) (z + as.length)
      (((FinTM.sweepFold visit s as).2.map (fun c => some (symbol c))).reverse ++ l) r := by
  induction as generalizing s z l with
  | nil => simp only [List.map_nil, List.nil_append, List.length_nil, MultiTapeTM.runFrom_zero,
      FinTM.sweepFold, Int.natCast_zero, add_zero, List.reverse_nil]
  | cons a as ih =>
    simp only [List.map_cons, List.cons_append, List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hr : (timed_laneCfg base lane (some (state s)) z l
        (some (symbol a) :: (as.map (fun c => some (symbol c)) ++ r))).workTapeSymbols lane =
        some (symbol a) := timed_laneCfg_read _ _ _ _ _ _
    change tm.runFrom ((tm.tr (state s) _ _).apply _) as.length = _
    rw [htr s a _ _ hr, timed_laneCfg_right, ih]
    simp only [FinTM.sweepFold, List.map_cons, List.reverse_cons, List.append_assoc,
      List.cons_append, List.nil_append, Int.natCast_add, Int.natCast_one]
    congr 1
    omega


/-- A focused clock write agrees with the generic one-lane transducer action. -/
private lemma timedAdmin_clock (q : TimedControl) (b : Option Bool) (d : SignType) :
    timedAdmin (some q) (some b, d) (none, 0) = timed_laneAction (4 : Fin 6) q b d := by
  unfold timedAdmin timed_laneAction
  congr 1
  funext i
  fin_cases i <;> rfl

/-- A borrow sweep is the same local fold as the fixed-width arithmetic function. -/
private lemma timedBorrow_fold (carry : Bool) (bs : List Bool) :
    sweepFold (fun carry b => (carry && !b, Bool.xor b carry)) carry bs = timedBorrow carry bs := by
  induction bs generalizing carry with
  | nil => rfl
  | cons b bs ih => simp only [sweepFold, timedBorrow, ih]

/-- Exact borrow transduction; neither source tapes nor buffered output are touched. -/
private lemma timed_borrow_run {x : List Bool} (base : Cfg 6 Bool TimedControl x)
    (bits : Fin 8 → Bool) (halt carry : Bool) (bs : List Bool)
    (z : ℤ) (l r : List (Option Bool)) :
    timedInterpreter.runFrom
      (timed_laneCfg base 4 (some (.borrow bits halt carry)) z l (bs.map some ++ r)) bs.length =
    timed_laneCfg base 4 (some (.borrow bits halt (timedBorrow carry bs).1))
      (z + bs.length) (((timedBorrow carry bs).2.map some).reverse ++ l) r := by
  have h := timed_lane_run timedInterpreter (4 : Fin 6) (TimedControl.borrow bits halt)
    (fun b : Bool => b) (fun carry b => (carry && !b, Bool.xor b carry))
    (by
      intro carry b inp ws hw
      simp only [timedInterpreter, hw]
      exact timedAdmin_clock _ _ _) base bs carry z l r
  simpa only [timedBorrow_fold] using h

/-- Moving the frontier of a finite zipper does not change its tape. -/
private lemma timed_sweep_shift (z : ℤ) (l w r : List (Option Bool)) :
    sweepTape z l (w ++ r) = sweepTape (z + w.length) (w.reverse ++ l) r := by
  induction w generalizing z l with
  | nil => simp
  | cons a w ih =>
    have hs : Function.update (FinTM.sweepTape z l (a :: (w ++ r))) z a =
        FinTM.sweepTape z l (a :: (w ++ r)) := by
      funext p
      by_cases hp : p = z
      · subst p
        simp [FinTM.sweepTape_read]
      · exact Function.update_of_ne hp _ _
    have hm := FinTM.sweepTape_right z l (w ++ r) a a
    rw [hs] at hm
    simp only [List.cons_append, List.length_cons, List.reverse_cons]
    rw [hm, ih]
    simp only [List.append_assoc, List.singleton_append]
    congr 1
    omega

/-- A Boolean buffer is a zipper with an empty left stack. -/
private lemma timed_buffer_zipper (bs : List Bool) :
    bufferTape bs = sweepTape 0 [] (bs.map some) := by
  funext z
  by_cases h : 0 ≤ z
  · simp only [bufferTape, if_pos h, sweepTape, not_lt.mpr h, ↓reduceIte, sub_zero,
      List.getElem?_map]
    cases bs[z.toNat]? <;> rfl
  · simp [bufferTape, sweepTape, h, show z < 0 by omega]

/-- At the right blank the full buffer occupies the reversed left zipper stack. -/
private lemma timed_buffer_zipper_end (bs : List Bool) :
    bufferTape bs = sweepTape bs.length (bs.map some).reverse [] := by
  rw [timed_buffer_zipper]
  have h := timed_sweep_shift 0 [] (bs.map some) []
  simpa using h

/-- A clock phase overrides only the clock lane and the finite control. -/
private def timedClockCfg {x : List Bool} (base : Cfg 6 Bool TimedControl x)
    (q : TimedControl) (bs : List Bool) (p : ℤ) : Cfg 6 Bool TimedControl x :=
  { base with
    state := some q
    workTapes := Function.update base.workTapes 4 (bufferTape bs)
    workTapePos := Function.update base.workTapePos 4 p }

/-- A stationary-input clock action has an explicit one-lane effect. -/
private lemma timedClock_step {x : List Bool} (base : Cfg 6 Bool TimedControl x)
    (q q' : TimedControl) (bs : List Bool) (p : ℤ) (d : SignType)
    (htr : ∀ inp ws, ws 4 = bufferTape bs p →
      timedInterpreter.tr q inp ws = timedAdmin (some q') (none, d) (none, 0)) :
    timedInterpreter.step (timedClockCfg base q bs p) = timedClockCfg base q' bs (p + d) := by
  change (timedInterpreter.tr q _ _).apply _ = _
  rw [htr _ _ (by simp [timedClockCfg, Cfg.workTapeSymbols])]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ (List.append_nil _)
  · funext i; fin_cases i <;> rfl
  · funext i
    fin_cases i <;> simp [timedAdmin, timedSix, timedClockCfg, Action.apply]

/-- Rewind from the last clock bit to the left blank, then enter the borrow pass. -/
private lemma timed_clock_back {x : List Bool} (base : Cfg 6 Bool TimedControl x)
    (bits : Fin 8 → Bool) (halt : Bool) (bs : List Bool) :
    ∀ j, j ≤ bs.length →
    timedInterpreter.runFrom (timedClockCfg base (.clockBack bits halt) bs (j - 1)) (j + 1) =
      timedClockCfg base (.borrow bits halt true) bs 0 := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    have h := timedClock_step base (.clockBack bits halt) (.borrow bits halt true) bs (-1) .pos
      (by intro inp ws hw; simp [timedInterpreter, hw])
    simpa using h
  | succ j ih =>
    intro hj
    have hr : bufferTape bs (j : ℤ) = some bs[j] := by
      rw [bufferTape_nat, List.getElem?_eq_getElem (by omega)]
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have h := timedClock_step base (.clockBack bits halt) (.clockBack bits halt) bs j .neg
      (by intro inp ws hw; simp [timedInterpreter, hw, hr])
    rw [show ((j + 1 : ℕ) : ℤ) - 1 = j by omega, h]
    simpa using ih (by omega)

/-- Borrowing rewrites the clock in exactly one pass and preserves its width. -/
private lemma timed_clock_borrow {x : List Bool} (base : Cfg 6 Bool TimedControl x)
    (bits : Fin 8 → Bool) (halt carry : Bool) (bs : List Bool) :
    timedInterpreter.runFrom (timedClockCfg base (.borrow bits halt carry) bs 0) bs.length =
    timedClockCfg base (.borrow bits halt (timedBorrow carry bs).1)
      (timedBorrow carry bs).2 bs.length := by
  have h := timed_borrow_run base bits halt carry bs 0 [] []
  have hstart : timed_laneCfg base 4 (some (.borrow bits halt carry)) 0 []
      (bs.map some ++ []) = timedClockCfg base (.borrow bits halt carry) bs 0 := by
    simp only [List.append_nil, timed_laneCfg, timedClockCfg, ← timed_buffer_zipper]
  have hend : timed_laneCfg base 4 (some (.borrow bits halt (timedBorrow carry bs).1))
      (0 + (bs.length : ℤ)) (((timedBorrow carry bs).2.map some).reverse ++ []) [] =
      timedClockCfg base (.borrow bits halt (timedBorrow carry bs).1)
        (timedBorrow carry bs).2 bs.length := by
    simp only [zero_add, List.append_nil, timed_laneCfg, timedClockCfg]
    rw [← timedBorrow_length carry bs, ← timed_buffer_zipper_end]
  rw [hstart, hend] at h
  exact h

/-- The selected action enters the clock rewind without applying a source transition. -/
private lemma timed_clock_start {x : List Bool} (cfg : Cfg 4 Bool UniversalControl x)
    (bs : List Bool) (bits : Fin 8 → Bool) (halt : Bool)
    (hs : cfg.state = some (.applyRecord bits halt)) :
    timedInterpreter.step (timedLift cfg bs) =
    timedClockCfg (timedLift cfg bs) (.clockBack bits halt) bs (bs.length - 1) := by
  have hstate : (timedLift cfg bs).state = some (.work (.applyRecord bits halt)) := by
    simp [timedLift, hs]
  unfold MultiTapeTM.step
  rw [hstate]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
  · funext i; fin_cases i <;> simp [timedInterpreter, timedAdmin, timedLift, timedSix, timedClockCfg, Action.apply]
  · funext i; fin_cases i <;> simp [timedInterpreter, timedAdmin, timedLift, timedSix, timedClockCfg, Action.apply, sub_eq_add_neg]

/-- A ready action reaches the completed borrow pass in `2w+2` transitions. -/
private lemma timed_clock_pass {x : List Bool} (cfg : Cfg 4 Bool UniversalControl x)
    (bs : List Bool) (bits : Fin 8 → Bool) (halt : Bool)
    (hs : cfg.state = some (.applyRecord bits halt)) :
    timedInterpreter.runFrom (timedLift cfg bs) (2 * bs.length + 2) =
    timedClockCfg (timedLift cfg bs) (.borrow bits halt (timedBorrow true bs).1)
      (timedBorrow true bs).2 bs.length := by
  have h0 : timedInterpreter.runFrom (timedLift cfg bs) 1 =
      timedClockCfg (timedLift cfg bs) (.clockBack bits halt) bs (bs.length - 1) := by
    exact timed_clock_start cfg bs bits halt hs
  have h1 := timed_clock_back (timedLift cfg bs) bits halt bs bs.length (le_refl _)
  have h2 := timed_clock_borrow (timedLift cfg bs) bits halt true bs
  have h := timedCut_run_join timedInterpreter (timedCut_run_join timedInterpreter h0 h1) h2
  simpa only [show 1 + (bs.length + 1) + bs.length = 2 * bs.length + 2 by omega] using h

/-- After a successful borrow, the retained action executes once. -/
private lemma timed_execute {x : List Bool} (cfg : Cfg 4 Bool UniversalControl x)
    (bs : List Bool) (bits : Fin 8 → Bool) (halt : Bool)
    (hs : cfg.state = some (.applyRecord bits halt)) :
    timedInterpreter.step { timedLift cfg bs with state := some (.execute bits halt) } =
      timedLift (universalInterpreter.step cfg) bs := by
  have hr : (fun i => (timedLift cfg bs).workTapeSymbols (i.castAdd 2)) =
      cfg.workTapeSymbols := by funext i; fin_cases i <;> rfl
  change (timedAction (universalInterpreter.tr (.applyRecord bits halt) cfg.inputSymbol
    (fun i => (timedLift cfg bs).workTapeSymbols (i.castAdd 2)))).apply
      { timedLift cfg bs with state := some (.execute bits halt) } = _
  rw [hr]
  have h := timedAction_apply cfg bs (universalInterpreter.tr (.applyRecord bits halt)
    cfg.inputSymbol cfg.workTapeSymbols)
  simpa only [MultiTapeTM.step, hs, Action.apply] using h

/-- A positive budget is decremented exactly once before the selected source action.

**Proof sketch.** Rewind the clock and run the fixed-width borrow sweep. Positive
value rules out a remaining carry at the right blank; one transition selects
execution and the next applies the source action through the buffering wrapper. -/
private lemma timed_clock_success {x : List Bool} (cfg : Cfg 4 Bool UniversalControl x)
    (bs : List Bool) (bits : Fin 8 → Bool) (halt : Bool)
    (hs : cfg.state = some (.applyRecord bits halt)) (hv : 0 < timedValue bs) :
    timedInterpreter.runFrom (timedLift cfg bs) (2 * bs.length + 4) =
      timedLift (universalInterpreter.step cfg) (timedBorrow true bs).2 := by
  have hf : (timedBorrow true bs).1 = false := by
    cases h : (timedBorrow true bs).1
    · rfl
    · have hz := (timedBorrow_underflow bs).mp h; omega
  let after := timedClockCfg (timedLift cfg bs) (.borrow bits halt false) (timedBorrow true bs).2 bs.length
  have hr : after.workTapeSymbols 4 = none := by
    simp only [after, timedClockCfg, Cfg.workTapeSymbols, Function.update_self]
    rw [← timedBorrow_length true bs, bufferTape_nat, List.getElem?_eq_none (le_refl _)]
  have he : timedInterpreter.step after =
      { timedLift cfg (timedBorrow true bs).2 with state := some (.execute bits halt) } := by
    change (timedInterpreter.tr (.borrow bits halt false) after.inputSymbol after.workTapeSymbols).apply after = _
    simp only [timedInterpreter, hr, Bool.false_eq_true, ↓reduceIte]
    refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
    · funext i; fin_cases i <;> simp [after, timedAdmin, timedClockCfg, timedLift, timedSix, Action.apply]
    · funext i; fin_cases i <;> simp [after, timedAdmin, timedClockCfg, timedLift, timedSix, Action.apply, timedBorrow_length]
  rw [show 2 * bs.length + 4 = (2 * bs.length + 2) + 1 + 1 by omega,
    MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step',
    timed_clock_pass cfg bs bits halt hs, hf]
  rw [he, timed_execute cfg _ bits halt hs]

/-- A zero budget halts with only the timeout tag, even if source emissions were buffered. -/
private lemma timed_clock_timeout {x : List Bool} (cfg : Cfg 4 Bool UniversalControl x)
    (bs : List Bool) (bits : Fin 8 → Bool) (halt : Bool)
    (hs : cfg.state = some (.applyRecord bits halt)) (hv : timedValue bs = 0) :
    let dst := timedInterpreter.runFrom (timedLift cfg bs) (2 * bs.length + 3)
    dst.state = none ∧ dst.output = [false] := by
  dsimp only
  have hf := (timedBorrow_underflow bs).mpr hv
  rw [show 2 * bs.length + 3 = (2 * bs.length + 2) + 1 by omega,
    MultiTapeTM.runFrom_succ_eq_step', timed_clock_pass cfg bs bits halt hs, hf]
  have hr : (timedClockCfg (timedLift cfg bs) (.borrow bits halt true)
      (timedBorrow true bs).2 bs.length).workTapeSymbols 4 = none := by
    simp only [timedClockCfg, Cfg.workTapeSymbols, Function.update_self]
    rw [← timedBorrow_length true bs, bufferTape_nat, List.getElem?_eq_none (le_refl _)]
  let after := timedClockCfg (timedLift cfg bs) (.borrow bits halt true)
    (timedBorrow true bs).2 bs.length
  have he : timedInterpreter.step after = (timedAdmin none (none, 0) (none, 0) (some false)).apply after := by
    change (timedInterpreter.tr (.borrow bits halt true) after.inputSymbol after.workTapeSymbols).apply after = _
    simp only [timedInterpreter, show after.workTapeSymbols 4 = none from hr, ↓reduceIte]
  change (timedInterpreter.step after).state = none ∧ (timedInterpreter.step after).output = [false]
  rw [he]
  exact ⟨rfl, rfl⟩

/-- Output-phase configurations retain all simulation and clock tapes. -/
private def timedOutputCfg {x : List Bool} (cfg : Cfg 4 Bool UniversalControl x)
    (bs : List Bool) (q : Option TimedControl) (p : ℤ) (out : List Bool) : Cfg 6 Bool TimedControl x :=
  { timedLift cfg bs with
    state := q
    workTapePos := Function.update (timedLift cfg bs).workTapePos 5 p
    output := out }

/-- A buffer scan moves only the output-buffer head and appends its designated bit. -/
private lemma timed_output_step {x : List Bool} (cfg : Cfg 4 Bool UniversalControl x)
    (bs : List Bool) (q : TimedControl) (q' : Option TimedControl) (p : ℤ)
    (out : List Bool) (d : SignType) (emit : Option Bool)
    (htr : ∀ inp ws, ws 5 = bufferTape cfg.output p →
      timedInterpreter.tr q inp ws = timedAdmin q' (none, 0) (none, d) emit) :
    timedInterpreter.step (timedOutputCfg cfg bs (some q) p out) =
      timedOutputCfg cfg bs q' (p + d) (out ++ emit.toList) := by
  change (timedInterpreter.tr q _ _).apply _ = _
  rw [htr _ _ (by simp [timedOutputCfg, timedLift, timedSix, Cfg.workTapeSymbols])]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> simp [timedOutputCfg, timedLift, timedSix, timedAdmin, Action.apply]

/-- Rewinding the buffer emits the success tag at the left blank, before any data bit. -/
private lemma timed_output_back {x : List Bool} (cfg : Cfg 4 Bool UniversalControl x)
    (bs out : List Bool) : ∀ j, j ≤ cfg.output.length →
    timedInterpreter.runFrom (timedOutputCfg cfg bs (some .emitBack) (j - 1) out) (j + 1) =
      timedOutputCfg cfg bs (some .flush) 0 (out ++ [true]) := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    have h := timed_output_step cfg bs .emitBack (some .flush) (-1) out .pos (some true)
      (by intro inp ws hw; simp [timedInterpreter, hw])
    simpa using h
  | succ j ih =>
    intro hj
    have hr : bufferTape cfg.output (j : ℤ) = some cfg.output[j] := by
      rw [bufferTape_nat, List.getElem?_eq_getElem (by omega)]
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have h := timed_output_step cfg bs .emitBack (some .emitBack) j out .neg none
      (by intro inp ws hw; simp [timedInterpreter, hw, hr])
    rw [show ((j + 1 : ℕ) : ℤ) - 1 = j by omega, h]
    simpa using ih (by omega)

/-- Flushing emits each remaining buffer bit once, then halts at the right blank.

**Proof sketch.** Induct on the unread buffer suffix. A symbol is emitted while
the buffer head advances; after the final symbol, the right blank produces the
halting transition without another emission. -/
private lemma timed_output_forward {x : List Bool} (cfg : Cfg 4 Bool UniversalControl x)
    (bs : List Bool) (r : List Bool) : ∀ l out, cfg.output = l ++ r →
    timedInterpreter.runFrom (timedOutputCfg cfg bs (some .flush) l.length out) (r.length + 1) =
      timedOutputCfg cfg bs none cfg.output.length (out ++ r) := by
  induction r with
  | nil =>
    intro l out hr
    have he : cfg.output = l := by simpa using hr
    have hread : bufferTape cfg.output (l.length : ℤ) = none := by
      rw [he, bufferTape_nat, List.getElem?_eq_none (le_refl _)]
    have h := timed_output_step cfg bs .flush none l.length out 0 none
      (by intro inp ws hw; simp [timedInterpreter, hw, hread])
    simpa [he] using h
  | cons b r ih =>
    intro l out hr
    have hread : bufferTape cfg.output (l.length : ℤ) = some b := by
      rw [hr]; exact universal_table_read l r b
    have h := timed_output_step cfg bs .flush (some .flush) l.length out .pos (some b)
      (by intro inp ws hw; simp [timedInterpreter, hw, hread])
    rw [show (b :: r).length + 1 = (r.length + 1) + 1 by simp,
      MultiTapeTM.runFrom_succ_eq_step, h]
    have hh := ih (l ++ [b]) (out ++ [b]) (by simpa [List.append_assoc] using hr)
    simpa only [SignType.pos_eq_one, SignType.coe_one, Option.toList_some,
      List.length_append, List.length_cons, List.length_nil, Nat.cast_add, Nat.cast_one,
      List.append_assoc, List.singleton_append] using hh

/-- Source halting is followed by the success tag and exactly the buffered output. -/
private lemma timed_flush {x : List Bool} (cfg : Cfg 4 Bool UniversalControl x)
    (bs : List Bool) (hs : cfg.state = none) :
    let dst := timedInterpreter.runFrom (timedLift cfg bs) (2 * cfg.output.length + 3)
    dst.state = none ∧ dst.output = true :: cfg.output := by
  dsimp only
  have hcfg : timedLift cfg bs = timedOutputCfg cfg bs (some .emitStart) cfg.output.length [] := by
    refine Cfg.ext ?_ rfl rfl ?_ rfl
    · simp [timedLift, timedOutputCfg, hs]
    · funext i; fin_cases i <;> rfl
  have h0 := timed_output_step cfg bs .emitStart (some .emitBack) cfg.output.length [] .neg none
    (by intros; rfl)
  have h1 := timed_output_back cfg bs [] cfg.output.length (le_refl _)
  have h2 := timed_output_forward cfg bs cfg.output [] [true] (by simp)
  have hstart : timedInterpreter.runFrom (timedLift cfg bs) 1 =
      timedOutputCfg cfg bs (some .emitBack) (cfg.output.length - 1) [] := by
    rw [hcfg]
    simpa using h0
  have h := timedCut_run_join timedInterpreter (timedCut_run_join timedInterpreter hstart h1) h2
  have ht : 1 + (cfg.output.length + 1) + (cfg.output.length + 1) = 2 * cfg.output.length + 3 := by omega
  rw [ht] at h
  rw [h]
  exact ⟨rfl, rfl⟩

/-- The parser is live immediately before consuming the final separator cell. -/
private lemma timedPrefix_penultimate (bs α x : List Bool) :
    (timedPrefixTM.tm.runFrom (timedPrefixTM.tm.initCfg (pairEncode (pairEncode bs α) x))
      (4 * bs.length + 2 * α.length + 5)).state ≠ none := by
  have hlen := timed_input_length bs α x
  have h0 := timedPrefix_advance bs α x bs α .codeFirst (some (.codeSecond false)) none
    (4 * bs.length + 4 + 2 * α.length) (by omega) false
    (by rw [timed_code_get]; exact (timed_pair_separator α x).1) (by intro ws; rfl)
  rw [show 4 * bs.length + 2 * α.length + 5 =
      (4 * bs.length + 4 + 2 * α.length) + 1 by omega,
    MultiTapeTM.runFrom_succ_eq_step', timedPrefix_code bs α x α.length (le_refl _),
    List.take_length, h0]
  exact Option.some_ne_none _

/-- No earlier parser step can halt, since halting is absorbing. -/
private lemma timedPrefix_live (bs α x : List Bool) (s : ℕ)
    (hs : s < 4 * bs.length + 2 * α.length + 6) :
    (timedPrefixTM.tm.runFrom (timedPrefixTM.tm.initCfg (pairEncode (pairEncode bs α) x)) s).state ≠ none := by
  intro h
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (show s ≤ 4 * bs.length + 2 * α.length + 5 by omega)
  have hp := timedPrefix_penultimate bs α x
  rw [hd, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ h] at hp
  exact hp h

/-- Only the extracted code is supplied to the scheme's canonizer. -/
private def timedCanonTM (c : EffectiveMachineCode) : FinTM Bool :=
  bufferedCompTM timedPrefixTM c.canonizer

/-- The parser's unique work tape remains the clock lane of the composed canonizer. -/
private def timedCanonClock (c : EffectiveMachineCode) : Fin (timedCanonTM c).k :=
  Fin.castAdd (1 + c.canonizer.k) (0 : Fin 1)

/-- Exact prefix-local canonizer entry retains the entire clock word unchanged. -/
private lemma timedCanon_start (c : EffectiveMachineCode) (bs α x : List Bool) :
    (timedCanonTM c).tm.runFrom ((timedCanonTM c).tm.initCfg (pairEncode (pairEncode bs α) x))
      (4 * bs.length + 3 * α.length + 8) =
    bufferedSecondCfg timedPrefixTM c.canonizer (c.canonizer.tm.initCfg α) true
      ⟨4 * bs.length + 2 * α.length + 7, by rw [timed_input_length]; omega⟩
      (fun _ => bufferTape bs) (fun _ => bs.length) := by
  change (bufferedCompTM timedPrefixTM c.canonizer).tm.runFrom _ _ = _
  rw [show 4 * bs.length + 3 * α.length + 8 =
      (4 * bs.length + 2 * α.length + 6) + (α.length + 2) by omega,
    MultiTapeTM.runFrom_add, bufferedFirstCfg_init,
    bufferedFirstCfg_run timedPrefixTM c.canonizer _ _ (fun s hs => timedPrefix_live bs α x s hs),
    timedPrefix_complete]
  exact bufferedFirstCfg_rewind timedPrefixTM c.canonizer _ rfl

/-- Canonization uses virtual input `α`; physical input and clock remain stationary. -/
private lemma timedCanon_run (c : EffectiveMachineCode) (bs α x : List Bool) (t : ℕ) :
    ∃ b, (timedCanonTM c).tm.runFrom
      ((timedCanonTM c).tm.initCfg (pairEncode (pairEncode bs α) x))
      (4 * bs.length + 3 * α.length + 8 + t) =
    bufferedSecondCfg timedPrefixTM c.canonizer
      (c.canonizer.tm.runFrom (c.canonizer.tm.initCfg α) t) b
      ⟨4 * bs.length + 2 * α.length + 7, by rw [timed_input_length]; omega⟩
      (fun _ => bufferTape bs) (fun _ => bs.length) := by
  rw [MultiTapeTM.runFrom_add, timedCanon_start]
  obtain ⟨b, -, he⟩ := bufferedSecondCfg_run timedPrefixTM c.canonizer
    (c.canonizer.tm.initCfg α) true
    (by constructor <;> intro h <;> simp_all [VirtualTag])
    (x := pairEncode (pairEncode bs α) x)
    ⟨4 * bs.length + 2 * α.length + 7, by rw [timed_input_length]; omega⟩
    (fun _ => bufferTape bs) (fun _ => bs.length) t
  exact ⟨b, he⟩

/-- Canonizer completion identifies the table, parked input, and preserved clock. -/
private lemma timedCanon_complete (c : EffectiveMachineCode) (bs α x : List Bool) :
    let cfg := (timedCanonTM c).tm.runFrom
      ((timedCanonTM c).tm.initCfg (pairEncode (pairEncode bs α) x))
      (4 * bs.length + 3 * α.length + 8 + c.canonizerTime α.length)
    cfg.state = none ∧ cfg.output = (c.decode α).serialize ∧
      cfg.inputPos.val = 4 * bs.length + 2 * α.length + 7 ∧
      cfg.workTapes (timedCanonClock c) = bufferTape bs ∧
      cfg.workTapePos (timedCanonClock c) = bs.length := by
  dsimp only
  obtain ⟨b, he⟩ := timedCanon_run c bs α x (c.canonizerTime α.length)
  rw [he]
  have hc := (computesInTime_iff _ _ _ _).mp (c.canonizer_computes α)
  refine ⟨?_, hc.2, rfl, ?_, ?_⟩
  · simp only [bufferedSecondCfg, hc.1, Option.map_none]
  · simp [bufferedSecondCfg, timedCanonClock]
  · simp [bufferedSecondCfg, timedCanonClock]

/-- The exact deadline-inclusive answer of a source configuration. -/
private def timedAnswer (M : CodeTM) {x : List Bool}
    (src : Cfg 1 Bool (Fin (M.numStates + 1)) x) (t : ℕ) : List Bool :=
  let dst := M.tm.runFrom src t
  if dst.state = none then true :: dst.output else [false]

/-- The timed interpreter finishes from every checkpoint, within a uniform ledger.

**Proof sketch.** Induct on the remaining numeric budget. Already-halted sources
flush immediately. Otherwise the stopped lookup reaches a pending action; a zero
budget times out without applying it, while a positive budget borrows once and
applies it. The recursive call is made on the successor, including its halting
state. Thus halting on the final allowed transition reaches the success branch.
The emission-length increment is at most one, leaving two units of slack per
transition in the displayed bound. -/
private lemma timed_interpret_finishes (M : CodeTM) (α : List Bool) {x : List Bool}
    (r : ℕ) : ∀ (src : Cfg 1 Bool (Fin (M.numStates + 1)) x) (p : ℕ) (bs : List Bool),
    p ≤ M.serialize.length → timedValue bs = r →
    ∃ d, d ≤ (3 * M.serialize.length + 5 * (M.numStates + 1) + 20 + 2 * bs.length + 8) * (r + 1) +
        2 * src.output.length ∧
      let dst := timedInterpreter.runFrom (timedLift (universalSimulationCfg M α src p) bs) d
      dst.state = none ∧ dst.output = timedAnswer M src r := by
  induction r with
  | zero =>
    intro src p bs hp hv
    by_cases hs : src.state = none
    · refine ⟨2 * src.output.length + 3, by omega, ?_⟩
      have h := timed_flush (universalSimulationCfg M α src p) bs
        (by simp [universalSimulationCfg, hs])
      simpa only [universalSimulationCfg, timedAnswer, MultiTapeTM.runFrom_zero, hs, ↓reduceIte] using h
    · obtain ⟨d, p', ready, hd, hp', ⟨bits, halt, hready⟩, he, ha⟩ := timedCut_live_block M α src p hp hs
      have hreplay := timed_replay (universalSimulationCfg M α src p) bs d (by rw [he, hready]; simp)
      rw [he] at hreplay
      have htimeout := timed_clock_timeout ready bs bits halt hready hv
      refine ⟨d + (2 * bs.length + 3), by omega, ?_⟩
      rw [MultiTapeTM.runFrom_add, hreplay]
      simpa only [timedAnswer, MultiTapeTM.runFrom_zero, if_neg hs] using htimeout
  | succ r ih =>
    intro src p bs hp hv
    by_cases hs : src.state = none
    · have hpos : 3 ≤
          (3 * M.serialize.length + 5 * (M.numStates + 1) + 20 + 2 * bs.length + 8) * (r + 1 + 1) := by
        have h := Nat.mul_le_mul_left
          (3 * M.serialize.length + 5 * (M.numStates + 1) + 20 + 2 * bs.length + 8)
          (show 1 ≤ r + 1 + 1 by omega)
        omega
      refine ⟨2 * src.output.length + 3, by omega, ?_⟩
      have h := timed_flush (universalSimulationCfg M α src p) bs
        (by simp [universalSimulationCfg, hs])
      simpa only [universalSimulationCfg, timedAnswer, MultiTapeTM.runFrom_of_halt _ hs, hs, ↓reduceIte] using h
    · obtain ⟨d, p', ready, hd, hp', ⟨bits, halt, hready⟩, he, ha⟩ := timedCut_live_block M α src p hp hs
      have hreplay := timed_replay (universalSimulationCfg M α src p) bs d (by rw [he, hready]; simp)
      rw [he] at hreplay
      have hc := timed_clock_success ready bs bits halt hready (by omega)
      rw [ha] at hc
      have hv' : timedValue (timedBorrow true bs).2 = r := by
        have h := timedBorrow_value bs (by omega); omega
      obtain ⟨d', hd', hfinish⟩ := ih (M.tm.step src) p' (timedBorrow true bs).2 hp' hv'
      have hlength : (M.tm.step src).output.length ≤ src.output.length + 1 := by
        rw [MultiTapeTM.step_output, List.length_append]
        cases M.tm.outputSymbol src <;> simp
      rw [timedBorrow_length] at hd'
      refine ⟨d + (2 * bs.length + 4) + d', ?_, ?_⟩
      · rw [Nat.mul_succ]
        omega
      · rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add, hreplay, hc]
        simpa only [timedAnswer, MultiTapeTM.runFrom_succ_eq_step] using hfinish

/-- The binary clock's width is bounded even at deadline zero. -/
private lemma timed_bits_length (t : ℕ) : t.bits.length ≤ t := by
  induction t using Nat.binaryRec' with
  | zero => simp
  | bit b t ht ih =>
    rw [Nat.bits_append_bit t b ht, List.length_cons]
    cases b with
    | false =>
      have hn : t ≠ 0 := by intro h; have hh := ht h; cases hh
      simp only [Nat.bit_val]
      omega
    | true => change t.bits.length + 1 ≤ 2 * t + 1; omega

/-- The five fresh lanes are table, state, simulated work, input marker, and output. -/
private def timedFive {A : Type} (core : Fin 4 → A) (buffer : A) : Fin 5 → A :=
  fun i => if i = 0 then core 0 else if i = 1 then core 1 else
    if i = 2 then core 2 else if i = 3 then core 3 else buffer

/-- Interpreter actions reuse the parser's clock lane and five fresh lanes. -/
private def timedFrameAction (M : FinTM Bool) (clock : Fin M.k)
    (a : Action 6 Bool TimedControl) : Action (M.k + 5) Bool (Option M.State ⊕ TimedControl) :=
  ⟨a.inputTape, Fin.addCases
    (Function.update (fun _ => (none, 0)) clock (a.workTapes 4))
    (timedFive (fun i => a.workTapes (i.castAdd 2)) (a.workTapes 5)),
    a.output, a.state.map Sum.inr⟩

/-- Capture the canonizer's table, then run the timed interpreter with the retained clock. -/
private def timedCaptureTM (M : FinTM Bool) (clock : Fin M.k) : FinTM Bool where
  k := M.k + (1 + 4)
  State := Option M.State ⊕ TimedControl
  tm :=
    { q₀ := .inl (some M.tm.q₀)
      tr := fun q inp work => match q with
        | .inl (some q) =>
          let a := M.tm.tr q inp (fun i => work (Fin.castAdd 5 i))
          ⟨a.inputTape, tapeBlocks a.workTapes
            (a.output.map some, if a.output = none then 0 else .pos)
            (fun _ => (none, 0)), none, some (.inl a.state)⟩
        | .inl none => controlAction 0 (some (.inr timedInterpreter.q₀))
        | .inr q => timedFrameAction M clock (timedInterpreter.tr q inp
            (timedSix (fun i => work (Fin.natAdd M.k (i.castAdd 1)))
              (work (clock.castAdd 5)) (work (Fin.natAdd M.k (4 : Fin 5))))) }

/-- Complete first-phase configuration of the output-capture wrapper. -/
private def timedCaptureCfg (M : FinTM Bool) (clock : Fin M.k) {x : List Bool}
    (cfg : Cfg M.k Bool M.State x) :
    Cfg (timedCaptureTM M clock).k Bool (timedCaptureTM M clock).State x where
  state := some (.inl cfg.state)
  inputPos := cfg.inputPos
  workTapes := tapeBlocks cfg.workTapes (bufferTape cfg.output) (fun _ _ => none)
  workTapePos := tapeBlocks cfg.workTapePos cfg.output.length (fun _ => 0)
  output := []

/-- The capture wrapper starts with a blank table and blank interpreter tapes. -/
private lemma timedCapture_init (M : FinTM Bool) (clock : Fin M.k) (x : List Bool) :
    (timedCaptureTM M clock).tm.initCfg x =
      timedCaptureCfg M clock (M.tm.initCfg x) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [timedCaptureCfg, tapeBlocks]
    · intro j
      refine Fin.addCases ?_ ?_ j <;> intro j <;>
        simp [timedCaptureCfg, tapeBlocks]
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [timedCaptureCfg, tapeBlocks]
    · intro j
      refine Fin.addCases ?_ ?_ j <;> intro j <;>
        simp [timedCaptureCfg, tapeBlocks]

/-- One live transition captures every emitted bit, including a bit emitted on
the source machine's halting transition. Administrative states remain live.

**Proof sketch.** The original work block and physical input move in lockstep.
An emission writes precisely the table's right blank and advances its head; the
buffer-append identity gives its new contents. No real output is emitted, and
the four later simulation and output-buffer tapes remain untouched. -/
private lemma timedCapture_step (M : FinTM Bool) (clock : Fin M.k) {x : List Bool}
    (cfg : Cfg M.k Bool M.State x) (hs : cfg.state ≠ none) :
    (timedCaptureTM M clock).tm.step (timedCaptureCfg M clock cfg) =
      timedCaptureCfg M clock (M.tm.step cfg) := by
  unfold MultiTapeTM.step
  cases hq : cfg.state with
  | none => exact False.elim (hs hq)
  | some q =>
    have hs' : (timedCaptureCfg M clock cfg).state = some (.inl (some q)) := by
      simp [timedCaptureCfg, hq]
    rw [hs']
    dsimp only [timedCaptureTM]
    have hr : (fun i => (timedCaptureCfg M clock cfg).workTapeSymbols
        (Fin.castAdd 5 i)) = cfg.workTapeSymbols := by
      funext i
      simp [timedCaptureCfg, Cfg.workTapeSymbols, tapeBlocks]
    have hi : (timedCaptureCfg M clock cfg).inputSymbol = cfg.inputSymbol := rfl
    rw [hr, hi]
    let a := M.tm.tr q cfg.inputSymbol cfg.workTapeSymbols
    change (⟨a.inputTape, tapeBlocks a.workTapes
      (a.output.map some, if a.output = none then 0 else .pos)
      (fun _ => (none, 0)), none, some (.inl a.state)⟩ :
      Action (M.k + (1 + 4)) Bool _).apply _ = timedCaptureCfg M clock (a.apply cfg)
    refine Cfg.ext rfl rfl ?_ ?_ ?_
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [timedCaptureCfg, tapeBlocks, Action.apply]
      · intro j
        refine Fin.addCases ?_ ?_ j
        · intro j
          cases ho : a.output <;>
            simp [timedCaptureCfg, tapeBlocks, Action.apply, ho, bufferTape_append]
        · intro j; simp [timedCaptureCfg, tapeBlocks, Action.apply]
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [timedCaptureCfg, tapeBlocks, Action.apply]
      · intro j
        refine Fin.addCases ?_ ?_ j
        · intro j
          cases ho : a.output <;> simp [timedCaptureCfg, tapeBlocks, Action.apply, ho]
        · intro j; simp [timedCaptureCfg, tapeBlocks, Action.apply]
    · simp [timedCaptureCfg, tapeBlocks, Action.apply]

/-- Lockstep capture through the first halting transition. -/
private lemma timedCapture_run (M : FinTM Bool) (clock : Fin M.k) {x : List Bool}
    (cfg : Cfg M.k Bool M.State x) (t : ℕ)
    (h : ∀ s, s < t → (M.tm.runFrom cfg s).state ≠ none) :
    (timedCaptureTM M clock).tm.runFrom (timedCaptureCfg M clock cfg) t =
      timedCaptureCfg M clock (M.tm.runFrom cfg t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (fun s hs => h s (by omega)),
      timedCapture_step M clock _ (h t (by omega)), MultiTapeTM.runFrom_succ_eq_step']

/-- Interpreter entry retains the halted canonizer's work and captured table.
Its clock lane becomes active again during interpretation. -/
private def timedCapturedCfg (M : FinTM Bool) (clock : Fin M.k) {x : List Bool}
    (cfg : Cfg M.k Bool M.State x) :
    Cfg (timedCaptureTM M clock).k Bool (timedCaptureTM M clock).State x :=
  { timedCaptureCfg M clock cfg with state := some (.inr timedInterpreter.q₀) }

/-- A halted source configuration transfers to the live interpreter entry state. -/
private lemma timedCapture_transfer (M : FinTM Bool) (clock : Fin M.k) {x : List Bool}
    (cfg : Cfg M.k Bool M.State x) (h : cfg.state = none) :
    (timedCaptureTM M clock).tm.step (timedCaptureCfg M clock cfg) =
      timedCapturedCfg M clock cfg := by
  unfold MultiTapeTM.step
  simp only [timedCaptureCfg, h]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ ?_
  · rfl
  · funext i; exact add_zero _
  · rfl

/-- Every completed source computation reaches the interpreter with the table
captured in at most one extra transition.

**Proof sketch.** Choose the first source halting time. Lockstep capture holds
through that transition; one live administrative transition enters the interpreter.
Absorbing source halting identifies this first halted configuration with the one
at the supplied time bound, so all its fields (including parked input position)
are retained, not merely its completed output. -/
private lemma timedCapture_start (M : FinTM Bool) (clock : Fin M.k) (x : List Bool) (T : ℕ)
    (h : (M.tm.runFrom (M.tm.initCfg x) T).state = none) :
    ∃ t, t ≤ T + 1 ∧
      (timedCaptureTM M clock).tm.runFrom ((timedCaptureTM M clock).tm.initCfg x) t =
        timedCapturedCfg M clock (M.tm.runFrom (M.tm.initCfg x) T) := by
  classical
  have hh : ∃ t, (M.tm.runFrom (M.tm.initCfg x) t).state = none := ⟨T, h⟩
  let t := Nat.find hh
  have ht : t ≤ T := Nat.find_min' hh h
  have hs : (M.tm.runFrom (M.tm.initCfg x) t).state = none := Nat.find_spec hh
  have he : M.tm.runFrom (M.tm.initCfg x) T = M.tm.runFrom (M.tm.initCfg x) t := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le ht
    rw [hd, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hs]
  refine ⟨t + 1, by omega, ?_⟩
  rw [MultiTapeTM.runFrom_succ_eq_step', timedCapture_init,
    timedCapture_run M clock _ t (fun s hs => Nat.find_min hh hs),
    timedCapture_transfer M clock _ hs, he]


/-- A framed interpreter configuration shares precisely the retained clock lane. -/
private def timedFrame (M : FinTM Bool) (clock : Fin M.k) {x : List Bool}
    (cfg : Cfg 6 Bool TimedControl x) (tapes : Fin M.k → ℤ → Option Bool)
    (heads : Fin M.k → ℤ) : Cfg (timedCaptureTM M clock).k Bool (timedCaptureTM M clock).State x :=
  ⟨cfg.state.map Sum.inr, cfg.inputPos,
    Fin.addCases (Function.update tapes clock (cfg.workTapes 4))
      (timedFive (fun i => cfg.workTapes (i.castAdd 2)) (cfg.workTapes 5)),
    Fin.addCases (Function.update heads clock (cfg.workTapePos 4))
      (timedFive (fun i => cfg.workTapePos (i.castAdd 2)) (cfg.workTapePos 5)), cfg.output⟩

/-- The active six reads of a frame are exactly the interpreter's reads. -/
private lemma timedFrame_reads (M : FinTM Bool) (clock : Fin M.k) {x : List Bool}
    (cfg : Cfg 6 Bool TimedControl x) (tapes : Fin M.k → ℤ → Option Bool)
    (heads : Fin M.k → ℤ) :
    timedSix (fun i => (timedFrame M clock cfg tapes heads).workTapeSymbols
      (Fin.natAdd M.k (i.castAdd 1)))
      ((timedFrame M clock cfg tapes heads).workTapeSymbols (clock.castAdd 5))
      ((timedFrame M clock cfg tapes heads).workTapeSymbols (Fin.natAdd M.k (4 : Fin 5))) =
    cfg.workTapeSymbols := by
  funext i
  fin_cases i <;> simp [timedFrame, timedSix, timedFive, Cfg.workTapeSymbols]

/-- A framed action changes only the six active lanes. Inactive canonizer data remains framed.

**Proof sketch.** Compare configuration fields. Split tape indices into the old
canonizer block and the five fresh lanes, then distinguish the retained clock
inside the old block. Each active read, write, and head move agrees with its
six-lane counterpart; the other old lanes are unchanged. -/
private lemma timedFrame_apply (M : FinTM Bool) (clock : Fin M.k) {x : List Bool}
    (cfg : Cfg 6 Bool TimedControl x) (tapes : Fin M.k → ℤ → Option Bool)
    (heads : Fin M.k → ℤ) (a : Action 6 Bool TimedControl) :
    (timedFrameAction M clock a).apply (timedFrame M clock cfg tapes heads) =
      timedFrame M clock (a.apply cfg) tapes heads := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases (m := M.k) (n := 5) ?_ ?_ i
    · intro j
      by_cases hj : j = clock
      · subst j
        simp only [timedFrameAction, timedFrame, Action.apply, Fin.addCases_left, Function.update_self]
      · simp [timedFrameAction, timedFrame, Action.apply, hj, Function.update_of_ne]
    · intro j
      fin_cases j <;> simp [timedFrameAction, timedFrame, timedFive, Action.apply]
  · funext i
    refine Fin.addCases (m := M.k) (n := 5) ?_ ?_ i
    · intro j
      by_cases hj : j = clock
      · subst j
        simp only [timedFrameAction, timedFrame, Action.apply, Fin.addCases_left, Function.update_self]
      · simp [timedFrameAction, timedFrame, Action.apply, hj, Function.update_of_ne]
    · intro j
      fin_cases j <;> simp [timedFrameAction, timedFrame, timedFive, Action.apply]

/-- Every interpreter transition lifts to the assembled machine, including final halting. -/
private lemma timedFrame_step (M : FinTM Bool) (clock : Fin M.k) {x : List Bool}
    (cfg : Cfg 6 Bool TimedControl x) (tapes : Fin M.k → ℤ → Option Bool)
    (heads : Fin M.k → ℤ) :
    (timedCaptureTM M clock).tm.step (timedFrame M clock cfg tapes heads) =
      timedFrame M clock (timedInterpreter.step cfg) tapes heads := by
  cases hs : cfg.state with
  | none =>
    rw [MultiTapeTM.step_of_halt hs,
      MultiTapeTM.step_of_halt (show (timedFrame M clock cfg tapes heads).state = none by simp [timedFrame, hs])]
  | some q =>
    have hstate : (timedFrame M clock cfg tapes heads).state = some (.inr q) := by simp [timedFrame, hs]
    conv_lhs => unfold MultiTapeTM.step; rw [hstate]; dsimp only [timedCaptureTM]
    have hi : (timedFrame M clock cfg tapes heads).inputSymbol = cfg.inputSymbol := rfl
    rw [timedFrame_reads, hi, timedFrame_apply]
    simp only [MultiTapeTM.step, hs]

/-- Full interpreter runs lift without changing the inactive frame. -/
private lemma timedFrame_run (M : FinTM Bool) (clock : Fin M.k) {x : List Bool}
    (cfg : Cfg 6 Bool TimedControl x) (tapes : Fin M.k → ℤ → Option Bool)
    (heads : Fin M.k → ℤ) (t : ℕ) :
    (timedCaptureTM M clock).tm.runFrom (timedFrame M clock cfg tapes heads) t =
      timedFrame M clock (timedInterpreter.runFrom cfg t) tapes heads := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih, timedFrame_step, MultiTapeTM.runFrom_succ_eq_step']

/-- Capturing a completed canonizer yields the initial six-lane interpreter frame.

**Proof sketch.** Compare the five configuration fields, splitting old and fresh
lanes. At the retained clock, use the parser completion identities for its contents
and head; the remaining lanes are the captured table and fresh blank tapes. -/
private lemma timedCaptured_frame (M : FinTM Bool) (clock : Fin M.k) {x : List Bool}
    (src : Cfg M.k Bool M.State x) (bs : List Bool)
    (ht : src.workTapes clock = bufferTape bs) (hh : src.workTapePos clock = bs.length) :
    timedCapturedCfg M clock src =
      timedFrame M clock (timedLift (timedCut_InterpreterInitial src.inputPos src.output) bs)
        src.workTapes src.workTapePos := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases (m := M.k) (n := 5) ?_ ?_ i
    · intro j
      by_cases hj : j = clock
      · subst j; simp [timedCapturedCfg, timedCaptureCfg, timedFrame, timedLift, timedSix, tapeBlocks, ht]
      · simp [timedCapturedCfg, timedCaptureCfg, timedFrame, timedLift, timedSix, tapeBlocks, hj]
    · intro j
      fin_cases j <;> simp [timedCapturedCfg, timedCaptureCfg, timedFrame, timedLift,
        timedSix, timedFive, timedCut_InterpreterInitial, universalFour, tapeBlocks] <;> rfl
  · funext i
    refine Fin.addCases (m := M.k) (n := 5) ?_ ?_ i
    · intro j
      by_cases hj : j = clock
      · subst j; simp [timedCapturedCfg, timedCaptureCfg, timedFrame, timedLift, timedSix, tapeBlocks, hh]
      · simp [timedCapturedCfg, timedCaptureCfg, timedFrame, timedLift, timedSix, tapeBlocks, hj]
    · intro j
      fin_cases j <;> simp [timedCapturedCfg, timedCaptureCfg, timedFrame, timedLift,
        timedSix, timedFive, timedCut_InterpreterInitial, universalFour, tapeBlocks] <;> rfl

/-- The complete timed universal machine has finite control and finitely many tapes. -/
private def timedUniversalTM (c : EffectiveMachineCode) : FinTM Bool :=
  timedCaptureTM (timedCanonTM c) (timedCanonClock c)

/-- The part of startup depending only on the code representation. -/
private def timedStartupBound (c : EffectiveMachineCode) (α : List Bool) : ℕ :=
  3 * α.length + c.canonizerTime α.length + (c.decode α).serialize.length +
    2 * (Nat.bits (c.decode α).numStates).length + 2 * (c.decode α).tm.q₀.val + 16

/-- The canonical header endpoint is inside the complete serialization. -/
private lemma timed_header_bound (M : CodeTM) :
    2 * (Nat.bits M.numStates).length + 2 + M.tm.q₀.val + 1 ≤ M.serialize.length := by
  obtain ⟨records, hr⟩ := universal_serialization_header M
  rw [hr, universal_pair_length]
  simp only [List.length_append, List.length_replicate, List.length_cons]
  omega

/-- Full startup retains the binary deadline, canonizes `α` alone, and reaches
an initialized source checkpoint within `4|bits|` plus a code-only constant.

**Proof sketch.** Run the prefix-local canonizer and capture its serialization.
Transfer to the framed interpreter, replay the stopped initialization gadgets,
and identify the initialized source checkpoint using the nested-pair length.
Add the canonizer, transfer, and header-initialization costs. -/
private lemma timed_initialized (c : EffectiveMachineCode) (bs α x : List Bool) :
    ∃ (t : ℕ) (tapes : Fin (timedCanonTM c).k → ℤ → Option Bool)
      (heads : Fin (timedCanonTM c).k → ℤ),
      t ≤ 4 * bs.length + timedStartupBound c α ∧
      (timedUniversalTM c).tm.runFrom
        ((timedUniversalTM c).tm.initCfg (pairEncode (pairEncode bs α) x)) t =
      timedFrame (timedCanonTM c) (timedCanonClock c)
        (timedLift (universalSimulationCfg (c.decode α) (pairEncode bs α)
          ((c.decode α).tm.initCfg x)
          (2 * (Nat.bits (c.decode α).numStates).length + 2 + (c.decode α).tm.q₀.val + 1)) bs)
        tapes heads := by
  let T := 4 * bs.length + 3 * α.length + 8 + c.canonizerTime α.length
  let src := (timedCanonTM c).tm.runFrom
    ((timedCanonTM c).tm.initCfg (pairEncode (pairEncode bs α) x)) T
  have hc := timedCanon_complete c bs α x
  obtain ⟨t, ht, he⟩ := timedCapture_start (timedCanonTM c) (timedCanonClock c)
    (pairEncode (pairEncode bs α) x) T hc.1
  obtain ⟨records, hrecords⟩ := universal_serialization_header (c.decode α)
  have hinit := timedCut_Interpreter_initialize src.inputPos (c.decode α).serialize
    (Nat.bits (c.decode α).numStates) records (c.decode α).tm.q₀.val hrecords
  let d := (c.decode α).serialize.length + 2 * (Nat.bits (c.decode α).numStates).length +
    2 * (c.decode α).tm.q₀.val + 7
  have hi := timed_replay (timedCut_InterpreterInitial src.inputPos (c.decode α).serialize) bs d
    (by rw [hinit]; exact Option.some_ne_none _)
  rw [hinit] at hi
  refine ⟨t + d, src.workTapes, src.workTapePos, ?_, ?_⟩
  · dsimp only [timedStartupBound, d, T] at *; omega
  · change (timedCaptureTM (timedCanonTM c) (timedCanonClock c)).tm.runFrom _ _ = _
    rw [MultiTapeTM.runFrom_add, he, timedCaptured_frame _ _ _ bs hc.2.2.2.1 hc.2.2.2.2]
    have ho : src.output = (c.decode α).serialize := hc.2.1
    rw [ho, timedFrame_run, hi]
    congr 2
    apply Cfg.ext
    · rfl
    · apply Fin.ext
      have hp : src.inputPos.val = 4 * bs.length + 2 * α.length + 7 := hc.2.2.1
      simp only [universalEvalCfg, timedCut_InterpreterBase, universalSimulationCfg,
        universalInputPos, MultiTapeTM.initCfg, Fin.val_mk]
      change src.inputPos.val = 2 * (pairEncode bs α).length + 2 + 1
      have hlen := universal_pair_length bs α
      omega
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> simp [universalEvalCfg, timedCut_InterpreterBase,
        universalSimulationCfg, universalFour, Nat.cast_add]
    · rfl

/-- Absorb clock-width work and fixed startup into a code-only quadratic coefficient.

**Proof sketch.** Write n = t + 1. Both the clock width and n are at most n squared.
Bound startup by (S + 4) n squared, and the interpreter coefficient by (B + 10) n;
its multiplication by n supplies the remaining quadratic term. -/
private lemma timed_cost_bound (S B t w s d : ℕ) (hw : w ≤ t)
    (hs : s ≤ 4 * w + S) (hd : d ≤ (B + 2 * w + 8) * (t + 1)) :
    s + d ≤ (S + B + 14) * (t + 1) ^ 2 := by
  have hn : 1 ≤ t + 1 := by omega
  have hsq : t + 1 ≤ (t + 1) ^ 2 := by
    calc t + 1 = (t + 1) * 1 := by omega
      _ ≤ (t + 1) * (t + 1) := Nat.mul_le_mul_left _ hn
      _ = (t + 1) ^ 2 := by ring
  have hs' : s ≤ (S + 4) * (t + 1) ^ 2 := by
    have hw' := Nat.mul_le_mul_left 4 (show w ≤ (t + 1) ^ 2 by omega)
    have hS := Nat.mul_le_mul_left S (show 1 ≤ (t + 1) ^ 2 by omega)
    calc s ≤ 4 * w + S := hs
      _ ≤ 4 * (t + 1) ^ 2 + S * (t + 1) ^ 2 := by omega
      _ = (S + 4) * (t + 1) ^ 2 := by ring
  have hb : B + 2 * w + 8 ≤ (B + 10) * (t + 1) := by
    have hB := Nat.mul_le_mul_left (B + 8) hn
    have hw' := Nat.mul_le_mul_left 2 (show w ≤ t + 1 by omega)
    calc B + 2 * w + 8 ≤ (B + 8) * (t + 1) + 2 * (t + 1) := by omega
      _ = (B + 10) * (t + 1) := by ring
  calc s + d ≤ (S + 4) * (t + 1) ^ 2 + (B + 2 * w + 8) * (t + 1) :=
      Nat.add_le_add hs' hd
    _ ≤ (S + 4) * (t + 1) ^ 2 + ((B + 10) * (t + 1)) * (t + 1) :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ hb) _
    _ = (S + B + 14) * (t + 1) ^ 2 := by ring

/-- The assembled finite machine computes the exact bounded answer uniformly in the input.

**Proof sketch.** Join the initialized outer run to the bounded inner run, lifting
the latter through the inactive canonizer frame. Its halted state and exact answer
give a completed computation; the clock-width estimate and cost ledger enlarge
the time bound to the stated code-dependent quadratic budget. -/
private lemma timed_computes (c : EffectiveMachineCode) (α x : List Bool) (t : ℕ) :
    (timedUniversalTM c).ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x)
      (timedAnswer (c.decode α) ((c.decode α).tm.initCfg x) t)
      ((timedStartupBound c α + universalBlockBound c α + 14) * (t + 1) ^ 2) := by
  obtain ⟨s, tapes, heads, hs, hstart⟩ := timed_initialized c (Nat.bits t) α x
  obtain ⟨d, hd, hfinish⟩ := timed_interpret_finishes (c.decode α) (pairEncode (Nat.bits t) α) t
    ((c.decode α).tm.initCfg x)
    (2 * (Nat.bits (c.decode α).numStates).length + 2 + (c.decode α).tm.q₀.val + 1)
    (Nat.bits t) (timed_header_bound (c.decode α)) (timedValue_bits t)
  have htime : s + d ≤
      (timedStartupBound c α + universalBlockBound c α + 14) * (t + 1) ^ 2 := by
    apply timed_cost_bound _ _ _ _ _ _ (timed_bits_length t) hs
    simpa only [universalBlockBound, MultiTapeTM.initCfg, Cfg.init, List.length_nil,
      Nat.mul_zero, Nat.add_zero] using hd
  have hcompute : (timedUniversalTM c).ComputesInTime
      (pairEncode (pairEncode (Nat.bits t) α) x)
      (timedAnswer (c.decode α) ((c.decode α).tm.initCfg x) t) (s + d) := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_add, hstart]
    change ((timedCaptureTM (timedCanonTM c) (timedCanonClock c)).tm.runFrom _ d).state = none ∧
      ((timedCaptureTM (timedCanonTM c) (timedCanonClock c)).tm.runFrom _ d).output = _
    rw [timedFrame_run]
    exact ⟨by simp only [timedFrame, hfinish.1, Option.map_none], hfinish.2⟩
  exact hcompute.mono htime

/-- **The time-bounded universal machine** [AB09, §1.4.1, "Universal TM with time
bound"]: a single machine that, given `⟨⟨⌞t⌟, α⟩, x⟩` (clock and code first, input
last), simulates the machine `α` denotes on `x` for at most `t` steps, reporting
success (`true :: output`) or timeout (`[false]`).

**Proof sketch.** Extend the simulation of `Turing.universal` with a binary
countdown clock on a further work tape, initialized from `⌞t⌟ = Nat.bits t` (parsed
from the doubled-bit region; cost `O(t + 1)`, within budget). Each simulated step
costs an additional `O((Nat.bits t).length + 1)` for the decrement, whence the
quadratic budget; `M`'s emissions are buffered on a work tape rather than emitted
(their total length is at most `t`, by `Turing.MultiTapeTM.output_length_le`).
Halting is checked after each simulated transition, **including the `t`-th**: if the
simulated machine has halted by the time the clock expires — deadline included —
`U` emits `true` and flushes the buffer; otherwise it emits `false`. At `t = 0` no
initialized machine has halted (`Turing.FinTM.not_computesInTime_zero`), and the
timeout branch applies (audit finding 6). The two cases below are exhaustive:
either some output witnesses halting within `t`, or every output fails to. -/
theorem timed_universal (c : EffectiveMachineCode) :
    ∃ U : FinTM Bool, ∀ α : List Bool, ∃ C : ℕ, ∀ (x : List Bool) (t : ℕ),
      (∀ output : List Bool,
        (c.decode α).toFinTM.ComputesInTime x output t →
        U.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x)
          (true :: output) (C * (t + 1) ^ 2)) ∧
      ((∀ output : List Bool, ¬(c.decode α).toFinTM.ComputesInTime x output t) →
        U.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x)
          [false] (C * (t + 1) ^ 2)) := by
  refine ⟨timedUniversalTM c, fun α =>
    ⟨timedStartupBound c α + universalBlockBound c α + 14, ?_⟩⟩
  intro x t
  have hu := timed_computes c α x t
  constructor
  · intro output hsource
    obtain ⟨hh, ho⟩ := (computesInTime_iff _ _ _ _).mp hsource
    simpa only [timedAnswer, hh, if_pos, ho] using hu
  · intro hsource
    have hh : ((c.decode α).tm.runFrom ((c.decode α).tm.initCfg x) t).state ≠ none := by
      intro hhalt
      exact hsource _ ((computesInTime_iff _ _ _ _).mpr ⟨hhalt, rfl⟩)
    simpa only [timedAnswer, if_neg hh] using hu

/-- **The concrete bounded-answer export** [AB09, §1.4.1, time-bounded universal
simulation, with the realized constant]: the single simulator behind
`Turing.timed_universal`, with its code-dependent quadratic coefficient written
out in public vocabulary — the startup part
`3|α| + canonizerTime(|α|) + |serialize| + 2·|bits(numStates)| + 2·q₀ + 16`
plus the interpreter part `Turing.universalBlockBound` plus `14`. One simulator
is chosen **before** the code, the input, and the deadline; both the success
clause and the timeout clause of `Turing.timed_universal` are preserved
verbatim.

This is the maintainer export mandated by the Chapter-2 phase-3 audit and
requested by the epoch-2 TMSAT delivery (bridge protocol, step 3): the Chapter-2
bridge `timed_universal_quantitative` is discharged from this theorem by
monotonicity, after its side's arithmetic bound on this displayed coefficient.
No bound is asserted on the arbitrary existential witness of
`Turing.timed_universal` — the witness exhibited here is the concrete machine of
its proof, and the displayed coefficient is that proof's realized constant. No
Chapter-2 notion appears. New public surface, flagged for the shared
infrastructure audit round.

**Proof sketch.** `timed_computes` states exactly this bound for the concrete
simulator, with the startup written as `timedStartupBound`, whose definition is
the displayed startup expression; the two clauses then follow from the
deadline-inclusive answer `timedAnswer` by the same case analysis as
`Turing.timed_universal` (success: the halted source's output is reported behind
`true`; timeout: no completed output exists, so the source configuration is
live and the answer is `[false]`). -/
theorem timed_universal_concrete (c : EffectiveMachineCode) :
    ∃ U : FinTM Bool, ∀ (α x : List Bool) (t : ℕ),
      (∀ output : List Bool,
        (c.decode α).toFinTM.ComputesInTime x output t →
        U.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x)
          (true :: output)
          ((3 * α.length + c.canonizerTime α.length +
              (c.decode α).serialize.length +
              2 * (Nat.bits (c.decode α).numStates).length +
              2 * (c.decode α).tm.q₀.val + 16 +
              universalBlockBound c α + 14) * (t + 1) ^ 2)) ∧
      ((∀ output : List Bool, ¬(c.decode α).toFinTM.ComputesInTime x output t) →
        U.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x)
          [false]
          ((3 * α.length + c.canonizerTime α.length +
              (c.decode α).serialize.length +
              2 * (Nat.bits (c.decode α).numStates).length +
              2 * (c.decode α).tm.q₀.val + 16 +
              universalBlockBound c α + 14) * (t + 1) ^ 2)) := by
  refine ⟨timedUniversalTM c, fun α x t => ?_⟩
  -- The displayed coefficient is definitionally `timedStartupBound` expanded.
  have hu : (timedUniversalTM c).ComputesInTime
      (pairEncode (pairEncode (Nat.bits t) α) x)
      (timedAnswer (c.decode α) ((c.decode α).tm.initCfg x) t)
      ((3 * α.length + c.canonizerTime α.length +
          (c.decode α).serialize.length +
          2 * (Nat.bits (c.decode α).numStates).length +
          2 * (c.decode α).tm.q₀.val + 16 +
          universalBlockBound c α + 14) * (t + 1) ^ 2) :=
    timed_computes c α x t
  constructor
  · intro output hsource
    obtain ⟨hh, ho⟩ := (computesInTime_iff _ _ _ _).mp hsource
    simpa only [timedAnswer, hh, if_pos, ho] using hu
  · intro hsource
    have hh : ((c.decode α).tm.runFrom ((c.decode α).tm.initCfg x) t).state ≠ none := by
      intro hhalt
      exact hsource _ ((computesInTime_iff _ _ _ _).mpr ⟨hhalt, rfl⟩)
    simpa only [timedAnswer, if_neg hh] using hu

end Turing


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


## ===== TCSlib/Complexity/TuringMachine.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Configuration
import TCSlib.Complexity.TuringMachine.Deterministic
import TCSlib.Complexity.TuringMachine.StateRenaming
import TCSlib.Complexity.TuringMachine.Finite
import TCSlib.Complexity.TuringMachine.Nondeterministic
import TCSlib.Complexity.TuringMachine.Oracle
import TCSlib.Complexity.TuringMachine.Simulation
import TCSlib.Complexity.TuringMachine.Sweep
import TCSlib.Complexity.TuringMachine.Composition
import TCSlib.Complexity.TuringMachine.Build.Convention
import TCSlib.Complexity.TuringMachine.Build.Wrappers
import TCSlib.Complexity.TuringMachine.Build.Loop
import TCSlib.Complexity.TuringMachine.Build.Primitives
import TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction
import TCSlib.Complexity.TuringMachine.Robustness.SingleTape
import TCSlib.Complexity.TuringMachine.Robustness.Bidirectional
import TCSlib.Complexity.TuringMachine.Robustness.ObliviousSchedule
import TCSlib.Complexity.TuringMachine.Robustness.ObliviousCandidate
import TCSlib.Complexity.TuringMachine.Robustness.ObliviousSetup
import TCSlib.Complexity.TuringMachine.Robustness.ObliviousLedger
import TCSlib.Complexity.TuringMachine.Robustness.Oblivious
import TCSlib.Complexity.TuringMachine.Encoding
import TCSlib.Complexity.TuringMachine.CodeParser
import TCSlib.Complexity.TuringMachine.MathlibBridge
import TCSlib.Complexity.TuringMachine.UniversalStartup
import TCSlib.Complexity.TuringMachine.UniversalInterpreter
import TCSlib.Complexity.TuringMachine.UniversalBlock
import TCSlib.Complexity.TuringMachine.Universal

/-!
# Complexity — Turing machines

The multi-tape Turing machine model underlying the Arora-Barak formalization
(see `AroraBarakChapter1Plan.md`): a machine-free configuration/action layer, the
deterministic machine with time and space semantics, the bundled finite layer over which
all complexity classes are stated, and oracle machines as a wrapper over the same
configurations.

The core model files are vendored from cslib
(https://github.com/leanprover/cslib, commit a3747758, 2026-09-14); see the file headers
for the local modifications.

## Contents

* `Configuration` — configurations `Cfg`, actions `Action` and their application; the
  space measure. Nothing here mentions a machine (vendored).
* `Deterministic` — `MultiTapeTM`, the step/run semantics, time and space bounds
  (vendored).
* `StateRenaming` — transport of actions, configurations, and machines along maps
  of the state type; shared by the oracle embedding and the code normal form.
* `Finite` — the bundled `FinTM` layer carrying `Fintype`/`DecidableEq` state instances;
  all headline definitions are stated over it.
* `Nondeterministic` — binary-choice nondeterministic machines [AB09, §2.1.2]:
  choice-word run semantics, all-branch halting, the bundled `FinNDTM` layer, and the
  deterministic embedding (the classes live in `ClassNP/NTIME`).
* `Oracle` — oracle machines `OracleTM` [AB09, §3.4]: same configurations, oracle-dependent
  step; the embedding of plain machines and its oracle-independence sanity theorems.
* `Simulation` — generic machine-construction gadgets: emission chains, control
  actions, disjoint tape-block embeddings with lockstep run lemmas, the input-head
  rewind, and the two-machine branch union.
* `Sweep` — the generic zipper/transduction layer for sweep-based tape
  simulations, with the initialized-run head/support bound.
* `Composition` — identity/constant machines and closure of time-bounded computability
  under composition; also the formal home of the append-only-output convention
  argument.
* `Build/Convention`, `Build/Wrappers`, `Build/Loop`, `Build/Primitives` — the
  machine-construction library (`machine-library-design.md`): the `Cfg.ofWords` seam
  discipline, the capture/silence and halt-redirect wrappers with the timed branch,
  the bounded-loop combinator, and the primitive catalog of timed string functions.
  Spec phase: contracts stated, fills pending, flagged for the shared infrastructure
  audit round.
* `Robustness/AlphabetReduction` — binary alphabet suffices [AB09, Claim 1.5].
* `Robustness/SingleTape` — one work tape suffices, quadratically [AB09, Claim 1.6].
* `Robustness/Bidirectional` — unidirectional tape use suffices [AB09, Claim 1.8].
* `Robustness/Oblivious` — oblivious machines and the quadratic oblivious simulation
  [AB09, Remark 1.7, Exercise 1.5] (imports the `ClassP` definitions it needs).
* `Encoding` — machines as strings [AB09, §1.4]: the code normal form `CodeTM`, the
  fixed canonical serialization, the representation-scheme laws `MachineCode`, and
  the effective scheme `EffectiveMachineCode` that the universal machine requires.
* `Universal` — the universal machine [AB09, Theorem 1.9]: the all-string evaluator
  with linear overhead and divergence preservation, the relaxed quadratic
  total-function form, and the time-bounded variant (code-first input layout).
-/


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


## ===== audits/logs/ch1-infra-sweep.log =====

shared infrastructure round: final verification sweep (57 modules)
START_UTC: 2026-10-03T07:20:00Z
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
TCSlib/Complexity/TuringMachine/Build/Wrappers.lean:135:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Wrappers.lean:190:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Wrappers.lean:206:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Wrappers.lean:226:8: warning: declaration uses 'sorry'
=== 11/57 TCSlib/Complexity/TuringMachine/Build/Loop
TCSlib/Complexity/TuringMachine/Build/Loop.lean:83:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Loop.lean:148:8: warning: declaration uses 'sorry'
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
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:66:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:79:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:96:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:113:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:131:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:145:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:160:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:173:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:191:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:212:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:237:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:258:8: warning: declaration uses 'sorry'
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
END_UTC: 2026-10-03T07:21:30Z


## ===== audits/logs/ch1-infra-axioms.log =====

shared infrastructure round: axiom attestation at the pack tree
UTC: 2026-10-03T07:22:04Z
'Turing.timed_universal_concrete' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.timed_universal_quantitative' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.timed_universal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.universal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.universal_quadratic' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.exists_effectiveMachineCode' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.HALT_not_computable' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.TMSAT_mem_NP' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Complexity.TMSAT_NPHard' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Complexity.TMSAT_NPComplete' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
ROOTS Turing.timed_universal_concrete: []
ROOTS Complexity.timed_universal_quantitative: []
ROOTS Turing.timed_universal: []
ROOTS Complexity.TMSAT_mem_NP: [Complexity.TMSAT_mem_NP]
ROOTS Complexity.TMSAT_NPHard: [Complexity.TMSAT_NPHard]
ROOTS Complexity.TMSAT_NPComplete: [Complexity.TMSAT_NPHard, Complexity.TMSAT_mem_NP]
ROOTS Complexity.NP_subset_EXP: [Complexity.enumMachine_contracts]
ROOTS Complexity.HALT_NPHard: [Complexity.enumMachine_contracts]
BRIDGE AUDIT PASS: the export and the discharged bridge are admission-free; TMSAT roots shrank exactly to their D-sites; headline and epoch-2 regressions unchanged.
---
'Turing.timed_universal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.universal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.universal_quadratic' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.exists_effectiveMachineCode' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.HALT_not_computable' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.initCfg_ofWords' depends on axioms: [propext, Quot.sound]
'Turing.Cfg.ofWords_workTapes' depends on axioms: [propext]
'Turing.capture_run' depends on axioms: [propext, sorryAx, Quot.sound]
'Turing.FinTM.redirectTM_computes' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.FinTM.redirectTM_live' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_cond' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.loop_run' depends on axioms: [propext, sorryAx, Quot.sound]
'Turing.FinTM.exists_loopTM' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_prepend' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_lengthBits' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_polyUnary' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_polyBits' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairEncodeFixed' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairFst' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairSnd' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairValid' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairLenCheck' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_stripLast' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_splitSolve' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_incFixed' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
lean exit: 0
