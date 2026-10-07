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
