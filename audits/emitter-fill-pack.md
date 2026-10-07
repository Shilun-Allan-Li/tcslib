# External audit pack — the emitter increment, fill audit

Audits the **proofs** of the emitter increment: four Codex fill
deliveries (W, P, L, P2) closing all **seven** contracts of the layer
whose statements closed a three-round adversarial gate
(`audits/emitter-infra-resolutions.md`), with **271 new private
declarations** and zero removals. The **statements are not in question
here** — your own three rounds audited them, refuted two construction
sketches, derived the envelopes, and bound the fills to those
derivations; this round is the companion proof audit in the mold of
the machine-library fill gate: proof correctness and helper hygiene
against the frozen statements, your recorded construction plans, and
the binding disciplines of the resolutions. Gate closes on **zero
blockers/majors**. Record findings in
`audits/emitter-fill-findings.md`.

**Evidence separation.** Out of scope: the seven statements and the
transformers/vocabulary (the closed statement gate); the harvest
sources (`e3c*` in `ClassNP/Nondeterminism.lean` — campaign material
under its own epoch audit; attached as the reimplementation templates,
not for re-audit); the 12 campaign admissions; the A2 reverse-host
delivery (its own campaign record). Both the P and P2 hosts disclosed
the standard `/proc` shim; the maintainer's independent sweeps on an
ordinary host supersede it.

## Maintainer-side integration attestations (verify or challenge)

Full evidence: the attached
`audits/evidence/emitter-fill/span-attestation.md`. Summary:

1. **Whole-span freeze.** Net `Build/` diff over the fill span deletes
   exactly the seven contract placeholders plus three append-only
   docstring splices; zero public drift in all four files; one
   disclosed import; private additions **+1/+119/+151, zero removals
   — 271 total**, matching the REPORTs declaration for declaration.
2. **Per-delivery verification** at each integration: checksums;
   placeholder-exact deleted-line audits; byte-identical format-patch
   replay in isolated worktrees at the pinned bases (every base
   rev-parse-generated and object-verified in its brief); each
   REPORT's byte-reconstruction freeze check shipped.
3. **Elaboration.** `Build/` admissions stepped **7 → 6 → 4 → 1 → 0**,
   each step predicted and matched by a fresh 57/57 sweep, zero
   `error:` lines; final tree **12 admissions, all campaign** (the P2
   sweep log is the complete relaunched run after a recorded
   maintainer timeout slip).
4. **Axioms.** Maintainer traversals at every integration; the final
   run asserts all seven contracts admission-free at most the standard
   triple, with every campaign closure and library regression
   unchanged. The deliveries' own wider traversals (241/387/… helper
   and generated declarations) all clean.
5. **Policy.** Build lint 0 FAIL / 2 WARN throughout; Loop 5,713 and
   Primitives 7,636 lines under their recorded exceptions (the D7
   trailing-split deferral covers the growth).

## What is under audit, and priorities

The seven proofs and 271 helpers, against the frozen statements, your
construction derivations (r1 findings 6–7; r2 findings 4–8; r3
findings 2–3), and the resolutions' binding section. Priorities,
riskiest first:

1. **L's unified bridge controller** (`emCallTM M emit` and its ~60
   lemmas): the clean-seam restoration argument as audited (clearing
   the tracked interval restores an initially blank bank — check the
   support/extent invariants actually carry it, including the
   terminal action's write and move); observed-completion dispatches
   (no `T`, `TE`, or witness runtime in the native table — verify by
   inspection); the relocation/frame lemmas preserving inactive
   tapes; the ledger landing `(24 + 13·M.k)·(T + a + b + 1)` against
   your `6 + 13·M.k + 3K` shape — re-derive the three phase bounds
   (`2T + a + 4`; `M.k(6T + 8)`; `a + 3b + 6`); first-positive-exit
   from disjoint control summands; the `M.k = 0`, empty-argument,
   empty-result cases; and that `0 < C.k` is genuinely exported by
   the chosen layout.
2. **L's forwarding host** (`emLoopHost`): `emLoop_step_prefix`/
   `emLoop_run_prefix` as the output-prefix commutation you derived;
   `emLoop_sum` against `loop_run`'s template with the output clause
   threaded (the frozen `loop_run` untouched — verify); the
   fuel/round alignment through the proved debit lemmas (indices
   exactly `0..R`, one round at `R = 0`); forwarding of the body's
   final emission; and the claimed **independence from `emit_run`**
   (their own forwarding lemmas — confirm no citation, as concurrency
   required).
3. **P2's bridge embedding** (`emitterP2*`, 68 privates): the module
   witnesses extracted once and the fixed three-bank layout; the
   erasers and `emitterP2_words_clean` landing the exact
   `stateWord` identity; the **unconditional first module action**
   with strictly-positive return tests (the entry-equals-exit
   allowance your r3 note anticipated); the outer-departure
   positivity for the one-past-end round; the exact reject seam via
   `splitRestoreTM`; the envelope assembly into the predecessor's
   `emitterSplit_of_body`; and the final public proof being exactly
   the single application claimed.
4. **P's banked layer** (83 privates): `emitterSplit_of_body`'s
   conditional reduction off `exists_loopFindTM` (hypothesis shapes
   against the audited loop discipline); `emitter_width_budget`'s
   actual-candidate-first charging; `emitterBankTM`'s simultaneous
   whole-bank clear within `6T + 7` including zero tapes (and the
   zero-time-return caveat P2 then handled); `emitter_binary_check`'s
   equivalence chain; the two closed primitives' exact conventions
   (`appendBit` at coefficient 1 with the halting-transition
   emission; `unaryToken` at coefficient 3 with the full recursive
   convention and no marker substitution).
5. **W's `emit_apply`/`emit_run`** against your componentwise
   identity (r1 finding 7): the forwarded halting emission; the guard
   semantics; the `t = 0`/halted-start edges.
6. **Harvest fidelity**: the `emCall*`/`emitterTrack*`/`emitterP2`
   relocation families against the `e3c*` templates (attached) — per
   §8 these are reimplementations; check no silent semantic drift
   (in particular the recorded actual clamped displacement, the
   origin-marker discipline, and the interval-not-history distinction
   your r3 finding 1 enforced) and that no file-scoped foreign
   private is cited.
7. **Helper hygiene** over all 271: privates match stated contracts;
   nothing public-worthy smuggled without a flag (all four REPORTs
   request zero shared lemmas); the deliveries' kernel-traversal
   claims spot-checked against the attached logs; REPORT route
   justifications (P2's bridge-embedding choice) accurate.

Severity scheme as always: blocker / major / minor / note; findings to
`audits/emitter-fill-findings.md`; this pack is immutable once sent
(errata via the resolutions file).

## Verification appendix (runs and manifest)

- Integration sweeps: `audits/logs/{emitterW-e3contA2,emitterP,emitterPL,emitterP2}-sweep.log`
  (final one attached), stepping as itemized above.
- Final closure attestation: `audits/logs/emitterP2-axioms.log`
  (attached); lint `audits/logs/emitterP2-lint.log` (attached).
- Bundle manifest — **22 attachments** after the pack: the 4 `Build/`
  sources; the 2 model files (`Finite`, `Composition`); the design
  document (§11–§11d); the gate resolutions; the 3 rounds' findings;
  the 4 fill REPORTs; the harvest template source
  (`ClassNP/Nondeterminism.lean`) and its delivery REPORT
  (`batchA-cont.md`); the span attestation; the 3 final logs; the
  57-module order list. Total
  4 + 2 + 1 + 1 + 3 + 4 + 2 + 1 + 3 + 1 = 22. All earlier logs and
  per-delivery evidence are committed at the paths the REPORTs cite.
