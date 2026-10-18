# Machine-library fill campaign — Batch L2: loop continuation (`loopHost_contracts`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch1`** — this exact branch, NOT
  `main`. Every file this brief cites exists only on it.
- Create your working branch off it (suggested name `fill/lib-L2`), record
  the base commit hash in `REPORT.md`. The required base is
  `90273dd6dea2f9e092ca7d4b5ab5dc72c96ef1ee` (the integrated checkpoint
  state — the batch-L checkpoint, batch W complete, and batch P's eleven
  fills are all already on the branch).
- **Delivery is by zip, not PR or push** (`workflow.md` §4):
  `fill-lib-L2.zip` with `REPORT.md`, the full modified source, the
  `git format-patch` series, a git bundle, the final sweep log, the
  axiom-print log, and `SHA256SUMS`.

## Context

This is the continuation of batch L. **Three documents are binding, in
this order**: the original `briefs/lib-fill-batchL.md` (freeze, ownership,
the round-3 construction ledger, verification protocol); the checkpoint
agent's own continuation instructions at
`audits/ch1-lib-agent-reports/batchL-continuation.md` (the exact admitted
declaration, the tape layout and 14-phase controller table with its
proved/pending column, and six ordered proof obligations — this is your
work plan, written by the agent who built the controller); and the
checkpoint REPORT's ledger mapping
(`audits/ch1-lib-agent-reports/batchL.md`), whose "Still required inside
`loopHost_contracts`" column enumerates what each ledger row still owes.

The single frontier is the private
**`Turing.FinTM.loopHost_contracts`** (`Build/Loop.lean`, the file's one
`sorry`): the phase assembly, canonical seam family, and uniform time
ledger for the already-defined concrete `loopHost`. Everything else in
the file is proved: `loop_run`, both terminal summation lemmas
(`loop_halted_run`, `loop_find_run`), the three public combinators'
conditional derivations, the standalone borrow machine
(`loopBorrow_correct`), the body wrapper with its release-bit and
stop-flag discipline (`loopBody_run`, `loopBody_capture`), the replay
machine (`loopHost_replay`), the input-rewind and width estimates, and
the orbit/debit arithmetic. **One fact changed since the checkpoint, in
your favor: `Turing.capture_run` is now proved** (batch W, integrated),
so the three capture helpers are admission-free and a completed fill
must end with the whole file — and all three public combinators —
**admission-free**.

## Owned file and target

- `TCSlib/Complexity/TuringMachine/Build/Loop.lean` — one target:
  `loopHost_contracts` (10 pts). Work the continuation document's six
  obligations in order: (1) relocations and fuel setup, phases 0–3;
  (2) startup return and active body calls; (3) host counter lifting,
  phases 8–10; (4) acceptance completion, flag dispatch + payload rewind
  + replay; (5) the canonical configuration family (the debit-iterate
  counter word, fuel residue retained, `loop_orbit_inv` threaded);
  (6) terminal choice and the single maximum constant.

Binding constraints carried from the audit and the checkpoint, restated:
- Per-segment counter work is bounded **worst-case by the width**
  (≤ `2·u.length + 2` standalone, lifted to the host) — no amortization
  per segment (round-3 R3-2).
- The underflow-plus-emission belongs to the **last rejecting segment**;
  the initial anchor release is free; `R = 0` with empty fuel still
  tests `s0 x` (round-3 item 4's table).
- If the last candidate accepts, the rejection terminal is unreachable
  and may be any halted configuration with the required `[false]`/`[]`
  output; seams unreachable after an earlier acceptance get their local
  contracts from their specified seams (round-3 item 4).
- Do not apply the frozen `loop_run` to the `[false]` terminal;
  `loop_halted_run` is the checked lemma for that case.
- The two output modes share the controller: `findMode = false` emits
  the fixed verdicts; `findMode = true` replays the full captured
  payload (empty payload distinguished from exhaustion by the stop-flag
  discipline, not by output).

## Admissions

**None are sanctioned.** On completion the file has zero `sorry`s and
all four public loop theorems print at most the standard triple; update
the shipped `verification/Axioms.lean` expectations exactly as the
continuation document's closure section prescribes (all combinator and
capture-helper root expectations become empty). If the budget exhausts,
deliver a further checkpoint that **shrinks the frontier**: isolate the
narrowest remaining assembly facts into named admitted privates (each
prominently reported with what it asserts and why it is believed true),
keep every completed phase proof, and update `CONTINUATION.md` — the
checkpoint discipline your predecessor set is the model.

## Environment, ground rules, out-of-scope

As the original brief, unchanged: pinned toolchain, `lake exe cache get`
once, **never `lake build`**; bootstrap the 57-module order; iterate the
owned module (position 11) plus later modules; final full fresh
57-module sweep, zero `error:` lines. Exclusive ownership; privates
listed; **statement freeze absolute** — including the five public loop
declarations and `loopHost_contracts`' own statement (it is the
continuation interface your corollaries already consume; if the
assembly genuinely needs a different interface, that is an escalation,
not an edit); docstrings stay. **10 points; continuation again if
exhausted.** The file carries a recorded 1,466-line size exception —
report the final size; do not move code out of the file. Out-of-scope
sorries now visible: the four pending primitives in
`Build/Primitives.lean` (batch P2 concurrent) and the campaign
admissions listed in the original brief.

## REPORT.md checklist

- [ ] `loopHost_contracts` proved (or the shrunken frontier named
      exactly, with per-phase status against the continuation document's
      table).
- [ ] The six obligations mapped to your discharging lemmas; the
      constant ledger's final maximum named.
- [ ] Base hash; all new private declarations listed; final file size.
- [ ] Axiom prints: all four public loop theorems and every helper —
      admission-free on completion (or the named residue, root-verified).
- [ ] The shipped `verification/Axioms.lean` expectations updated per
      the continuation document's closure section.
- [ ] Requested shared lemmas / escalations — or "none".
- [ ] Final sweep log tail; diff touches only `Build/Loop.lean`.

## Known pitfalls at this pin

The original brief's list carries over verbatim, plus the checkpoint's
hard-won specifics:
- The release bit forces one genuine source action before anchor
  recognition — startup's no-anchor guard includes time zero, active
  rounds use the strict-interior guard (continuation document,
  obligation 2).
- An unreleased anchor stop sets flag `some false`; a genuine source
  halt sets `some true` **retaining every source emission** — the
  acceptance path replaces a padded endpoint by its first halt before
  applying `capture_run`.
- The counter word at candidate `i` is
  `((fun w => (loopDebit w).1)^[i]) (Nat.bits (R x.length))` — its width
  and value lemmas are already proved; don't re-derive them.
- Fuel-phase residue (work tapes and heads) is **retained** across the
  whole seam family; `loopFrame`/`loopControl_apply` isolate active
  tracks against arbitrary residue.
- The input rewind is budgeted by the preceding run's displacement
  (`loop_input_run_le`), not by input length — keep it that way or the
  sublinear-`T` case breaks.
- `rightCfg_run`/`leftCfg_run` (public, `Simulation.lean`) are the
  intended lifting lemmas for the fuel and body sources — the
  continuation document names them per obligation.
