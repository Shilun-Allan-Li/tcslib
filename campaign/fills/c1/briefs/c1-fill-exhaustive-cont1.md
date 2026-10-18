# Ch3–4 fill campaign — C1, wave 1, E continuation 1: the exhaustive replay of a fixed NDTM (`Turing.FinNDTM.exists_exhaustiveDecider`, `ClassNP/ExhaustiveReplay.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- **Paths in this brief are those of your base** (the commit below). After your base the
  campaign moved its process records: `audits/` and `briefs/` became `campaign/`, and
  `campaign/MOVED.md` at the tip maps each old path to its new one. Read every cited file at
  your base (`git show <base>:<path>`, or after the checkout below), not at the tip. The
  environment addendum is attached to this dispatch; it is also
  `briefs/fill-environment-addendum.md` at your base.
- Before you start, confirm that `git merge-base --is-ancestor @ANCESTOR@ HEAD` succeeds. If it
  fails, **stop**. That commit contains:
  - **your target as a gated statement** (the C1 host-contracts gate,
    `audits/c1-hosts-statements-findings.md`, PASS 0/0/11; resolutions
    `audits/c1-hosts-statements-resolutions.md`), and its consumer
    `ndAcceptsWithin_decider_of_universal` (proved, in your file);
  - C1's design (`audits/evidence/c1/C1-design.md`; `E` is §3.5, and `BF := E(UN)` is the user's
    decision 2) and C1's fill plan (`audits/evidence/c1/C1-fill-plan.md`; you are wave 1's E);
  - the step clock `Turing.exists_stepClockTMVia` (B6-F1, PR #103, proved), the replay machine and
    its lemma (`ChoiceReplay`), R1's silent embedding (`Build/Embed`) and the phase host
    (`Build/Seam`);
  - **the API PRs** (the user's "Everything" rule, 2026-10-16: every definition your route reads
    has a published lemma): the specification API (PR #112), the core API (PR #116), the
    brief-inventory API (PR #118) and **the ND inventory API (PR #119, which gives this brief
    `haltsWithin_iff`, `acceptsWithin_iff`, `initCfg_eq`, the replay machine's and the extended
    configuration's fields, `clockCfg`'s fields and `Cfg.stopped_iff`)**;
  - **the first round** (2026-10-17): the worker's report
    `audits/c1-fill-agent-reports/exhaustive-1-REPORT.md` and the maintainer's review
    `audits/evidence/c1/fills/exhaustive-1/REVIEW.md`, with its probes
    `C1ReviewProbes.lean.txt` (P1–P4);
  - the fill-agent environment addendum `briefs/fill-environment-addendum.md` (**v2**: Part 1, the
    resources and the cache, applies on every host), and the
    declaration-keyed copy-text screen v3 `audits/evidence/retrofit/copy-text-screen-v3.py`;
  - **this round's inputs** (`audits/evidence/c1-fill-exhaustive-cont1/`): the import overlay, the
    import probe and the screen population. Also the order list
    `briefs/orders/c1-fill-exhaustive-cont1.txt`, the base sorry set, the screen base and the
    pre-ship log (`audits/logs/c1-fill-exhaustive-cont1-*`).
- **Before anything else, run Part 1 of `briefs/fill-environment-addendum.md`**: the preflight,
  with its stop rule (E-RES). The first round stopped at a full memory limit. If Lean cannot start,
  follow Part 2 exactly.
- **Branch at exactly that commit, not at the campaign tip:**

  ```sh
  git checkout -b fill/c1-exhaustive-cont1 @ANCESTOR@
  git rev-parse HEAD        # must print @ANCESTOR@
  ```

  Record that hash as your base in `REPORT.md`. Never rebase, merge or cherry-pick.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-c1-exhaustive-cont1.zip`. It
  contains:
  - `REPORT.md` and the full modified source;
  - a `git format-patch` series against your base, and a git bundle whose only prerequisite is
    your base;
  - the bootstrap and final sweep logs and the axiom log;
  - both screen outputs, and `SHA256SUMS`.

## Base, line numbers and what lands around you

- **Your base's Lean content is the campaign tip** (`6d18902f`, #120's head, as at round 1's base).
  The inputs commit adds no Lean change. Lines in this brief are those of that tree, **before** your
  import edit. `ClassNP/ExhaustiveReplay.lean` has 110 lines there, unchanged since #87 (the first
  round's imports and appendix were not landed). Every probe and measurement below was run there,
  against the olean snapshot of #120's replay (`oleans-lndnf`).
- **In flight, merging after your base and invisible to it:** the open stack #121–#126 (C1-E's
  statements, the ND inventory API's round 2, W's landing, the seam-layout contract, the §13d G4
  partial's landing, and the decider as a hypothesis; none touches your file or its imports); the
  five #118 briefs still out (U2-S, F5, F3 cont1, cont6, MIG-12); and UN in
  `Diagonalization/NTimeHierarchy`, which imports your file. Cite nothing they add.

## Parallel batches this round

None in `ClassNP/ExhaustiveReplay.lean`. Your consumer is already written: `BF :=
E(UN)`, `Turing.ndAcceptsWithin_decider_of_universal` (line 79, proved modulo your target), and
through it the hierarchy's top rung.

## The first round (2026-10-17)

The first round was **environment-blocked at phase 0**: the worker's host had an 8 GiB memory limit
already at its ceiling and a nearly full shared disk, so the bootstrap stalled. It delivered the
three authorized imports and an appendix, and no proof text. The maintainer's review verified the
three imports (no cycle; the overlay elaborates; the probe resolves 61/61) and **pre-authorizes
them again here**. It also probed the semantic and arithmetic parts of phase 4 and phase 1's
precondition: **`audits/evidence/c1/fills/exhaustive-1/C1ReviewProbes.lean.txt`, 0 errors, standard
axioms.** You may adopt these probes as `xr_` privates (rename `xrProbe_` to `xr_`):
- **P1** `¬ N.tm.HaltsWithin z 0`;
- **P2** the window support: after a branch of length `|w|` from `initCfg z`, every work head is
  within `|w|` of its origin, every cell beyond radius `|w|` is blank, and the output has length at
  most `|w|`;
- **P3** at an all-halting depth `L ≤ T`, acceptance within `L` and within `T` agree; **P3′** the
  first all-halting depth exists, is at least `1`, and answers as `T` does;
- **P4** the ledger's shape, `Σ_{L ≤ T} 2^L·A(L + 1) ≤ (A + 3)·2^{(A + 3)(T + 1)}`.

They cite three public names beyond round 1's list: `NDTM.stepWith_of_some`,
`NDTM.stepWith_of_halt` and `workTapePos_apply_le`. The probe includes them.

## What this is

**C1's exponential decider core** (C1's design §3.5): the trivial exponential simulation of a fixed
NDTM [AB09, §3.2], as a public generic theorem. One target, frozen:
1. **`Turing.FinNDTM.exists_exhaustiveDecider`** (line 61): for every bundled binary NDTM `N`
   there are a deterministic `E` and a constant `C` such that on every input `z` on which every
   branch of length `T` halts, `E` outputs `[true]` if `N` accepts `z` within `T` and `[false]`
   otherwise, within `C·2^{C·(T + 1)}` steps. No `|z|` term.

**The published lemmas your route reads** (ground rule 10):
- **the ND semantics** (#119): `NDTM.haltsWithin_iff`, `FinNDTM.acceptsWithin_iff`,
  `NDTM.initCfg_eq` with `Cfg.init`'s fields, `NDTM.runWith_nil`, `_cons`, `_append`,
  `runWith_of_halt`, `NDTM.HaltsWithin.mono`, `FinNDTM.AcceptsWithin.mono`;
- **the replay** (`ChoiceReplay`): `NDTM.replayTM_runFrom` (the replay lemma), `replayTM_q₀`, `_tr`,
  and `withChoiceTape`'s five fields (#119);
- **the step clock**: `Turing.exists_stepClockTMVia` (at `Γ = Bool`, `e = refl`), with `clockCfg`'s
  five fields and `Cfg.stopped_iff` (#119);
- **R1's silent embedding** (`Build/Embed`): `embedSilentTM_runFrom`, `embedSilentTM_frame`,
  `embedSilentCfg_selected_tape`, `_selected_pos`, `_cap`, `_unselected`;
- **the phase host and seams** (`Build/Seam`): `phaseHostTM_run`, `seamCompTM_run_ofCfg`,
  `seamReleaseTM_firstReturn`;
- **the rows** (`Build/Catalog`, `Build/CounterLoop`, `Simulation`): `incrementTM_run_succ_ofCfg`,
  `incrementTM_run_overflow_ofCfg`, the counter loop's run lemmas and ledger, `timed_rewind` (the
  native input head's rewind);
- **the decider form:** `FinTM.computesInTime_iff`, `MultiTapeTM.initCfg_eq`;
- the model: `MultiTapeTM.step_of_some`, `step_of_halt`, the run algebra, `Action.apply`'s fields,
  `Cfg.mapState`'s fields.

**Read first:**
- the target's docstring, whose proof sketch is binding where this brief does not refine it;
- `Turing.NDTM.replayTM_runFrom` and the step clock's docstring (its two exits, its frame clause);
- `ClassNP/Nondeterminism.lean`'s private `choiceCore` (line 247): an older replay of a fixed `N`
  on a choice word. **It is a hazard, not a model** (C1's design §3.5 expects your theorem to retire
  it later).

**Pre-ship check** (maintainer, at the base, against `oleans-lndnf`;
`audits/logs/c1-fill-exhaustive-cont1-preship.log`):
- **The import overlay**
  (`audits/evidence/c1-fill-exhaustive-cont1/ExhaustiveReplayOverlay.lean.txt`): your file with the
  three authorized imports added after line 7. It elaborates with your target's sorry warning and
  nothing else.
- **The import probe** (`C1ExhaustiveImportProbe.lean.txt`, 64 `#check`s: round 1's 61 and the
  probes' three): every public declaration this brief cites resolves from the overlay's import
  context. 0 errors, 0 warnings. Re-run it after your delivery.

## Owned regions and targets (modify these and nothing else)

| # | File:line | Target |
|---|---|---|
| 1 | `ClassNP/ExhaustiveReplay.lean:61` | `Turing.FinNDTM.exists_exhaustiveDecider` |

Your regions (line numbers before your import edit; add 3 after it):
- **(a) the imports**, as your first edit: exactly
  `import TCSlib.Complexity.TuringMachine.ChoiceReplay`,
  `import TCSlib.Complexity.TuringMachine.Build.StepClock` and
  `import TCSlib.Complexity.TuringMachine.Build.Seam`, after line 7. No other import.
- **(b) one home**, for your `private` declarations: the blank line **42**, after `namespace Turing`
  and before the target's docstring. `private` only, and no `section`, `open` or `variable` that
  leaks past one.
- **(c) the body**, the `sorry` on line **65**.
- **(d) for a partial only, a flagged "Fill appendix (C1-E)" paragraph at the end of the target's
  docstring**, before its closing ` -/` (line 60). The closer ends a text line; put it on its own
  line after your paragraph. It is library text: what is proved and what is open, with no session
  narrative.

Frozen: the module header and docstring, `ndAcceptsWithin_decider_of_universal`, the target's
statement, and every other file. The maintainer updates the module's status text at integration.

### Route (binding; the host-first rule, `policy.md` §1, `workflow.md` §2)

- **The host is the phase host** (`phaseHostTM`, `phaseHostTM_run`), over the docstring's phases:
  - the depth `L` on a counter tape, from `0`;
  - for each `L`, the words of length `L` on the choice tape, by `incrementTM` from all-`false`
    to overflow;
  - for each word, **one replay**;
  - after each replay, the flags "some branch accepted" and "some branch is live", in the control;
  - between replays, **the window clear** and the input rewind;
  - at the end of a depth, stop if no branch was live, else `L + 1`.

  Never write a second phase host, seam, embedding, counter loop or clock.
- **One replay** is `N.tm.replayTM` (the choice tape last), run silently by R1 (`embedSilentTM`,
  capturing `N`'s output) under the step clock (`exists_stepClockTMVia`), with a counter word of
  value `L`.
  - The replay lemma identifies the replayed run with `N`'s branch along the word.
  - The clock's `finish none` exit is "halted within `L`", and `timeout` is "still live at `L`".
  - The captured output decides acceptance (`[true]`).
  - Read `N`'s machine only through the replay lemma and `replayTM`'s fields. `N` is arbitrary:
    **never unfold** `N.tm.tr`, `replayTM` or `stepWith`.
- **The window clear is your leaf host**: after a replay of `L` steps every work head is within `L`
  of its origin (P2), so blanking radius `L` (a counter loop over a one-step clearing body, or two
  counter sweeps) restores the tapes. It is a new row, a private one; list it as a **promotion
  candidate**. The input head returns by `timed_rewind`. `clearTM_run_ofCfg` needs a delimited word,
  so it does not serve here directly.
- **Four machine obligations** (round 1's review, (c)), each per replay:
  1. **Restore the clock's counter.** After either exit the counter tape holds some `w'` of the same
     width, with no value specified, so re-write the value-`L` word before every replay
     (`copyTM_run_ofCfg` is allowed; `copyTM_run` is a barred R3 row).
  2. **Rewind the choice head.** The replay lemma leaves it at some `p ≤ τ`
     (`replayTM_runFrom`'s `∃ p ≤ t`). Rewind it before `incrementTM_run_succ_ofCfg` and before the
     next replay, whose lemma starts at head `0`.
  3. **Read and clear the capture tape.** It holds `bufferTape (pre ++ output)`, with its head at
     the end (`embedSilentCfg`). The `[true]` test reads it, and P2's bound
     `|output| ≤ τ ≤ L` keeps it inside the radius-`L` window.
  4. **Clear `[-L, L]` on each of `N`'s work tapes, and return every head to `0`**: heads can sit at
     negative positions, and the replay lemma's precondition is `initCfg` up to the choice tape.
- **The answer.** The first depth `L` at which every branch has halted is at most `T`
  (`NDTM.HaltsWithin.mono`). There, acceptance within `L` and within `T` agree:
  - `AcceptsWithin.mono` gives one direction;
  - the other truncates an accepting word of length `T` at `L`, using `runWith_append` and
    `runWith_of_halt`.
- **The ledger** is the docstring's, `Σ_{L ≤ T} 2^L · O_N(L + 1) ≤ C·2^{C·(T + 1)}`. Each replay
  touches at most `L + 1` input cells, so there is no `|z|` term. Prove the sum bound once, as a
  private arithmetic lemma.

## Gate guidance (binding)

- **The C1 host-contracts gate** fixed the statement (`audits/c1-hosts-statements-findings.md`). It
  quantifies over every `T` at which all branches halt, with no `T` computed. The deepening must not
  assume `T` is known, and must stop at the *first* all-halting depth.
- **Edge cases that must stay true of your proof:**
  - `T = 0` is **vacuous**: `N`'s initial configuration is live, so no `T = 0` satisfies the
    all-halting hypothesis (P1). The first all-halting depth is at least `1` (P3′). (The first
    round's brief said otherwise; round 1's review corrected it.)
  - a branch that halts with output `[false]` or `[]`: halted, not accepting;
  - an `N` with zero work tapes (`N.k = 0`): the replay machine has one tape, the choice tape;
  - the input `z = []`.

## Cited infrastructure (public and proved at the issue commit; all in `C1ExhaustiveImportProbe.lean.txt`)

The probe's names (your file's own declarations are not listed), in six groups:
- the ND semantics;
- the replay;
- the step clock;
- R1's silent embedding;
- the phase host and seams;
- the rows and the model.

**Proved modulo, exactly:** none.

## Ground rules (binding)

1. **File ownership, by region.** Only regions (a)–(d) of `ClassNP/ExhaustiveReplay.lean`. List
   every new declaration with its role.
2. **Statement freeze** over the target and every landed declaration.
3. **No new public declaration.**
4. **Escalation** on anything unprovable as stated: stop on that item, record the obstruction, and
   continue with the rest.
5. **No touching other sorries.** Cite proved material; never re-prove it.
6. **Imports.** Exactly the three in region (a).
7. **One proof per shared argument.** Never write a second phase host, seam, embedding, counter loop
   or clock, and never re-walk `Nondeterminism`'s `choiceCore`.
8. **Size.** No cap; file size alone is not a driver. Report the final line count and the public and
   private declaration counts (base: 110 lines).
9. **Continuation budget.** A partial zip states the phase reached, the open declarations (each with
   a literal "Proof sketch") and the target's axiom walk. A partial is expected and fine; an
   unreported gap is not.
10. **The pinned base, and no unfolding (user, 2026-10-16).**
    - Cite only declarations public at your base, and your file's own privates.
    - **Never unfold a definition of another file.** Read every definition through its published
      lemmas (the four API PRs and the landed lemmas the probe lists).
    - **The machine model's primitives** (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
      `Cfg.mapState`, `NDTM.stepWith`, `NDTM.runWith`) are read through their lemmas. Unfold `step`
      and `Action.apply` only for a leaf defined in your own file.
    - If a fact you need about another file's definition has no published lemma, **stop on that
      item and escalate** (ground rule 4), naming the lemma you need.
    - List every declaration you cite outside your file. If you cite more than the probe's list,
      add them to a copy of the probe and run it.
11. **MIG-1 compatibility.**
    - Cite none of the six R3 canonical rows.
    - Cite no private declaration of another file.
    - Keep your new privates under the `xr_` prefix.

### Phases (for a partial; ground rule 9)

1. The window clear (its leaf and its run).
2. One replay under the clock, silently, with its two exits read.
3. One depth: the enumeration, the flags, the clear between replays.
4. The deepening, the answer and the ledger.

## Duplication governance (binding)

Run the text-level screen **before and after**, **one run at a time, under `nice -n 10`**
(`audits/TEMPLATE.md` failure mode 5; `policy.md`, **Duplication**).
- **The population** is 7 files (`audits/evidence/c1-fill-exhaustive-cont1/screen-population.txt`):
  your file; `ChoiceReplay`; `ClassNP/Nondeterminism` (`choiceCore`, the main hazard);
  `Build/StepClock`; `Build/CounterLoop`; `ClassNP/NTIME`; and `SpaceComplexity/ExpBFS/Radius`
  (the window-support hazard, round 1's review).
- **The screen** is `audits/evidence/retrofit/copy-text-screen-v3.py`, on the repository paths.
- **The base** is `audits/logs/c1-fill-exhaustive-cont1-screen-base.txt`: **297 declarations, 106
  pairs, 36,004 characters** (MEASURED at issue).

```sh
P=audits/evidence/c1-fill-exhaustive-cont1
nice -n 10 python3 -I audits/evidence/retrofit/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/screen-population.txt) > /tmp/screen-before.txt
# after your changes, again, only when the first run has finished
nice -n 10 python3 -I audits/evidence/retrofit/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/screen-population.txt) > /tmp/screen-after.txt
```

- **No new cross-file pair** with an owned-file declaration on one side. Nothing is pre-disclosed.
- **Known hazards:** `choiceCore` and its run lemmas (`Nondeterminism`); the step clock's private
  round induction (`StepClock`). Follow their pattern, never transcribe it. A pair at 90% or more is
  a copy.
- List every new in-file pair with a one-line justification. Quote both outputs in `REPORT.md`,
  which carries **"new copies: none"** (or lists each pair).

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake build`**. Use
  `scripts/lean_check_tree.sh` for every check.
- **Bootstrap once** from `briefs/orders/c1-fill-exhaustive-cont1.txt` (**77 modules**: the upstream
  closure of your owned file, with the three imports, and of every module downstream of it, without
  the root `TCSlib`).

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < briefs/orders/c1-fill-exhaustive-cont1.txt )
  ```

  **The base sorry-warning set has 19 entries in 9 modules**
  (`audits/logs/c1-fill-exhaustive-cont1-base-sorries.txt`). Yours is
  `ClassNP/ExhaustiveReplay`'s one. Record the base list by name first, and report any difference.
- **Final checks:**
  1. `ClassNP/ExhaustiveReplay`: zero errors, no sorry warning (for a partial, exactly the open
     declarations'), and no other warning in anything you added.
  2. Every other module of the order list: zero errors, and sorry warnings exactly the base's minus
     yours.
  3. Re-run `C1ExhaustiveImportProbe.lean.txt`: 0 errors.
- **Axiom prints** for the target, `ndAcceptsWithin_decider_of_universal`, and every new private:
  within `[propext, Classical.choice, Quot.sound]`, no `sorryAx` from your target for a complete
  delivery.
- **Lint:** `python3 -I scripts/campaign_style_lint.py TCSlib/Complexity/ClassNP`, 0 FAIL (base:
  0 FAIL, 15 WARN over 21 files). No new line over 100 characters.

## REPORT.md checklist

- [ ] The target proved (or the phase reached); the base hash and the ancestor check.
- [ ] The preflight's numbers (addendum v2, Part 1).
- [ ] The three imports as the first edit, and nothing else outside regions (b)–(d).
- [ ] Every new declaration with its role; the window clear and why no row serves it; the appendix.
- [ ] The constant `C`, and the ledger.
- [ ] Promotion candidates and escalations, or "none".
- [ ] Rule 10: the declarations cited outside your file, and the probe re-run. Rule 11: a grep of
      your diff for the six R3 rows and for other files' private names.
- [ ] Duplication: both v3 screens, every new pair justified, "new copies: none".
- [ ] File size; the final sweep tail; the axiom prints; the lint line.

## Known pitfalls at this pin (hard-won)

- **Exact-length words.** `HaltsWithin` and `AcceptsWithin` quantify over words of length exactly
  `t`. `runWith_of_halt` extends a halted branch to every longer word.
- **The replay machine puts the choice tape last** (`Fin.lastCases`, `withChoiceTape`). A blank
  choice cell reads as `false` (`replayTM_tr`), and the choice head stops when the branch halts.
- **The step clock's counter is a delimited word of value `L`**, little-endian, on its last tape;
  its `finish` carries `none` for a halted body.
- **`Cfg.inputPos` is shifted by one**, and `timed_rewind` returns the input head to position `1`.
- `omega` with products as atoms (`ring` first); the exponential ledger wants `Nat.pow_le_pow_right`
  and `Nat.mul_le_mul`. The linter needs a literal "Proof sketch" before every `sorry` (partial
  only).
