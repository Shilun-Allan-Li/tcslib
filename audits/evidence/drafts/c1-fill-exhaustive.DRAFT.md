# Ch3–4 fill campaign — C1, wave 1, E: the exhaustive replay of a fixed NDTM (`Turing.FinNDTM.exists_exhaustiveDecider`, `ClassNP/ExhaustiveReplay.lean`)

> **DRAFT (maintainer, 2026-10-17). Not issued.** Measured at #120's head `6d18902f` (the tip once
> #118, #119 and #120 merge). It issues with wave 1 after #119 and #120 merge (C1's fill plan; user,
> 2026-10-17). ⟨…⟩ are filled then.

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
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
  - the fill-agent environment addendum `briefs/fill-environment-addendum.md`, and the
    declaration-keyed copy-text screen v3 `audits/evidence/retrofit/copy-text-screen-v3.py`;
  - **this round's inputs** (`audits/evidence/c1-fill-exhaustive/`): the import overlay, the import
    probe and the screen population. Also the order list `briefs/orders/c1-fill-exhaustive.txt`, the
    base sorry set, the screen base and the pre-ship log (`audits/logs/c1-fill-exhaustive-*`).
- If Lean cannot start, follow `briefs/fill-environment-addendum.md` exactly.
- **Branch at exactly that commit, not at the campaign tip:**

  ```sh
  git checkout -b fill/c1-exhaustive @ANCESTOR@
  git rev-parse HEAD        # must print @ANCESTOR@
  ```

  Record that hash as your base in `REPORT.md`. Never rebase, merge or cherry-pick.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-c1-exhaustive.zip`. It contains:
  - `REPORT.md` and the full modified source;
  - a `git format-patch` series against your base, and a git bundle whose only prerequisite is
    your base;
  - the bootstrap and final sweep logs and the axiom log;
  - both screen outputs, and `SHA256SUMS`.

## Base, line numbers and what lands around you

- **Your base's Lean content is the campaign tip after #120** (⟨BASE-LEAN⟩). The inputs commit
  adds no Lean change. Lines in this brief are those of that tree, **before** your import edit.
  `ClassNP/ExhaustiveReplay.lean` has 110 lines there, unchanged since #87. Every probe and
  measurement below was run there, against the olean snapshot of #120's replay (`oleans-lndnf`).
- **In flight, merging after your base and invisible to it:** wave 1's other four briefs (W in
  `Build/NDHost`, WC in `Build/InputWindow`, R in `NDCodeSimulator`, UN in
  `Diagonalization/NTimeHierarchy`); the six #118 briefs; C1-E's statements (#121). Cite nothing
  they add.

## Parallel batches this round

None in `ClassNP/ExhaustiveReplay.lean`. Your consumer is already written: `BF :=
E(UN)`, `Turing.ndAcceptsWithin_decider_of_universal` (line 79, proved modulo your target), and
through it the hierarchy's top rung.

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
`audits/logs/c1-fill-exhaustive-preship.log`):
- **The import overlay**
  (`audits/evidence/c1-fill-exhaustive/ExhaustiveReplayOverlay.lean.txt`): your file with the three
  authorized imports added after line 7. It elaborates with your target's sorry warning and
  nothing else.
- **The import probe** (`C1ExhaustiveImportProbe.lean.txt`, 63 `#check`s): every public
  declaration this brief cites resolves from the overlay's import context. 0 errors, 0 warnings.
  Re-run it after your delivery.

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
- **(d) a flagged "Fill appendix (C1-E)" paragraph at the end of the target's docstring**, before
  its closing ` -/` (line 60). The closer ends a text line; put it on its own line after your
  paragraph.

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
  of its origin, so blanking radius `L` (a counter loop over a one-step clearing body, or two
  counter sweeps) restores the tapes. It is a new row, a private one; list it as a **promotion
  candidate**. The input head returns by `timed_rewind`.
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
  - `T = 0`: the empty word is the only branch, `N`'s initial configuration is already halted, and
    `E` answers at depth `0`;
  - a branch that halts with output `[false]` or `[]`: halted, not accepting;
  - an `N` with zero work tapes (`N.k = 0`): the replay machine has one tape, the choice tape;
  - the input `z = []`.

## Cited infrastructure (public and proved at the issue commit; all in `C1ExhaustiveImportProbe.lean.txt`)

The probe's names, in seven groups:
- the target and its consumer;
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
- **The population** is 6 files (`audits/evidence/c1-fill-exhaustive/screen-population.txt`): your
  file; `ChoiceReplay`; `ClassNP/Nondeterminism` (`choiceCore`, the main hazard);
  `Build/StepClock`; `Build/CounterLoop`; `ClassNP/NTIME`.
- **The screen** is `audits/evidence/retrofit/copy-text-screen-v3.py`, on the repository paths.
- **The base** is `audits/logs/c1-fill-exhaustive-screen-base.txt`: **278 declarations, 106 pairs,
  36,004 characters** (MEASURED).

```sh
P=audits/evidence/c1-fill-exhaustive
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
- **Bootstrap once** from `briefs/orders/c1-fill-exhaustive.txt` (**77 modules**: the upstream
  closure of your owned file, with the three imports, and of every module downstream of it, without
  the root `TCSlib`).

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < briefs/orders/c1-fill-exhaustive.txt )
  ```

  **The base sorry-warning set has 19 entries in 9 modules**
  (`audits/logs/c1-fill-exhaustive-base-sorries.txt`). Yours is `ClassNP/ExhaustiveReplay`'s one.
  Record the base list by name first, and report any difference.
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
