# Ch3–4 fill campaign — C1, wave 1, R: the interpreter core for nondeterministic codes (`Turing.exists_ndInterpreterCore`, `NDCodeSimulator.lean`)

> **DRAFT (maintainer, 2026-10-17). Not issued.** Measured at #120's head `6d18902f` (the tip once
> #119 and #120 merge). It issues with wave 1 after #119 and #120 merge (C1's fill plan; user,
> 2026-10-17). ⟨…⟩ are filled then.

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor @ANCESTOR@ HEAD` succeeds. If it
  fails, **stop**. That commit contains:
  - **your target as a gated statement** (the C1 host-contracts gate,
    `audits/c1-hosts-statements-findings.md`, PASS 0/0/11; resolutions
    `audits/c1-hosts-statements-resolutions.md`; the prefix clause is the repaired one of its minor
    M4);
  - C1's design (`audits/evidence/c1/C1-design.md`; `R` is §3.6, the replay route is the user's
    decision 3) and C1's fill plan (`audits/evidence/c1/C1-fill-plan.md`; you are wave 1's R);
  - **the hosts:** H1's hosted counter loop over H2's step block (`Build/StepBlockLoop`, PR #94),
    Z1 (`Build/VirtualInput`), the prefix canonizer (`UniversalStartup`), the install call
    (`Build/Loop`), the replay machine (`ChoiceReplay`);
  - **the API PRs** (the user's "Everything" rule, 2026-10-16: every definition your route reads has
    a published lemma): the specification API (PR #112), the core API (PR #116), the brief-inventory
    API (PR #118) and **the ND inventory API (PR #119, which gives this brief the hosted loop's
    definitions — `StepBlock.Rep_iff`, `exit_true`, `exit_false`, `summaryTape_eq`, `tableTape_eq`,
    `outputSummary_nil`, `summaryCells_eq` — Z1's `vhostCfg` fields, the replay machine's fields,
    `CodeNDTM.toFinNDTM`'s fields and `Cfg.ofWords`'s fields)**;
  - the fill-agent environment addendum `briefs/fill-environment-addendum.md`, and the
    declaration-keyed copy-text screen v3 `audits/evidence/retrofit/copy-text-screen-v3.py`;
  - **this round's inputs** (`audits/evidence/c1-fill-core/`): the import overlay, the import probe
    and the screen population. Also the order list `briefs/orders/c1-fill-core.txt`, the base sorry
    set, the screen base and the pre-ship log (`audits/logs/c1-fill-core-*`).
- If Lean cannot start, follow `briefs/fill-environment-addendum.md` exactly.
- **Branch at exactly that commit, not at the campaign tip:**

  ```sh
  git checkout -b fill/c1-core @ANCESTOR@
  git rev-parse HEAD        # must print @ANCESTOR@
  ```

  Record that hash as your base in `REPORT.md`. Never rebase, merge or cherry-pick.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-c1-core.zip`. It contains:
  - `REPORT.md` and the full modified source;
  - a `git format-patch` series against your base, and a git bundle whose only prerequisite is
    your base;
  - the bootstrap and final sweep logs and the axiom log;
  - both screen outputs, and `SHA256SUMS`.

## Base, line numbers and what lands around you

- **Your base's Lean content is the campaign tip after #120** (⟨BASE-LEAN⟩). The inputs commit adds
  no Lean change. Lines in this brief are those of that tree, **before** your import edit.
  `NDCodeSimulator.lean` has 147 lines there, unchanged since #94 (H1's harvest). Every probe and
  measurement below was run there, against the olean snapshot of #120's replay (`oleans-lndnf`).
- **In flight, merging after your base and invisible to it:** wave 1's other four briefs (W in
  `Build/NDHost`, WC in `Build/InputWindow`, E in `ClassNP/ExhaustiveReplay`, UN in
  `Diagonalization/NTimeHierarchy`); the six #118 briefs, among them the canonizer's continuation 6
  in `CodeSimulator`, which your file imports; C1-E's statements (#121). Cite nothing they add.
- **Your file's other stub,** the replay canonizer `exists_replayCanonizer` (line 91), is wave 2's
  and stays sorried: you cite its statement.

## Parallel batches this round

None in `NDCodeSimulator.lean`. WC (`Build/InputWindow`) fills the window copier you cite. Your
consumers come later: UN (the universal NDTM, through the guess-then-run assembly's interpreter
interface) and the diagonalizer's middle rung (C1-E).

## What this is

**C1's interpreter core `R`** (C1's design §3.6): one deterministic machine, uniform over codes,
that runs the coded NDTM's branch along a guessed stream at linear overhead. One target, frozen:
1. **`Turing.exists_ndInterpreterCore`** (line 128): for every effective scheme `c`, a machine `R`
   with a stream tape `j` and verdicts `accept ≠ reject`, such that for every code `α` there is `C`:
   from `entry` on `z = ⟨⟨bits t, α⟩, x⟩` with a stream `s` (`t ≤ |s|`) on tape `j`, `R` reaches
   `accept` iff the decoded machine's branch on `x` along `s.take t` halted with output `[true]`,
   at a time `T ≤ C·(t + 1)` with no earlier verdict, and `T ≤ C·(t' + |x| + |bits t| + 1)` whenever
   the branch along `s.take t'` already halted (the prefix clause).

**Proved modulo, exactly:** `Turing.exists_replayCanonizer` (your file, wave 2) and
`Turing.exists_inputWindowCopyTM` (WC, this wave). Cite their statements; never their bodies.

**The published lemmas your route reads** (ground rule 10):
- **the header** (`UniversalStartup`): `prefixCanonTM`, `prefixCanonTM_eq`, `prefixCanon_complete`
  (a halted composite at a suffix-independent time, with its output and its input head at
  `2|u| + 3`, the first cell of the suffix); `FinTM.pairExtractTM_fst`, `_snd`
  (`5·(n + 1)` steps); `FinTM.timed_rewind`;
- **the installation** (`Build/Loop`): `FinTM.exists_installCallTM`, stated through `Cfg.ofWords`
  seams (`Cfg.ofWords_state`, `_inputPos`, `_workTapes`, `_workTapePos`, `_output`, #119);
- **the window:** `Turing.exists_inputWindowCopyTM`, with `counterValue_bits` (the counter `bits t`
  has value `t`);
- **the loop** (`Build/StepBlockLoop`): `StepBlock.hostedLoopTM_run` (the early-escape bound is
  the prefix clause), `StepBlock.hostedLoop_read` (the verdict), with `StepBlock.Rep_iff`,
  `exit_true`, `exit_false`, `summaryTape_eq`, `tableTape_eq`, `outputSummary_nil`,
  `summaryCells_eq` (#119), `vhostCfg`'s fields and `vhostBank_eq`, `counter_cfg_eq`;
- **the code and its replay:** `serializeK_eq`, `tableBitsK`'s lemmas,
  `CodeNDTM.serialize_eq_tableBitsK` (proved, your file), `CodeNDTM.toFinNDTM_k`, `_State`, `_tm`,
  `NDTM.replayTM_runFrom` (the replay lemma), `replayTM_q₀`, `_tr`, `withChoiceTape`'s fields,
  `NDTM.runWith_initCfg_take` (input locality), `NDTM.initCfg_eq` with `Cfg.init`'s fields;
- **composition:** `seamCompTM_run_ofCfg`, `seamReleaseTM_firstReturn`, `phaseHostTM_run`,
  `embedSilentTM_runFrom` and `embedSilentCfg_*` (capturing a sub-machine's output on a tape);
- **the model:** `MultiTapeTM.step_of_some`, `step_of_halt`, the run algebra, `Action.apply`'s
  fields, `Cfg.mapState`'s fields, `FinTM.computesInTime_iff`.

**Read first:**
- the target's docstring, whose proof sketch is binding where this brief does not refine it;
- `StepBlock.hostedLoopTM_run` and `hostedLoop_read`, all their hypotheses and both exits;
- `UniversalStartup`'s `prefixCanon_complete` and the chapter-1 startup it serves
  (`universalCanonTM`, `universalCaptureTM`): **the model, not a citation** of their privates.

**Pre-ship check** (maintainer, at the base, against `oleans-lndnf`;
`audits/logs/c1-fill-core-preship.log`):
- **The import overlay** (`audits/evidence/c1-fill-core/NDCodeSimulatorOverlay.lean.txt`): your file
  with the two authorized imports added after line 8. It elaborates with your file's two sorry
  warnings and nothing else.
- **The import probe** (`C1CoreImportProbe.lean.txt`, 77 `#check`s): every public
  declaration this brief cites resolves from the overlay's import context. 0 errors, 0 warnings.
  Re-run it after your delivery.

## Owned regions and targets (modify these and nothing else)

| # | File:line | Target |
|---|---|---|
| 1 | `NDCodeSimulator.lean:128` | `Turing.exists_ndInterpreterCore` |

Your regions (line numbers before your import edit; add 2 after it):
- **(a) the imports**, as your first edit: exactly
  `import TCSlib.Complexity.TuringMachine.Build.InputWindow` and
  `import TCSlib.Complexity.TuringMachine.UniversalStartup`, after line 8. No other import.
- **(b) one home**, for your `private` declarations: the blank line **95**, between the replay
  canonizer's `sorry` and your target's docstring. `private` only, and no `section`, `open` or
  `variable` that leaks past one.
- **(c) the body**, the `sorry` on line **145**.
- **(d) a flagged "Fill appendix (C1-R)" paragraph at the end of the target's docstring**, before
  its closing ` -/` (line 127). The closer ends a text line; put it on its own line after your
  paragraph.

Frozen: the module header and docstring, the bridge, **the replay canonizer's statement and its
`sorry`**, your target's statement, and every other file. The maintainer updates the module's status
text at integration.

### Route (binding; the host-first rule, `policy.md` §1, `workflow.md` §2)

The docstring's route, refined. Never write a second host, seam, embedding, loop or clock.
- **Startup, the header.** `z = pairEncode u x` with `u = pairEncode (bits t) α`.
  - **Two prefix passes.** Run `prefixCanonTM (pairExtractTM true false)`: it outputs `bits t` and
    halts with the input head at `2|u| + 3` (`prefixCanon_complete` with `pairExtractTM_fst`).
    Rewind the native input head (`FinTM.timed_rewind`). Run
    `prefixCanonTM (pairExtractTM false true)`: it outputs `α` and leaves the head at the start of
    `x`.
  - Each pass runs silently, its output captured on a dedicated tape by R1 (`embedSilentTM`). Each
    costs `O(|u| + 1)`, which is a per-code constant plus `O(|bits t|)`.
  - **Do not run the canonizer through `prefixCanonTM`:** its time bound is a function of `|u|`,
    which grows with `bits t`, so it would not stay a per-code constant.
- **Startup, the table.** Install `serializeK (c.decode α).tm.replayTM` by
  `FinTM.exists_installCallTM` with the replay canonizer's machine on the captured `α`
  (`exists_replayCanonizer`). Its time depends on `|α|` alone, a per-code constant. Then install the
  unary initial state.
- **The window.** Keep a second copy of `bits t` first (the window copy consumes its counter). Copy
  `x.take t` with `exists_inputWindowCopyTM`: the input head is at the start of `x`, the native
  position its contract wants. Rewind the window.
- **The loop.** `StepBlock.hostedLoopTM_run` at three work tapes, the stream as the mirrored choice
  tape, hosted by Z1 on the window, over the counter `bits t` (`counterValue_bits`), from the replay
  machine's represented start. Establish `Rep` through `Rep_iff` and Z1's configuration through
  `vhostCfg`'s fields. **The verdict** reads H2's output summary at the live exits
  (`hostedLoop_read`).
- **The semantics.**
  - The replay lemma identifies the simulated run with the coded branch along `s.take t` on the
    window.
  - Input locality (`runWith_initCfg_take`, at `m = t`) identifies that branch on `x.take t` with
    the branch on `x`.
  - `CodeNDTM.toFinNDTM_tm` reads the decoded machine.
- **The ledger.**
  - Startup: a per-code constant plus `O(|bits t|)`.
  - Window: `O(min(t, |x|) + |bits t|)`.
  - Loop: the escape bound `t'·50·(|table| + 1) + 4t' + 2|bits t|` when the branch halts by `t'`,
    or the full count otherwise.

  That gives both clauses with one per-code `C`, using `|bits t| ≤ t + 1`.
- **Promotion candidates** (list each in `REPORT.md`; notes only): the two-pass header split, which
  UN's setup and B5a's H1 continuation also need; a silent "run a `FinTM` on the native input and
  capture its output" phase, if your proof factors one.

## Gate guidance (binding)

- **The C1 host-contracts gate** fixed the statement, including the repaired prefix clause (its
  minor M4; `audits/c1-hosts-statements-resolutions.md`). **The design's ledger** (C1's design §3.6)
  is the intended one; a coarser bound that loses the prefix clause is a statement failure, not an
  option.
- **Edge cases that must stay true of your proof:**
  - `t = 0`: `bits 0 = []`, the window is empty, the loop runs no round, and `R` rejects, since an
    initial configuration is live (the gate's minor M4: no branch has halted at `t' = 0`);
  - `|x| < t`: the window copy stops early; locality still applies, since `x.take t = x`;
  - `|s| > t`: only `s.take t` matters;
  - a code `α` whose decoding is any machine: `c.decode` is total.

## Cited infrastructure (public and proved at the issue commit; all in `C1CoreImportProbe.lean.txt`)

The probe's names, in seven groups:
- the window copier's statement (the target, the replay canonizer and the bridge are in your file);
- the header;
- the installation;
- the loop;
- the code and the replay;
- composition;
- the model.

## Ground rules (binding)

1. **File ownership, by region.** Only regions (a)–(d) of `NDCodeSimulator.lean`. List every new
   declaration with its role.
2. **Statement freeze** over the target and every landed declaration.
3. **No new public declaration.**
4. **Escalation** on anything unprovable as stated: stop on that item, record the obstruction, and
   continue with the rest.
5. **No touching other sorries** (the replay canonizer's stays). Cite proved material; never
   re-prove it.
6. **Imports.** Exactly the two in region (a).
7. **One proof per shared argument.** Never write a second loop, step block, Z1, seam, phase host,
   embedding or prefix parser. Never re-walk `UniversalStartup`'s or `CodeSimulator`'s privates.
8. **Size.** No cap; file size alone is not a driver. Report the final line count and the public and
   private declaration counts (base: 147 lines).
9. **Continuation budget.** A partial zip states the phase reached, the open declarations (each with
   a literal "Proof sketch") and the target's axiom walk. A partial is expected and fine; an
   unreported gap is not.
10. **The pinned base, and no unfolding (user, 2026-10-16).**
    - Cite only declarations public at your base, and your file's own privates.
    - **Never unfold a definition of another file.** Read every definition through its published
      lemmas (the four API PRs and the landed lemmas the probe lists). In particular read
      `prefixCanonTM` only through `prefixCanonTM_eq` and `prefixCanon_complete`; the buffered
      composite's configurations (`bufferedSecondCfg`) have no field equations and are not on this
      route.
    - **The machine model's primitives** (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
      `Cfg.mapState`, `NDTM.stepWith`, `NDTM.runWith`) are read through their lemmas. The coded
      machine is arbitrary: read it only through the replay lemma and the replay machine's fields.
      Unfold `step` and `Action.apply` only for a leaf defined in your own file.
    - If a fact you need about another file's definition has no published lemma, **stop on that
      item and escalate** (ground rule 4), naming the lemma you need.
    - List every declaration you cite outside your file. If you cite more than the probe's list,
      add them to a copy of the probe and run it.
11. **MIG-1 compatibility.**
    - Cite none of the six R3 canonical rows.
    - Cite no private declaration of another file.
    - Keep your new privates under the `ic_` prefix.

### Phases (for a partial; ground rule 9)

1. The startup: the two prefix passes, the table, the initial state.
2. The window.
3. The loop and the verdict.
4. The semantics and the ledger, both clauses.

## Duplication governance (binding)

Run the text-level screen **before and after**, **one run at a time, under `nice -n 10`**
(`audits/TEMPLATE.md` failure mode 5; `policy.md`, **Duplication**).
- **The population** is 7 files (`audits/evidence/c1-fill-core/screen-population.txt`): your file;
  `CodeSimulator` (H1's region, the main hazard); `Build/StepBlockLoop`; `UniversalStartup`;
  `UniversalK` (U2's startup, a sibling); `ChoiceReplay`; `Build/InputWindow`.
- **The screen** is `audits/evidence/retrofit/copy-text-screen-v3.py`, on the repository paths.
- **The base** is `audits/logs/c1-fill-core-screen-base.txt`: **171 declarations, 19 pairs, 5,115
  characters** (MEASURED).

```sh
P=audits/evidence/c1-fill-core
nice -n 10 python3 -I audits/evidence/retrofit/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/screen-population.txt) > /tmp/screen-before.txt
# after your changes, again, only when the first run has finished
nice -n 10 python3 -I audits/evidence/retrofit/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/screen-population.txt) > /tmp/screen-after.txt
```

- **No new cross-file pair** with an owned-file declaration on one side. Nothing is pre-disclosed.
- **Known hazards:** the chapter-1 startup (`universalCaptureTM` and its run); U2's startup
  (`UniversalK`); `CodeSimulator`'s H1 assembly. Follow their pattern, never transcribe it. A pair
  at
  90% or more is a copy.
- List every new in-file pair with a one-line justification. Quote both outputs in `REPORT.md`,
  which carries **"new copies: none"** (or lists each pair).

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake build`**. Use
  `scripts/lean_check_tree.sh` for every check.
- **Bootstrap once** from `briefs/orders/c1-fill-core.txt` (**80 modules**: the upstream closure of
  your owned file, with the two imports, and of every module downstream of it, without the root
  `TCSlib`).

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < briefs/orders/c1-fill-core.txt )
  ```

  **The base sorry-warning set has 35 entries in 15 modules**
  (`audits/logs/c1-fill-core-base-sorries.txt`). Yours is `NDCodeSimulator`'s
  `exists_ndInterpreterCore`; its other entry, the replay canonizer, stays. Record the base list by
  name first, and report any difference.
- **Final checks:**
  1. `NDCodeSimulator`: zero errors, exactly the replay canonizer's sorry warning (for a partial,
     plus the open declarations'), and no other warning in anything you added.
  2. Every other module of the order list: zero errors, and sorry warnings exactly the base's minus
     yours.
  3. Re-run `C1CoreImportProbe.lean.txt`: 0 errors.
- **Axiom prints** for the target and every new private: within
  `[propext, Classical.choice, Quot.sound]` plus the `sorryAx` of the two cited stubs (the replay
  canonizer, the window copier), and nothing else.
- **Lint:** `python3 -I scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine`, 0 FAIL
  (base: 0 FAIL, 63 WARN over 79 files). No new line over 100 characters.

## REPORT.md checklist

- [ ] The target proved (or the phase reached), modulo exactly the two cited stubs; the base hash
  and
      the ancestor check.
- [ ] The two imports as the first edit, and nothing else outside regions (b)–(d).
- [ ] Every new declaration with its role; the appendix.
- [ ] The per-code constant `C`, and the ledger of both clauses.
- [ ] Promotion candidates and escalations, or "none".
- [ ] Rule 10: the declarations cited outside your file, and the probe re-run. Rule 11: a grep of
      your diff for the six R3 rows and for other files' private names.
- [ ] Duplication: both v3 screens, every new pair justified, "new copies: none".
- [ ] File size; the final sweep tail; the axiom prints; the lint line.

## Known pitfalls at this pin (hard-won)

- **`Cfg.inputPos` is shifted by one.** In `pairEncode u x` the suffix `x` starts at index
  `2|u| + 2`,
  native position `2|u| + 3`, which is where `prefixCanon_complete` leaves the head.
- **`pairEncode` doubles its first component:** `u` takes `2|u|` cells, then the separator
  `[false, true]`.
- **The replay machine puts the choice tape last**, and the step block mirrors the source's tapes
  first: the stream is the replay machine's last tape.
- **`counterLoopOrbit` is an `abbrev`:** `rw` may not fire on it, while `exact` and `simp only` do
  (#118's note N3).
- **`StepBlock.exit k live` is a sigma type:** rewrite it with `exit_true` and `exit_false`.
- `omega` with products as atoms (`ring` first). The linter needs a literal "Proof sketch" before
  every `sorry` (partial only).
