# Ch3–4 fill campaign — B6 fill, batch F5: the bounded-prefix ruler device (`Build/InputDevice.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor @ANCESTOR@ HEAD` succeeds. If it
  fails, **stop**. That commit contains:
  - **your three targets as gated statements** (the B6 hosts gate,
    `audits/b6-hosts-statements-findings.md`, PASS 0/0/5; resolutions
    `audits/b6-hosts-statements-resolutions.md`);
  - the B6 fill plan (`audits/evidence/b6-fill/B6-fill-plan.md`; F5 is §3 and §6, decision 3);
  - the macro-step lockstep `Turing.Lockstep` (`Build/Contract/Basic`), the R2 seams and the
    phase host (`Build/Seam`), the R1 embeddings (`Build/Embed`), and Z1's virtual-input host
    (`Build/VirtualInput`), the model for your host;
  - **the API PRs** (the user's "Everything" rule, 2026-10-16: every definition your route reads
    has a published lemma): the specification API (PR #112), the core API (PR #116) and the
    brief-inventory API (PR #118, which gives `VirtualTag` and the virtual-input host's tapes for
    this brief);
  - the fill-agent environment addendum `briefs/fill-environment-addendum.md`, and the
    declaration-keyed copy-text screen v3 `audits/evidence/retrofit/copy-text-screen-v3.py`;
  - **this round's inputs** (`audits/evidence/b6-fill-rulerdevice/`): the import overlay, the
    import probe and the screen population. Also the order list
    `briefs/orders/b6-fill-rulerdevice.txt`, the base sorry set, the screen base and the pre-ship
    log (`audits/logs/b6-fill-rulerdevice-*`).
- If Lean cannot start, follow `briefs/fill-environment-addendum.md` exactly.
- **Branch at exactly that commit, not at the campaign tip:**

  ```sh
  git checkout -b fill/b6-rulerdevice @ANCESTOR@
  git rev-parse HEAD        # must print @ANCESTOR@
  ```

  Record that hash as your base in `REPORT.md`. Never rebase, merge or cherry-pick.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-b6-rulerdevice.zip`. It contains:
  - `REPORT.md` and the full modified source;
  - a `git format-patch` series against your base, and a git bundle whose only prerequisite is
    your base;
  - the bootstrap and final sweep logs and the axiom log;
  - both screen outputs, and `SHA256SUMS`.

## Base, line numbers and what lands around you

- **Your base's Lean content is the campaign tip after #118** (`f7546373`). The inputs commit
  adds no Lean change. Lines in this brief are those of that tree. `Build/InputDevice.lean` is
  unchanged since #92 (339 lines). Every probe and measurement below was run there, against the
  olean snapshot of #118's round-3 replay (`oleans-lbapi4`).
- **In flight, merging after your base and invisible to it:** U2-S (`UniversalK`), F3's
  continuation (`WindowClock`), the canonizer's continuation 6 (`CodeSimulator`), G4's
  continuation (`ZoneRebalance`), MIG-12 (`Build/CfgRecord`), MIG-1's batches, and
  the C1 PRs #119, #120 and #121 (new equations in the nondeterministic model, `Build/NDHost`,
  `Build/StepClock`, `Build/StepBlock` and `Build/VirtualInput`, and new statements in two new
  modules; declarations only). Cite nothing they add.

## Parallel batches this round

None in `Build/InputDevice.lean`. Your consumers come later: F6 (`Complexity.space_universal`)
uses the ruler host, and U2-E (`Turing.universalK`) uses it around H2-F.

## What this is

**B6's fifth batch: host H5's bounded-prefix ruler device** (`machine-library-design.md` §14,
the H5 row). It sits off the headline's path: only `space_universal` and U2-E use the ruler.
Three targets, all frozen:
1. **`Turing.exists_rulerTestTM`** (line 216), the restoring suffix-boundary test;
2. **`Turing.exists_rulerDeviceTM`** (line 249), the device's call rows (read and move);
3. **`Turing.exists_rulerHostTM`** (line 313), the ruler host, a positive finite block
   simulation of any native-input machine on a suffix input.

**The published lemmas your route reads** (the core API, PR #116, and the brief-inventory API,
PR #118; ground rule 10):
- `FinTM.VirtualTag_iff` (#118): the virtual-input rows' tag hypotheses; `vhostBuffer_eq` and
  `vhostBank_eq` (#118): Z1's tape indices, where you read its statements;
- `MultiTapeTM.mem_visitedByTapeHead_iff`, `visitedByTapeHead_add_subset`,
  `visitedByTapeHead_step_subset` (moved to `Deterministic`): the host's space ledger;
- `embedEmitCfg_selected_tape`/`_pos`, `embedEmitCfg_unselected`, `embedEmitCfg_eq`,
  `embedEmitCfg_{state,inputPos,output}`: the test on the ruler tape by R1;
- `Cfg.inputSymbol_of_zero`/`_of_end`, `inputSymbolInner`, `Cfg.workTapeSymbols_eq`, and the
  `moveInputPos` lemmas (`moveInputPos_zero`, `_neg_of_ne_left`, `_pos_of_ne_right`,
  `_leftBoundary`, `_rightBoundary`): the heads.

**Read first:**
- the three docstrings, whose proof sketches are binding where this brief does not refine them;
- the module docstring, and `RulerAt`, `rulerHostCfg`, `inputCell_sub_eq_none_iff` and
  `inputCell_of_drop` (proved; the semantic facts the test and the read row need);
- `Build/VirtualInput.lean`: `vhostEmitTM`, `vhostEmitTM_runFrom`,
  `vhostEmitTM_visitedByTapeHead_bank` and `_buffer`. This is how a host carries a boundary tag
  and a source bank. **It is the model, not a citation** of its private steps.
- the fill plan's F5 paragraph.

**Pre-ship check** (maintainer, at the base; `audits/logs/b6-fill-rulerdevice-preship.log`):
- **The import overlay** (`audits/evidence/b6-fill-rulerdevice/InputDeviceOverlay.lean.txt`):
  your file with the two authorized imports added after line 7. It elaborates with the three
  targets' sorry warnings, and nothing else.
- **The import probe** (`B6F5ImportProbe.lean.txt`, 58 `#check`s): every public declaration
  this brief cites resolves from the overlay's import context. 0 errors, 0 warnings. Re-run it
  after your delivery.

## Owned regions and targets (modify these and nothing else)

| # | File:line | Target |
|---|---|---|
| 1 | `Build/InputDevice.lean:216` | `Turing.exists_rulerTestTM` |
| 2 | `Build/InputDevice.lean:249` | `Turing.exists_rulerDeviceTM` |
| 3 | `Build/InputDevice.lean:313` | `Turing.exists_rulerHostTM` |

Your regions:
- **(a) the imports**, as your first edit: exactly
  `import TCSlib.Complexity.TuringMachine.Build.Contract.Basic` and
  `import TCSlib.Complexity.TuringMachine.Build.Seam`, after line 7 (the user's decision 3,
  2026-10-15). No other import.
- **(b) three homes**, for your `private` declarations: the blank lines **202** (before target
  1's docstring), **228** (before target 2's) and **281** (before target 3's, after
  `rulerHostCfg`). `private` only, and no `section`, `open` or `variable` that leaks past one.
- **(c) the three bodies**, the `sorry`s on lines **227**, **270** and **337**.
- **(d) a flagged "Fill appendix (B6-F5)" paragraph at the end of each target's docstring**,
  before its closing ` -/` (lines 215, 248, 312). Each closer ends a text line; put it on its
  own line after your paragraph.

Frozen: the module header, `inputCell`, `NativeAt`, `RulerAt`, `rulerHostCfg`, the proved
lemmas, the three statements, and every other file. The maintainer updates the module's status
text at integration.

### Hosts (binding; the host-first rule, `policy.md` §1, `workflow.md` §2)

- **The boundary test is a leaf** (the fill plan). It is a small finite controller that moves
  the input head left and the ruler head right in lockstep, reads one input cell, and moves both
  back. No catalog row moves the input head together with a work head (`walkTM` and the seek
  family move work heads only; `timed_rewind` moves the input head alone); its docstring says
  so. Its run is one induction over the ruler's `ℓ` cells. `inputCell_sub_eq_none_iff` is the
  verdict's semantic fact.
- **The call rows are seams over the test:** R2 (`seamCompTM`, `seamCompTM₂` for the two
  verdicts, `seamReleaseTM` where an entry is also an exit) or the phase host (`phaseHostTM`,
  `phaseHostTM_run`). Read answers blank on `yes` and the native symbol on `no`
  (`inputCell_of_drop`). A move is the native clamped move to the right, nothing when stationary,
  and suppressed on `yes` / native on `no` to the left. The read verdict and the move step are
  one-step leaves.
- **The host is a `Turing.Lockstep`:**
  - its encoding is `rulerHostCfg` with the tag `b = (c.inputPos.val = 0)`, a function of the
    source configuration;
  - its cost is one host step, or one step plus the boundary test after a left move from a
    cleared tag;
  - the endpoint, the cut and the frames come from `Lockstep.runFrom`, `.cut` and `.locate`.

  The test runs on the ruler tape by R1 (`embedEmitTM` and its frame lemmas, or
  `embedSilentTM`; the test is silent). The host's one-step source transition is its own
  transformer, as Z1's is. The visited-set clauses follow `vhostEmitTM_visitedByTapeHead_bank`'s
  argument through your own lemmas. Never re-walk Z1's privates.
- **Promotion candidates** (list each in `REPORT.md`; notes only): the lockstep-move leaf, and
  any generic "host step plus a pause" lockstep lemma (U2-E and F6 compose the host).

### Phases (for a partial; ground rule 9)

1. Target 1, the boundary test (its leaf and its run).
2. Target 2, the call rows over target 1.
3. Target 3, the ruler host over target 1.

A partial may leave only targets open. Insert a helper only once it is proved.

## Gate guidance (binding)

- **The B6 hosts gate** (`audits/b6-hosts-statements-resolutions.md`) fixed the statements at
  landing, including its finding 2: the host's state map `inj` is a map, not an injection.
- **The adversarial instances the gate checked must stay true of your proofs:**
  - `ℓ = 1`, `z = [true]`, `y = []` at both positions;
  - an empty payload at `p = |z| + 1`;
  - the clamped right move at `i = |y| + 1`;
  - a source that halts on a left move (no pause after a halting transition).

## Cited infrastructure (public and proved at the issue commit; all in `B6F5ImportProbe.lean.txt`)

The probe's 58 names, in eight groups:
- the targets, the device layer and its facts;
- the lockstep and the run calculus;
- seams, the phase host and the release adapter;
- R1 embedding;
- Z1's host, for the pattern only;
- the brief-inventory API (#118);
- the renamings' field equations (#118's round 2);
- the live-step API (#118's round 3): `Action.apply_state`/`_inputPos`/`_workTapePos`/`_output`,
  `MultiTapeTM.step_of_some`, `MultiTapeTM.outputSymbol_of_some`.

**Proved modulo, exactly:** none.

## Ground rules (binding)

1. **File ownership, by region.** Only regions (a)–(d) of `Build/InputDevice.lean`. List every new
   declaration with its role.
2. **Statement freeze** over the targets and every landed declaration: no renames, re-signatures,
   restatements or attribution edits.
3. **No new public declaration.**
4. **Escalation** on anything unprovable as stated: stop on that item, record the obstruction,
   and continue with the rest.
5. **No touching other sorries.** Cite proved material; never re-prove it.
6. **Imports.** Exactly the two in region (a).
7. **One proof per shared argument.** Never write a second seam, phase host, lockstep iteration
   or embedding transport. Never re-walk Z1's or `UniversalStartup`'s virtual-input proofs.
8. **Size.** No cap; file size alone is not a driver. Report the final line count and the public
   and private declaration counts (base: 339 lines).
9. **Continuation budget.** A partial zip states the phase reached, the open declarations (each
   with a literal "Proof sketch"), and each target's axiom walk. A partial is expected and fine;
   an unreported gap is not.
10. **The pinned base, and no unfolding (user, 2026-10-16).**
    - Cite only declarations public at your base, and your file's own privates.
    - **Never unfold a definition of another file.** Read every definition through its published
      lemmas: the equation and field lemmas of the specification API (PR #112), the core API
      (PR #116) and the brief-inventory API (PR #118), and the landed lemmas the probe lists.
    - **The machine model's primitives** (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
      `Cfg.mapState`) are read through their existing lemmas (`runFrom_add`,
      `runFrom_succ_eq_step'`, `step_of_*`, and the renamings' field equations
      `Cfg.mapState_state`/`_inputPos`/`_workTapes`/`_workTapePos`/`_output` and
      `Action.mapState_*`, #118's round 2). **The ruler host simulates an arbitrary machine:**
      read its steps by `MultiTapeTM.step_of_some`/`step_of_halt`, its emission by
      `outputSymbol_of_some`/`_of_halt`, and the applied action by `Action.apply_state`,
      `_inputPos`, `_workTapePos`, `_output` and `Action.apply_workTapes` (#118, round 3).
      Unfold `step` and `Action.apply`
      only for a leaf defined in your own file. `phaseHostTM`'s two-line table is read through
      `phaseHostTM_run`.
    - Your own file's definitions (`RulerAt`, `rulerHostCfg`, `inputCell`) may be unfolded.
    - If a fact you need about another file's definition has no published lemma, **stop on that
      item and escalate** (ground rule 4), naming the lemma you need. Never prove it by unfolding.
    - List every declaration you cite outside your file. If you cite more than the probe's list,
      add them to a copy of the probe and run it.
11. **MIG-1 compatibility.**
    - Cite none of the six R3 canonical rows.
    - Cite no private declaration of another file.
    - Keep your new privates under the `rd_` prefix.

## Duplication governance (binding)

Run the text-level screen **before and after**, **one run at a time, under `nice -n 10`**
(`audits/TEMPLATE.md` failure mode 5; `policy.md`, **Duplication**).
- **The population** is 11 files (`audits/evidence/b6-fill-rulerdevice/screen-population.txt`):
  - your file;
  - `Build/VirtualInput` (Z1, the model and the main hazard);
  - `UniversalStartup` (`universalInput_read`/`_move`, the chapter-1 virtual head over a suffix);
  - `UniversalInterpreter` and `UniversalBlock` (the chapter-1 interpreter's unary input marker:
    the fill plan's Finding B, never reuse it);
  - `Build/Seam`, `Build/Embed`, `Build/Contract/Basic` and `Simulation`;
  - the consumers `UniversalK` and `SpaceComplexity/Hierarchy`.
- **The screen** is `audits/evidence/retrofit/copy-text-screen-v3.py`, on the repository paths.
- **The base** is `audits/logs/b6-fill-rulerdevice-screen-base.txt`: **272 declarations, 138 pairs, 31,217 characters** (MEASURED).

```sh
P=audits/evidence/b6-fill-rulerdevice
nice -n 10 python3 -I audits/evidence/retrofit/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/screen-population.txt) > /tmp/screen-before.txt
# after your changes, again, only when the first run has finished
nice -n 10 python3 -I audits/evidence/retrofit/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/screen-population.txt) > /tmp/screen-after.txt
```

- **No new cross-file pair** with an owned-file declaration on one side. Nothing is
  pre-disclosed.
- **Known hazards:**
  - **Z1's host proofs** (`vhostEmitTM_step`, `_runFrom`, the visited-set lemmas and their
    privates): follow the pattern, never transcribe it. A pair at 90% or more is a copy.
  - `UniversalStartup`'s `universalInput_read`/`_move`;
  - the chapter-1 unary input marker.
- List every new in-file pair with a one-line justification (the read and move rows will look
  alike). At 90% or more it is a copy: factor it. Quote both outputs in `REPORT.md`, which
  carries **"new copies: none"** (or lists each pair).

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake build`**. Use
  `scripts/lean_check_tree.sh` for every check.
- **Bootstrap once** from `briefs/orders/b6-fill-rulerdevice.txt` (**80 modules**: the
  upstream closure of your owned file, with the two imports, and of every module downstream of
  it, without the root `TCSlib`).

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < briefs/orders/b6-fill-rulerdevice.txt )
  ```

  **The base sorry-warning set has 35 entries in 15 modules** (`audits/logs/b6-fill-rulerdevice-base-sorries.txt`).
  Yours are `Build/InputDevice`'s three. Record the base list by name first, and report any
  difference.
- **Final checks:**
  1. `Build/InputDevice`: zero errors, no sorry warning (for a partial, exactly the open
     declarations'), and no other warning in anything you added.
  2. Every other module of the order list: zero errors, and sorry warnings exactly the base's
     minus yours.
  3. Re-run `B6F5ImportProbe.lean.txt`: 0 errors.
- **Axiom prints** for the three targets and every new private: within
  `[propext, Classical.choice, Quot.sound]`, no `sorryAx` for a complete delivery.
- **Lint:** `python3 -I scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine/Build`,
  0 FAIL (base: 0 FAIL, 32 WARN over 37 files). No new line over 100 characters.

## REPORT.md checklist

- [ ] The targets proved (k/3), or the phase reached; the base hash and the ancestor check.
- [ ] The two imports as the first edit, and nothing else outside regions (b)–(d).
- [ ] Every new declaration with its role; each leaf and why no row serves it; the appendices.
- [ ] The constants `C` of each target, and the host's cost function.
- [ ] Promotion candidates and escalations, or "none".
- [ ] Rule 10: the declarations cited outside your file, and the probe re-run. Rule 11: a grep of
      your diff for the six R3 rows and for other files' private names.
- [ ] Duplication: both v3 screens, every new pair justified, "new copies: none".
- [ ] File size; the final sweep tail; the axiom prints; the lint line.

## Known pitfalls at this pin (hard-won)

- **`Cfg.inputPos` is shifted by one:** position `0` is the left blank, and `|z| + 1` the right
  one. `RulerAt` puts the physical head at `ℓ + i`, and `ℓ > 0` keeps every test sweep unclamped
  (`ℓ ≤ inputPos`).
- **`moveInputPos` clamps at both ends.** The virtual right move at `i = |y| + 1` is the physical
  clamp at `|z| + 1`; the left move at `i = 0` never happens physically (suppressed on `yes`).
- **`rulerHostCfg` puts the ruler last** (`Fin.lastCases`). The bank is `i.castSucc`.
- **`phaseHostTM_run`'s `hguard` must hold strictly before `T`.** A row whose entry is its
  verdict has `T = 0`; use the release adapter there.
- `omega` with products as atoms (`ring` first). The linter needs a literal "Proof sketch" before
  every `sorry` (partial only).
