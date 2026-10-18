# Ch3–4 fill campaign — B6, F5 continuation 1: the ruler device's call rows and host (`Turing.exists_rulerDeviceTM`, `Turing.exists_rulerHostTM`, `Build/InputDevice.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor @ANCESTOR@ HEAD` succeeds. If it
  fails, **stop**. That commit contains:
  - **the first round, landed (PR #133):** `Turing.exists_rulerTestTM` proved (the restoring
    boundary test, exact time `2ℓ + 2`, `C = 2`), with its private kit (`rd_test`, `rd_cfg`,
    `rd_trace`, `rd_run` and their lemmas), the table built from `Turing.tapeAction` through the
    `Build/Catalog` import (the user's ruling, 2026-10-18); its gate
    (`campaign/gates/51-b6-f5-rulerdevice-fill/`) and the maintainer's review
    (`campaign/fills/b6/reviews/rulerdevice-1/REVIEW.md`);
  - the B6 hosts gate's statements and rulings (`campaign/gates/13-b6-hosts-statements/`), and
    the first brief (`campaign/fills/b6/briefs/b6-fill-rulerdevice.md`), whose hosts, route and
    pitfalls this brief repeats for the two open targets;
  - **the API PRs** (the user's "Everything" rule, 2026-10-16): #112, #116, #118 (with its rounds
    2 and 3: the renamings' field equations and the live-step API);
  - the fill-agent environment addendum `campaign/standards/fill-environment-addendum.md`
    (**v2**: Part 1, the resources and the cache, applies on every host; it also says that the
    cache command's internal `lake build --no-build proofwidgets:release` is expected), and the
    declaration-keyed copy-text screen v3 `scripts/copy-text-screen-v3.py`;
  - **this round's inputs** (`campaign/fills/b6/inputs/b6-fill-rulerdevice-cont1/`): the import
    probe and the screen population. Also the order list
    `campaign/fills/b6/orders/b6-fill-rulerdevice-cont1.txt`, the base sorry set, the screen base
    and the pre-ship log (`campaign/fills/b6/logs/b6-fill-rulerdevice-cont1-*`).
- **Before anything else, run Part 1 of `campaign/standards/fill-environment-addendum.md`**: the
  preflight, with its stop rule (E-RES). If Lean cannot start, follow Part 2 exactly.
- **Branch at exactly that commit, not at the campaign tip:**

  ```sh
  git checkout -b fill/b6-rulerdevice-cont1 @ANCESTOR@
  git rev-parse HEAD        # must print @ANCESTOR@
  ```

  Record that hash as your base in `REPORT.md`. Never rebase, merge or cherry-pick.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-b6-rulerdevice-cont1.zip`. It
  contains:
  - `REPORT.md` and the full modified source;
  - a `git format-patch` series against your base, and a git bundle whose only prerequisite is
    your base;
  - the bootstrap and final sweep logs and the axiom log;
  - both screen outputs, and `SHA256SUMS`.
- **Checkpoint zips (binding this round).** The first round's first session proved all three
  targets and lost them with its workspace before any zip was made. After each phase below,
  commit and write `fill-b6-rulerdevice-cont1-cp<N>.zip` with the same contents as of that commit
  (the final sweep may be your module's check only). Deliver the latest if the session ends early.

## Base, line numbers and what lands around you

- **Your base's Lean content is the campaign tip after #133** (⟨BASE-LEAN⟩). The inputs commit
  adds no Lean change. Lines in this brief are those of that tree. `Build/InputDevice.lean` is
  #133's (526 lines; 15 public, 9 private). Every probe and measurement below was run there,
  against the olean snapshot ⟨SNAPSHOT⟩.
- **In flight, merging after your base and invisible to it:** ⟨IN-FLIGHT⟩. Cite nothing they add.

## Parallel batches this round

None in `Build/InputDevice.lean`. Your consumers come later: F6 (`Complexity.space_universal`)
uses the ruler host, and U2-E (`Turing.universalK`) uses it around H2-F.

## What this is

**B6's fifth batch, continued: host H5's bounded-prefix ruler device** (`machine-library-design.md`
§14, the H5 row). Target 1 is proved. Two targets remain, both frozen:
2. **`Turing.exists_rulerDeviceTM`** (line 436), the device's call rows (read and move);
3. **`Turing.exists_rulerHostTM`** (line 500), the ruler host, a positive finite block simulation
   of any native-input machine on a suffix input.

**Usable now** (the review): the boundary test's hypotheses are exactly `RulerAt ℓ 0 d i`'s last
conjunct, and `ℓ ≤ inputPos` follows from `inputPos = ℓ + i`, so target 2 can call target 1 or
`rd_run` directly. The first round's figures for the continuation, unchecked: the device
`2ℓ + 5 ≤ 4(ℓ + 1)` for `ℓ ≥ 1`; the host `1 + (2ℓ + 2) = 2ℓ + 3 ≤ 3(ℓ + 1)`.

**The published lemmas your route reads** (ground rule 10):
- `Turing.tapeAction`, `Turing.step_of_tapeAction_move`, `Turing.inputMoveAction` and
  `Turing.step_of_inputMoveAction` (`Build/Catalog`): **the one-step leaves' actions**, as target
  1's table uses them;
- `FinTM.VirtualTag_iff`, `vhostBuffer_eq` and `vhostBank_eq` (#118): Z1's tape indices, where
  you read its statements;
- `MultiTapeTM.mem_visitedByTapeHead_iff`, `visitedByTapeHead_add_subset`,
  `visitedByTapeHead_step_subset`: the host's space ledger;
- `embedEmitCfg_selected_tape`/`_pos`, `embedEmitCfg_unselected`, `embedEmitCfg_eq`,
  `embedEmitCfg_{state,inputPos,output}`: the test on the ruler tape by R1;
- `Cfg.inputSymbol_of_zero`/`_of_end`, `inputSymbolInner`, `Cfg.workTapeSymbols_eq`, and the
  `moveInputPos` lemmas: the heads.

**Read first:**
- the two open targets' docstrings, whose proof sketches are binding where this brief does not
  refine them;
- target 1's proof and kit (lines 207–414): the model for your leaves;
- the module docstring, `RulerAt`, `rulerHostCfg`, `inputCell_sub_eq_none_iff` and
  `inputCell_of_drop`;
- `Build/VirtualInput.lean`: `vhostEmitTM`, `vhostEmitTM_runFrom`,
  `vhostEmitTM_visitedByTapeHead_bank` and `_buffer`, how a host carries a boundary tag and a
  source bank. **It is the model, not a citation** of its private steps.

**Pre-ship check** (maintainer, at the base; `campaign/fills/b6/logs/b6-fill-rulerdevice-cont1-preship.log`):
- **Your file** elaborates with exactly the two open targets' sorry warnings (lines 436, 500).
- **The import probe** (`B6F5C1ImportProbe.lean.txt`, ⟨PROBE-N⟩ `#check`s: the first round's 111,
  and `tapeAction`, `step_of_tapeAction_move`, `inputMoveAction`, `step_of_inputMoveAction`): every
  public declaration this brief cites resolves. 0 errors, 0 warnings. Re-run it after your delivery.

## Owned regions and targets (modify these and nothing else)

| # | File:line | Target |
|---|---|---|
| 2 | `Build/InputDevice.lean:436` | `Turing.exists_rulerDeviceTM` |
| 3 | `Build/InputDevice.lean:500` | `Turing.exists_rulerHostTM` |

Your regions:
- **(a) two homes**, for your `private` declarations: the blank lines **415** (before target 2's
  docstring) and **468** (before target 3's, after `rulerHostCfg`). `private` only, under the
  `rd_` prefix, and no `section`, `open` or `variable` that leaks past one.
- **(b) the two bodies**, the `sorry`s on lines **457** and **524**.
- **(c) for a partial only, a paragraph headed `**Implementation status.**` at the end of an open
  target's docstring**, before its closing ` -/` (lines 435, 499). Each closer ends a text line;
  put it on its own line after your paragraph. It is public-facing library text: what is proved
  and what is open, in mathematical terms, with no campaign labels (brief, gate, finding or
  escalation names), no dates and no session narrative. The same holds for the docstrings of your
  new declarations; provenance goes in `REPORT.md`.

Frozen: the module header and imports, `inputCell`, `NativeAt`, `RulerAt`, `rulerHostCfg`, the
proved lemmas and target 1 with its kit, the two statements and their docstrings before (c), and
every other file. The maintainer updates the module's status text at integration.

### Hosts (binding; the host-first rule, `policy.md` §1, `workflow.md` §2)

- **The call rows are seams over the test:** R2 (`seamCompTM`, `seamCompTM₂` for the two
  verdicts, `seamReleaseTM` where an entry is also an exit) or the phase host (`phaseHostTM`,
  `phaseHostTM_run`). Read answers blank on `yes` and the native symbol on `no`
  (`inputCell_of_drop`). A move is the native clamped move to the right, nothing when stationary,
  and suppressed on `yes` / native on `no` to the left. **The read verdict and the move step are
  one-step leaves built from `Turing.tapeAction` or `Turing.inputMoveAction`**, as target 1's
  table is (the user's ruling): no private action or step lemma for a shape those serve.
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
- **Promotion candidates** (list each in `REPORT.md`; notes only): any generic "host step plus a
  pause" lockstep lemma (U2-E and F6 compose the host).

### Phases (for a partial; ground rule 9; a checkpoint zip after each)

2. Target 2, the call rows over target 1.
3. Target 3, the ruler host over target 1.

A partial may leave only targets open. Insert a helper only once it is proved.

## Gate guidance (binding)

- **The B6 hosts gate** fixed the statements, including its finding 2: the host's state map `inj`
  is a map, not an injection.
- **The adversarial instances the gate checked must stay true of your proofs:**
  - `ℓ = 1`, `z = [true]`, `y = []` at both positions;
  - an empty payload at `p = |z| + 1`;
  - the clamped right move at `i = |y| + 1`;
  - a source that halts on a left move (no pause after a halting transition).

## Cited infrastructure (public and proved at the issue commit; all in `B6F5C1ImportProbe.lean.txt`)

The probe's names: the first round's 111 (the targets, the device layer and its facts; the
lockstep and the run calculus; seams, the phase host and the release adapter; R1; Z1's host, for
the pattern only; #118's three rounds), and the catalog's action lemmas above.

**Proved modulo, exactly:** none.

## Ground rules (binding)

1. **File ownership, by region.** Only regions (a)–(c) of `Build/InputDevice.lean`. List every new
   declaration with its role.
2. **Statement freeze** over the targets and every landed declaration: no renames, re-signatures,
   restatements or attribution edits.
3. **No new public declaration.**
4. **Escalation, item by item:** on anything unprovable as stated, stop **on that item only**,
   record the obstruction mathematically, and continue with every item that does not depend on it.
5. **No touching other sorries.** Cite proved material; never re-prove it.
6. **Imports.** Unchanged (five, `Build/Catalog` among them). No other import.
7. **One proof per shared argument.** Never write a second seam, phase host, lockstep iteration,
   embedding transport, or one-step action lemma that `tapeAction`/`inputMoveAction` serve. Never
   re-walk Z1's or `UniversalStartup`'s virtual-input proofs, or target 1's trace: cite `rd_run`.
8. **Size.** No cap; file size alone is not a driver. Report the final line count and the public
   and private declaration counts (base: 526 lines; 15 public, 9 private).
9. **Continuation budget.** A partial zip states the phase reached, the open declarations (each
   with a literal "Proof sketch"), and each target's axiom walk.
10. **The pinned base, and no unfolding (user, 2026-10-16).**
    - Cite only declarations public at your base, and your file's own privates.
    - **Never unfold a definition of another file**, and no definitional closure either (a `rfl`,
      `exact`, `show`, `decide` or `simp` step that closes only because another file's definition
      reduces). Read every definition through its published lemmas.
    - **The machine model's primitives** (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
      `Cfg.mapState`) are read through their existing lemmas. **The ruler host simulates an
      arbitrary machine:** read its steps by `MultiTapeTM.step_of_some`/`step_of_halt`, its
      emission by `outputSymbol_of_some`/`_of_halt`, and the applied action by `Action.apply_*`
      and `Action.apply_workTapes`. Unfold `step` and `Action.apply` only for a leaf defined in
      your own file; `phaseHostTM`'s table is read through `phaseHostTM_run`.
    - Your own file's definitions (`RulerAt`, `rulerHostCfg`, `inputCell`, the `rd_` kit) may be
      unfolded.
    - If a fact you need about another file's definition has no published lemma, **stop on that
      item and escalate** (ground rule 4), naming the lemma you need.
    - **Self-check:** a seal test (a scratch copy of your module with `attribute [local
      irreducible]` on every other-file definition your proofs mention, `tapeAction` included,
      which must still elaborate; the first round's seal list is in its review) and an inspection
      of every `rw`/`simp`/`simpa`/`unfold` argument in your diff.
    - List every declaration you cite outside your file. If you cite more than the probe's list,
      add them to a copy of the probe and run it.
11. **MIG-1 compatibility.** Cite none of the six R3 canonical rows; cite no private declaration
    of another file (`Build/Catalog`'s included); keep your new privates under the `rd_` prefix.

## Duplication governance (binding)

Run the text-level screen **before and after**, **one run at a time, under `nice -n 10`**
(`campaign/standards/TEMPLATE.md` failure mode 5; `policy.md`, **Duplication**).
- **The population** is 12 files
  (`campaign/fills/b6/inputs/b6-fill-rulerdevice-cont1/screen-population.txt`): the first
  round's 11 (your file; `Build/VirtualInput`, Z1, the model and the main hazard;
  `UniversalStartup`; `UniversalInterpreter` and `UniversalBlock`; `Build/Seam`, `Build/Embed`,
  `Build/Contract/Basic`, `Simulation`; the consumers `UniversalK` and
  `SpaceComplexity/Hierarchy`), plus `Build/Catalog` (the action lemmas).
- **The screen** is `scripts/copy-text-screen-v3.py`, on the repository paths.
- **The base** is `campaign/fills/b6/logs/b6-fill-rulerdevice-cont1-screen-base.txt`:
  **⟨SCREEN-BASE⟩** (MEASURED).
- **Already accepted, in-file:** `rd_trace_step` against `rd_read_nat` (81%, the shared
  `bufferTape_nat` lookup).
- **No new cross-file pair** with an owned-file declaration on one side. **Known hazards:** Z1's
  host proofs (`vhostEmitTM_step`, `_runFrom`, the visited-set lemmas and their privates);
  `UniversalStartup`'s `universalInput_read`/`_move`; the chapter-1 unary input marker; target 1's
  trace (cite it). A pair at 90% or more is a copy. List every new in-file pair with a one-line
  justification (the read and move rows will look alike; factor them by a parameter where their
  proofs coincide). Quote both outputs in `REPORT.md`, which carries **"new copies: none"** (or
  lists each pair).

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake build`**. Use
  `scripts/lean_check_tree.sh` for every check.
- **Bootstrap once** from `campaign/fills/b6/orders/b6-fill-rulerdevice-cont1.txt` (**⟨ORDER-N⟩
  modules**: the upstream closure of your owned file and of every module downstream of it,
  without the root `TCSlib`). **The base sorry-warning set has ⟨SORRY-SET⟩**
  (`campaign/fills/b6/logs/b6-fill-rulerdevice-cont1-base-sorries.txt`). Yours are
  `Build/InputDevice`'s two. Record the base list by name first, and report any difference.
- **Final checks:**
  1. `Build/InputDevice`: zero errors, no sorry warning (for a partial, exactly the open
     declarations'), and no other warning in anything you added.
  2. Every other module of the order list: zero errors, and sorry warnings exactly the base's
     minus yours.
  3. Re-run `B6F5C1ImportProbe.lean.txt`: 0 errors.
- **Axiom prints** for the three targets and every new private: within
  `[propext, Classical.choice, Quot.sound]`, no `sorryAx` for a complete delivery.
- **Lint:** `python3 -I scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine/Build`,
  0 FAIL (base: ⟨LINT-BUILD⟩). No new line over 100 characters.

## REPORT.md checklist

- [ ] The preflight's numbers (addendum v2, Part 1).
- [ ] The targets proved, or the phase reached; the base hash and the ancestor check; the
      checkpoint zips written.
- [ ] Every new declaration with its role; each leaf, the action lemma it uses, and why no row
      serves it; the status paragraphs, if a partial.
- [ ] The constants `C` of each target, and the host's cost function.
- [ ] Promotion candidates and escalations (each stated mathematically), or "none".
- [ ] Rule 10: the declarations cited outside your file, the probe re-run, the seal test and the
      inspection. Rule 11: a grep of your diff for the six R3 rows and for other files' private
      names.
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
- **`step_of_tapeAction_move`** needs the state's table entry as an equation (`ht`), and a
  one-tape bank's index rewrites by `Subsingleton.elim i 0` (target 1's `rd_cfg_step`).
- `omega` with products as atoms (`ring` first). The linter needs a literal "Proof sketch" before
  every `sorry` (partial only).
