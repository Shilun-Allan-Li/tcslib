# Ch3–4 fill campaign — C1, wave 1, WC: the bounded input window copier (`Turing.exists_inputWindowCopyTM`, `Build/InputWindow.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor @ANCESTOR@ HEAD` succeeds. If it
  fails, **stop**. That commit contains:
  - **your target as a gated statement** (the C1 host-contracts gate,
    `audits/c1-hosts-statements-findings.md`, PASS 0/0/11; resolutions
    `audits/c1-hosts-statements-resolutions.md`);
  - C1's design (`audits/evidence/c1/C1-design.md`; the window copy is §3.4, device (i), and the
    user's decision 5) and C1's fill plan (`audits/evidence/c1/C1-fill-plan.md`; you are wave 1's
    WC);
  - **the API PRs** (the user's "Everything" rule, 2026-10-16: every definition your route reads
    has a published lemma): the specification API (PR #112), the core API (PR #116), the
    brief-inventory API (PR #118: `counterWord_succ`, `Action.apply`'s fields, `step_of_some`) and
    the ND inventory API (PR #119);
  - the fill-agent environment addendum `briefs/fill-environment-addendum.md`, and the
    declaration-keyed copy-text screen v3 `audits/evidence/retrofit/copy-text-screen-v3.py`;
  - **this round's inputs** (`audits/evidence/c1-fill-window/`): the import probe and the screen
    population. Also the order list `briefs/orders/c1-fill-window.txt`, the base sorry set, the
    screen base and the pre-ship log (`audits/logs/c1-fill-window-*`).
- If Lean cannot start, follow `briefs/fill-environment-addendum.md` exactly.
- **Branch at exactly that commit, not at the campaign tip:**

  ```sh
  git checkout -b fill/c1-window @ANCESTOR@
  git rev-parse HEAD        # must print @ANCESTOR@
  ```

  Record that hash as your base in `REPORT.md`. Never rebase, merge or cherry-pick.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-c1-window.zip`. It contains:
  - `REPORT.md` and the full modified source;
  - a `git format-patch` series against your base, and a git bundle whose only prerequisite is
    your base;
  - the bootstrap and final sweep logs and the axiom log;
  - both screen outputs, and `SHA256SUMS`.

## Base, line numbers and what lands around you

- **Your base's Lean content is the campaign tip after #120** (`75edca6f`). The inputs commit
  adds no Lean change. Lines in this brief are those of that tree. `Build/InputWindow.lean` has 84
  lines there, unchanged since #87. Every probe and measurement below was run there, against the
  olean snapshot of #120's replay (`oleans-lndnf`).
- **In flight, merging after your base and invisible to it:** wave 1's other four briefs (W in
  `Build/NDHost`, E in `ClassNP/ExhaustiveReplay`, R in `NDCodeSimulator`, UN in
  `Diagonalization/NTimeHierarchy`); the six #118 briefs; C1-E's statements (#121), and C1's
  follow-up API PR (gate 37's repairs: equations in `Build/StepBlock`, `CodeFormat`, `Encoding` and
  `Build/VirtualInput`; declarations only). Cite nothing they add.

## Parallel batches this round

None in `Build/InputWindow.lean`. Your consumers come later: R (the interpreter core) copies the
universal's input window with your machine, and through it UN.

## What this is

**C1's bounded input window copier** (C1's design §3.4, device (i)): the universal NDTM's time bound
has no `|x|` term, so it copies only the window `x.take t`, and input locality
(`Turing.NDTM.runWith_initCfg_take`) makes that enough. One target, frozen:
1. **`Turing.exists_inputWindowCopyTM`** (line 59): from `entry`, with the input head on the `p`-th
   input symbol and a delimited counter word `w` of value `d` on tape `j`, copy the window
   `y = (z.drop p).take d` onto tape `dst` from its head, within `C·(|y| + 1) + 2|w|` steps and not
   before, with every other tape, head and the output unchanged.

**The published lemmas your route reads** (ground rule 10):
- **the counter loop:** `counterLoopTM_run_done`, `counterLoopTM_run_escape`, `counter_cfg_eq` (the
  Bool layout of `counterLoopCfg`, the counter last), `counterOverhead_le`,
  `counterOverhead_le_of_le`, `counterWord_zero`, `_succ`, `_value`, `_length`, and the orbit
  `counterLoopOrbit` (an `abbrev`; see the pitfalls);
- **the embedding** (R1, `Build/Embed`): `embedEmitTM_runFrom`, `embedEmitTM_frame`, and
  `embedEmitCfg_selected_tape`, `_selected_pos`, `_unselected`, `_eq` (or the silent flavor's
  `embedSilentTM_runFrom`, `_frame` and `embedSilentCfg_*`);
- **the model:** `MultiTapeTM.step_of_some`, `step_of_halt`, `runFrom_zero`,
  `runFrom_succ_eq_step'`, `runFrom_add`; `Action.apply_state`, `_inputPos`, `_workTapePos`,
  `_output`, `Action.apply_workTapes` (#118, round 3);
- **the heads:** `Cfg.inputSymbol_of_zero`, `_of_end`, `Cfg.workTapeSymbols_eq`, and
  `moveInputPos_zero`, `_pos_of_ne_right`, `_rightBoundary`;
- **the buffer:** `FinTM.bufferTape` and its lemmas.

**Read first:**
- the target's docstring, whose proof sketch is binding where this brief does not refine it;
- `Build/InputCall.lean`'s input seek (`exists_inputSeekTM` and its private `inputSeekStep`,
  `inputSeekStep_run`, `inputSeekMachine`): a counter loop over a one-step input-moving body, the
  counter on the last tape. **It is the model, not a citation** of its privates;
- `Turing.counterLoopTM_run_done` and `_run_escape`: their round hypotheses and their endpoints.

**Pre-ship check** (maintainer, at the base, against `oleans-lndnf`;
`audits/logs/c1-fill-window-preship.log`):
- **No import is added.** Your file elaborates at the base with exactly your target's sorry
  warning.
- **The import probe** (`C1WindowImportProbe.lean.txt`, 49 `#check`s): every public
  declaration this brief cites resolves from your file's import context. 0 errors, 0 warnings.
  Re-run it after your delivery.

## Owned regions and targets (modify these and nothing else)

| # | File:line | Target |
|---|---|---|
| 1 | `Build/InputWindow.lean:59` | `Turing.exists_inputWindowCopyTM` |

Your regions:
- **(a) one home**, for your `private` declarations: the blank line **37**, after
  `namespace Turing` and before the target's docstring. `private` only, and no `section`, `open` or
  `variable` that leaks past one.
- **(b) the body**, the `sorry` on line **82**.
- **(c) a flagged "Fill appendix (C1-WC)" paragraph at the end of the target's docstring**, before
  its closing ` -/` (line 58). The closer ends a text line; put it on its own line after your
  paragraph.

Frozen: the module header and docstring, the target's statement, and every other file. The
maintainer updates the module's status text at integration.

### Route (binding; the host-first rule, `policy.md` §1, `workflow.md` §2)

- **The host is the counter loop**, `Turing.counterLoopTM`, over a two-tape **body**: tape `0` is
  `dst`, tape `1` is the counter (the loop's last tape). Your machine is that loop **embedded by R1**
  along `ι : Fin 2 ↪ Fin k` with `0 ↦ dst` and `1 ↦ j` (`hjd`). The embedding freezes every other
  tape and head, and the output if the body is silent: those are the statement's frame clauses.
  Never write a second counter loop, embedding or seam.
- **The body is a one-step leaf, and it is yours.** In its running state: on an input symbol
  `some a`, write `a` on tape `0`, move tape `0` and the input head right, and return to the anchor;
  at the input's right end (`none`), go to the escape state. Define it in your home; you may unfold
  its step (a leaf of your own file) through `MultiTapeTM.step_of_some` and `Action.apply`'s fields.
- **The rounds:** round `r` starts with the input head at native position `p + r + 1` and `dst`'s
  head `r` cells right of its start. Every round takes one step. The loop runs `|y|` rounds and is
  exhausted when `|y| = d`; when the input ends first it escapes in round `|y| + 1 ≤ d`.
- **The ledger** is the docstring's: on exhaustion, `counterOverhead_le` once (`4d + 2|w| + 2`); on
  an early end, `counterOverhead_le_of_le` at `r = |y| + 1` (`4r + 2|w|`). The final counter word is
  the loop's: all `true` on exhaustion, `counterWord w (|y| + 1)` on escape (`counterWord_length`
  gives the width).
- **The two exits.** The statement has one exit, `done`. Map both of the loop's exits to it (a
  state renaming, `Cfg.mapState`, through its field equations), or compose a one-step join. Either
  way, keep the first-arrival clause: no earlier visit to `done`.
- **Promotion candidate** (list it in `REPORT.md`; a note only): a generic "counter loop over a
  one-step body" contract, if your proof factors one. `exists_inputSeekTM` is its other instance.

## Gate guidance (binding)

- **The C1 host-contracts gate** fixed the statement (`audits/c1-hosts-statements-findings.md`).
  It has no `|z|` term, and it allows the window to stop early at the input's end.
- **Edge cases that must stay true of your proof:**
  - `d = 0`: an empty window, `|y| = 0`; the counter underflows at once;
  - `p = |z|`: the head is on the right end marker, so the window is empty and the loop escapes in
    round `1 ≤ d` (when `d ≥ 1`);
  - `|y| < d`, the input ending inside the window;
  - a counter word with leading zero bits (its width `|w|` exceeds its value's length).

## Cited infrastructure (public and proved at the issue commit; all in `C1WindowImportProbe.lean.txt`)

The probe's names: the target; the counter loop, its layout and its ledger; R1's run and frame
lemmas; the model's step, run and action lemmas; the head lemmas; `FinTM.bufferTape` and its lemmas.

**Proved modulo, exactly:** none.

## Ground rules (binding)

1. **File ownership, by region.** Only regions (a)–(c) of `Build/InputWindow.lean`. List every new
   declaration with its role.
2. **Statement freeze** over the target and every landed declaration.
3. **No new public declaration.**
4. **Escalation** on anything unprovable as stated: stop on that item, record the obstruction, and
   report.
5. **No touching other sorries.** Cite proved material; never re-prove it.
6. **Imports.** None added.
7. **One proof per shared argument.** Never write a second counter loop, embedding or seam, and
   never re-walk `InputCall`'s seek privates.
8. **Size.** No cap; file size alone is not a driver. Report the final line count and the public and
   private declaration counts (base: 84 lines).
9. **Continuation budget.** A partial zip states the open declarations (each with a literal "Proof
   sketch") and the target's axiom walk.
10. **The pinned base, and no unfolding (user, 2026-10-16).**
    - Cite only declarations public at your base, and your file's own privates.
    - **Never unfold a definition of another file.** Read every definition through its published
      lemmas (the four API PRs and the landed lemmas the probe lists). `counterLoopCfg` is read
      through `counter_cfg_eq`; the embedding's configurations through `embedEmitCfg_*`.
    - **The machine model's primitives** (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
      `Cfg.mapState`) are read through their lemmas. Unfold `step` and `Action.apply` only for your
      own body leaf.
    - If a fact you need about another file's definition has no published lemma, **stop on that
      item and escalate** (ground rule 4), naming the lemma you need.
    - List every declaration you cite outside your file. If you cite more than the probe's list,
      add them to a copy of the probe and run it.
11. **MIG-1 compatibility.**
    - Cite none of the six R3 canonical rows.
    - Cite no private declaration of another file.
    - Keep your new privates under the `iw_` prefix.

## Duplication governance (binding)

Run the text-level screen **before and after**, **one run at a time, under `nice -n 10`**
(`audits/TEMPLATE.md` failure mode 5; `policy.md`, **Duplication**).
- **The population** is 5 files (`audits/evidence/c1-fill-window/screen-population.txt`): your file;
  `Build/CounterLoop`; `Build/InputCall` (the seek, the model and the main hazard); `Build/Scan`
  (`inputCopyTM`, the whole-input copier, the second hazard); `Build/Embed`.
- **The screen** is `audits/evidence/retrofit/copy-text-screen-v3.py`, on the repository paths.
- **The base** is `audits/logs/c1-fill-window-screen-base.txt`: **125 declarations, 43 pairs, 11,684
  characters** (MEASURED).

```sh
P=audits/evidence/c1-fill-window
nice -n 10 python3 -I audits/evidence/retrofit/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/screen-population.txt) > /tmp/screen-before.txt
# after your changes, again, only when the first run has finished
nice -n 10 python3 -I audits/evidence/retrofit/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/screen-population.txt) > /tmp/screen-after.txt
```

- **No new cross-file pair** with an owned-file declaration on one side. Nothing is pre-disclosed.
- **Known hazards:** `inputSeekStep_run` and the seek's ledger (`InputCall`), and
  `inputCopyTM_run_ofCfg` (`Scan`). Follow their pattern, never transcribe it. A pair at 90% or more
  is a copy.
- List every new in-file pair with a one-line justification. Quote both outputs in `REPORT.md`,
  which carries **"new copies: none"** (or lists each pair).

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake build`**. Use
  `scripts/lean_check_tree.sh` for every check.
- **Bootstrap once** from `briefs/orders/c1-fill-window.txt` (**80 modules**: the upstream closure
  of your owned file and of every module downstream of it, without the root `TCSlib`).

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < briefs/orders/c1-fill-window.txt )
  ```

  **The base sorry-warning set has 35 entries in 15 modules**
  (`audits/logs/c1-fill-window-base-sorries.txt`). Yours is `Build/InputWindow`'s one. Record the
  base list by name first, and report any difference.
- **Final checks:**
  1. `Build/InputWindow`: zero errors, no sorry warning (for a partial, exactly the open
     declarations'), and no other warning in anything you added.
  2. Every other module of the order list: zero errors, and sorry warnings exactly the base's minus
     yours.
  3. Re-run `C1WindowImportProbe.lean.txt`: 0 errors.
- **Axiom prints** for the target and every new private: within
  `[propext, Classical.choice, Quot.sound]`, no `sorryAx` for a complete delivery.
- **Lint:** `python3 -I scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine/Build`,
  0 FAIL (base: 0 FAIL, 30 WARN over 37 files). No new line over 100 characters.

## REPORT.md checklist

- [ ] The target proved, or the obstruction; the base hash and the ancestor check.
- [ ] Nothing outside regions (a)–(c).
- [ ] Every new declaration with its role; the body leaf and why no row serves it; the appendix.
- [ ] The constant `C`, and the ledger in both cases.
- [ ] Promotion candidates and escalations, or "none".
- [ ] Rule 10: the declarations cited outside your file, and the probe re-run. Rule 11: a grep of
      your diff for the six R3 rows and for other files' private names.
- [ ] Duplication: both v3 screens, every new pair justified, "new copies: none".
- [ ] File size; the final sweep tail; the axiom prints; the lint line.

## Known pitfalls at this pin (hard-won)

- **`Cfg.inputPos` is shifted by one:** position `0` is the left blank and `|z| + 1` the right one.
  The `p`-th input symbol is at native position `p + 1`, and `z.drop p` starts there.
- **`moveInputPos` clamps at both ends**, so a right move at `|z| + 1` stays there.
- **`counterLoopOrbit` is an `abbrev`:** `rw` with the orbit's round lemmas may not fire on it, while
  `exact` and `simp only` do (#118's note N3).
- **`counterLoopTM_run_done`'s round hypothesis** needs each round's exact time `τ > 0` and its
  first return to the anchor; a one-step round has `τ = 1`.
- `omega` with products as atoms (`ring` first). The linter needs a literal "Proof sketch" before
  every `sorry` (partial only).
