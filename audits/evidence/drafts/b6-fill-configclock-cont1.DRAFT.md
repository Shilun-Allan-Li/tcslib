# Ch3–4 fill campaign — B6 fill, batch F3, continuation 1: the configuration-count runner (`Turing.exists_configWindowRunnerTM`, `SpaceComplexity/WindowClock.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor @ANCESTOR@ HEAD` succeeds. If it
  fails, **stop**. That commit contains:
  - **F3's partial, landed (PR #111):** the five private arithmetic lemmas `cw_true_value`,
    `cw_round_cost`, `cw_budget`, `cw_time_bound`, `cw_head_bound` and a partial appendix in your
    file;
  - **the specification API (PR #112)**, the user's ruling on its escalation E1. It gives
    `Turing.recordAt_iff`, `Turing.recordLength_eq` and the public `Turing.record_pos_lt`, the
    layout facts (`fieldsTape_*`, `fieldOffset_zero`, `joinFields_*`), and every row contract's
    field equations;
  - **the core API (PR #116) and the brief-inventory API (PR #118)**, the rest of the user's
    "Everything" rule (2026-10-16). For this brief, #118 gives `Turing.RecSym.digitEmb_apply` (a
    lifted digit is `RecSym.digit`), `Turing.binDigits_eq` and `Turing.posWidth_eq`;
  - **B6's first two batches, both landed:**
    - F1 (PR #103): the step clock `exists_stepClockTMVia`, proved;
    - F2 (PR #99): the windowed loop and the windowed runner `exists_windowRunnerTM`, both proved
      and sorry-free since F1 landed.
  - record-table row 18 (`exists_recordInitTM`, PR #95), MIG-1 stage S (#98), and everything
    merged up to the G2 fill (#108);
  - the B6 fill plan (`audits/evidence/b6-fill/B6-fill-plan.md`; F3 is §3 and §6, Route A);
  - the fill-agent environment addendum `briefs/fill-environment-addendum.md`, and the
    declaration-keyed copy-text screen v3 `audits/evidence/retrofit/copy-text-screen-v3.py`;
  - **this round's inputs** (`audits/evidence/b6-fill-configclock/`): the pre-ship overlay and its
    generator, the import probe, the consumer probe, and the screen population. Also the order
    list `briefs/orders/b6-fill-configclock.txt`, the base sorry set, the screen base and the
    pre-ship log (`audits/logs/b6-fill-configclock-*`).
- If Lean cannot start, follow `briefs/fill-environment-addendum.md` exactly.
- **Branch at exactly that commit, not at the campaign tip:**

  ```sh
  git checkout -b fill/b6-configclock-cont1 @ANCESTOR@
  git rev-parse HEAD        # must print @ANCESTOR@
  ```

  Record that hash as your base in `REPORT.md`. Never rebase, merge or cherry-pick.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-b6-configclock-cont1.zip`. It contains:
  - `REPORT.md` and the full modified source;
  - a `git format-patch` series against your base, and a git bundle whose only prerequisite is
    your base;
  - the bootstrap and final sweep logs and the axiom log;
  - both screen outputs, and `SHA256SUMS`.

## Base, line numbers and what lands around you

- **Your base's Lean content is the campaign tip after #118** (⟨BASE-LEAN⟩). The inputs commit
  adds no Lean change. Lines in this brief are those of that tree. `WindowClock.lean` is the
  partial's (312 lines; 4 public, 5 private). Every probe and measurement below was run there,
  against the olean snapshot of #118's replays (`oleans-lbapi2`).
- **F2's runner is proved and sorry-free** in your base. Its proof is in
  `Build/WindowRun.lean`, but **cite only its statement** (ground rule 10).
- **In flight, merging after your base and invisible to it:**
  - the canonizer's continuation 6 (`CodeSimulator`), G4's continuation (`ZoneRebalance`), U2-S
    (`UniversalK`) and F5 (`Build/InputDevice`);
  - MIG-12 (`Build/CfgRecord`) if issued: it keeps every public statement there, so your citations
    of `CfgRecord`'s public facts are unaffected;
  - MIG-1's batches.

  Cite nothing these add.

## Parallel batches this round

None in `WindowClock.lean`. F4 (`U₀`) comes from U2's `k = 1` corollaries (H2-F and U2-S are in
flight). F5 (`InputDevice`) may be briefed in parallel. F6 (`space_universal`) and H (the
headline region of `Hierarchy`) follow.

## What this is

**B6's third batch, continued, on the critical path to `Complexity.space_hierarchy`**
(F1 → F2 → F3 → H). The first delivery (`fill-b6-configclock.zip`; review
`audits/evidence/b6-fill-configclock/delivery-review.md`) proved the clock arithmetic and stopped
on escalation E1. **E1 is ruled (user, 2026-10-16): not by unfolding but by published lemmas.**
The specification API (PR #112, in your base) gives the field cells from a `RecordAt` hypothesis
(`recordAt_iff`), the record-length formula (`recordLength_eq`) and `n + 1 < 2 ^ posWidth n`
(`record_pos_lt`, now public). Ground rule 10 forbids unfolding any other file's definition.
- One target: **`Turing.exists_configWindowRunnerTM`**, the windowed runner that builds its own
  clock, large enough for every configuration in the window plus the extra halt-test round.
- Its statement passed the B6 hosts gate (`audits/b6-hosts-statements-findings.md`, PASS 0/0/5) and
  landed in PR #92. **It is frozen.**
- **The route is Route A**, the gate's ruling once the shared clock is filled (fill plan §5,
  decision 1): build an all-`true` clock word, run F2's runner on it, clear it.
- **Route B** (the counter loop with the window round as its body) is the fallback only if Route
  A meets an obstruction you record as an escalation.

**Read first:**
- the target's docstring, whose Route A sketch is binding where this brief does not refine it;
- `exists_windowRunnerTM`'s statement and docstring (`Build/WindowRun.lean`, line 1062);
- `Turing.windowRun_stop_unique`, `Turing.FinTM.configBound_le_two_pow`, `Turing.recordLength`
  and `Turing.joinFields_length`;
- the fill plan's F3 paragraphs.

**Pre-ship check** (maintainer, at the base, against `oleans-lf3p`;
`audits/logs/b6-fill-configclock-preship.log`):
- **The overlay** (`audits/evidence/b6-fill-configclock/WindowClockOverlay.lean.txt`, generator
  `tools/mkoverlay.py` with `tools/home.lean.txt`): `WindowClock.lean` with the recommended
  clock-writer stub at the home. **0 errors, 0 non-sorry warnings, 2 sorry warnings** (the stub
  and the target). The generator pins the target byte for byte and undoes its edit.
- **The import probe** (`F3ImportProbe.lean.txt`, 60 `#check`s): every public declaration this
  brief cites resolves from `WindowClock`'s import context. 0 errors, 0 warnings. **Re-run it
  after your delivery.**
- **The consumer probe** (`F3ConsumerProbe.lean.txt`): row 18's endpoint, after the radius word
  is cleared in `clearTM_run_ofCfg`'s endpoint shape, leaves every tape other than `0` blank,
  which is this contract's precondition. Row 18, the clear and this runner instantiate together
  at the diagonalizer's data. 0 errors, 0 warnings. With
  `audits/evidence/w1-fill-recordtable-cont5/RT5ConsumerProbe.lean.txt` (the record part), this
  shows that H can call your contract on row 18's output.

## Owned regions and targets (modify these and nothing else)

| # | File:line | Target | Route |
|---|---|---|---|
| 1 | `SpaceComplexity/WindowClock.lean:280` | `Turing.exists_configWindowRunnerTM` (frozen statement) | Route A |

Your regions:
- **(a) the home**, lines 143–224: after the section header `/-! ### The runner -/` (142) and up
  to the target's docstring (225). This holds the partial's five `cw_` lemmas and your new
  `private` declarations. You may **adjust the `cw_` lemmas' statements or remove them**: they
  are private, and none is used yet. Report each change. `private` only, and no `section`,
  `open` or `variable` that leaks past it.
- **(b) the target's body**, the `sorry` on line 310.
- **(c) the target docstring's "Fill appendix (B6-F3, partial)" paragraph** (lines 269–278).
  Rewrite it as "Fill appendix (B6-F3)" for the final state; it stays before the closing ` -/`
  (line 279).

Everything else is frozen: the module header, the three proved bridges (lines 57–140), the
target's docstring before the appendix (225–267), the statement (280–309), and every other file.
The maintainer updates the module's status text at integration; report any text that reads
wrong.

### The recommended clock writer (Recommended shape; you may restate it)

`tools/home.lean.txt` is one stub, `exists_clockWriterTM {Γ} (e : Γ) (m c : ℕ)`:
- **input:** a layout `fs` of `m` nonempty fields at the head of tape `0` (`RecordAt d 0 fs`), and
  tape `1` blank;
- **result:** `c` passes over the field cells written as one contiguous word of `e`s of width
  `c · (fs.map List.length).sum` at the head of tape `1`, both heads returned, silently, within
  `C · ((joinFields fs).length + 1)`.

It is generic, two-tape, and modelled on `Turing.exists_fieldsCopyTM`. You embed it into the
runner's bank by R1 on tapes `{0, clock}`. **Insert it only once it is proved** (restated or as
stated), so that a partial never adds an open admission. If you restate it, keep it private and
generic, and give the statement in `REPORT.md`. **The stub may be used as recommended:** its proof
reads the field cells through `recordAt_iff` and the layout facts, and drives
`copyMapTM_run_ofCfg` and `skipTM_run_ofCfg` on them.

**Why a one-cell move.** No public row stops on a word's delimiter: `skipTM` and `seekEndTM`
stop one cell past it. The copies must join into one delimited word, which F2's runner requires
(`FinTM.bufferTape` of the digit word, blank on both sides). So after skipping the clock tape
past each written field, move its head one cell left onto the delimiter, where the next copy
continues the word. That move is the one leaf you may write: a one-step controller like the
catalog's `tapeAction i 0 none .neg _`. The separators of `fs` are skipped, not written, so a
pass writes `(fs.map List.length).sum` cells.

### Hosts (binding; the host-first rule, `policy.md` §1, `workflow.md` §2)

- **Compose by the public combinators:** R2 seams (`seamCompTM`, `seamCompTM_run_ofCfg`,
  `seamCompTM_firstReturn_ofCfg`, `seamReleaseTM`), the phase host (`phaseHostTM`,
  `phaseHostTM_run`), and R1 embedding (`embedEmitTM`, `embedEmitTM_runFrom`, `embedEmitTM_frame`,
  `embedEmitCfg_eq`). Never write a second seam, phase host, loop or embedding transport.
- **The rows:**
  - the mapped copy `copyMapTM_run_ofCfg` (proved since #108; `extract := fun _ => ()`,
    `merge := fun _ _ => e`);
  - `skipTM_run_ofCfg`, `skipBackTM_run_ofCfg` and `clearTM_run_ofCfg`;
  - F2's runner `exists_windowRunnerTM`;
  - state transport `MultiTapeTM.runFrom_mapState_of_agreeOn`.
- **Leaves you may write:** the one-cell move above, and a one-step exit dispatch if a phase
  host needs one. Nothing else.
- **Promotion candidates** (list each with its contract in `REPORT.md`; notes only): the clock
  writer.

### The route (binding where it names a row)

1. **The clock.**
   - The clock tape is the runner's last tape (`Fin.last (K + 1)` in F2's statement). Your
     runner's `K + 1` tapes are F2's `K' + 2`.
   - Write `w := List.replicate W true`, as `RecSym.digitEmb`-digits (`RecSym.digitEmb_apply`),
     with the clock writer at
     `e := RecSym.digitEmb M.State T true`, `m := k + 3` (`cfgRecord`'s field count), and a constant
     `c` depending only on `M` and `upd`. Then `W = c · (fs.map List.length).sum`.
   - The clock tape is blank in your precondition, so the word is delimited, as F2's runner needs.
2. **The run.** Seam to F2's runner at its entry. Its precondition:
   - the record on tape `0`: yours, unchanged by the writer;
   - the digit word at the clock head;
   - every other tape blank: yours.
3. **The exits.**
   - **`exhausted`:** dispatch to `exit .exhausted`. The target makes no tape claim there.
   - **`halted`, `left`:** F2's endpoint leaves a digit word `w'` of width `|w|` on the clock
     interval (`wordPatch`). `clearTM_run_ofCfg` blanks it, since it is delimited: the clock tape
     was blank outside it. That returns the clock head, and you dispatch to `exit out`. The
     endpoint is then the target's: the stopping record on tape `0` (F2's endpoint clause), and
     every other tape, every head and the input position as at the start.
4. **The ledger.**
   - **Time:** the writer is `O(L + 1)`. F2's runner takes at most
     `5 · (2^W - 1) + 2W + 3`, since `Nat.ofDigits 2` of `W` trues is `2^W - 1`. The clear and the
     dispatches are `O(W)`. With `W ≤ c · L`, the total is at most `C · 2^(C · (L + 1))`.
   - **Heads and space:** F2's envelope `C · (L + |w| + 1)` with `|w| ≤ cL` gives the target's
     `C · (L + 1)`, and its space clause the target's.
   - **Certification** (the target's `∀ N ≤ configBound + 1` clause): F2 certifies `out` when
     `C_R · N · (L + |x| + 1) ≤ 2^W - 1`. Use these facts:
     - `configBound ≤ 2^(|Q| + posWidth |x| + 3k(2s + 1))`
       (`Turing.FinTM.configBound_le_two_pow`);
     - `|x| + 2 ≤ 2^(posWidth |x|)`;
     - `recordLength k n s = k(2s + 1) + posWidth n + k + 4`;
     - `(joinFields fs).length = (fs.map List.length).sum + fs.length - 1`
       (`Turing.joinFields_length`, for nonempty `fs`). `cfgRecord` has `k + 3` fields (state,
       position, `k` tape windows, tag), so its field total is `k(2s + 1) + posWidth |x| + 2`,
       linear in `L`.

     Choose `c` so that `2^W - 1` exceeds `C_R · (2^(|Q| + posWidth + 3k(2s+1)) + 1) · 2^(L + 1)`
     for every `s`. The plan's estimate is `c` about `|Q| + log C_R + 6` (ESTIMATE; prove your
     own).
   - **The determined clause** (`out ≠ exhausted → ∃ N …`): F2's, with the clock cleared.
     `Turing.windowRun_stop_unique` moves the certification from F2's `N` to the statement's.

### Phases (for a partial; ground rule 9)

0. Done in the first delivery: the clock arithmetic (`cw_*`). Discharge `cw_budget`'s `hL`
   by `recordLength_eq` and `hn` by `record_pos_lt`.
1. **The clock writer** proved (inserted at the home).
2. **The target** proved: the composition, the endpoint, the ledger.

A partial may leave only the target open, with the clock writer proved or not inserted.

## Gate guidance (binding)

- **The B6 hosts gate's minors** bind as fixed at landing (`audits/b6-hosts-statements-resolutions.md`).
  In particular, the bound `N ≤ configBound + 1` contains the extra halt-test round (RD-3's
  check 4).
- **Route B** is not a parallel route. Use it only on a recorded Route A obstruction.

## Cited infrastructure (public and proved at the issue commit; all in `F3ImportProbe.lean.txt`)

The probe's 60 names, in six groups:
- the target, its runner and the window semantics;
- the configuration count and the record layout;
- the framed rows of the clock writer and the cleanup;
- composition;
- Route B, for the fallback only;
- the record facts and the brief-inventory API (`recordAt_iff`, `recordLength_eq`,
  `record_pos_lt`; #118's `RecSym.digitEmb_apply`, `binDigits_eq`, `posWidth_eq`).

**Proved modulo, exactly:** none. A complete delivery has no `sorryAx` in your target.

## Ground rules (binding)

1. **File ownership, by region.** Only regions (a)–(c) of `SpaceComplexity/WindowClock.lean`. List
   every new declaration with its role.
2. **Statement freeze** over the target and every landed declaration: no renames,
   re-signatures, restatements or attribution edits.
3. **No new public declaration.** Your machines are private; list them as promotion candidates.
4. **Escalation** on anything unprovable as stated, including a cited row that does not compose
   as the route says: stop on that item, record the obstruction, and continue with the rest.
5. **No touching other sorries.** Cite proved material; never re-prove it.
6. **Imports.** Unchanged (`Build/WindowRun`, `SpaceComplexity/ConfigGraph`). No TCSlib import
   may be added. Every row the route names is in the closure; the Contract layer is not, and is
   not needed. A Mathlib import only if a needed lemma requires it; flag it.
7. **One proof per shared argument.** Never write a second seam, phase host, clock, R1
   reconstruction or record bookkeeping; never re-walk a row's trace or F2's proof.
8. **Size.** No cap; file size alone is not a driver. Report the final line count and the public and
   private declaration counts (base: 312 lines; 4 public, 5 private).
9. **Continuation budget.** A partial zip states the phase reached, the open declarations (each with
   a literal "Proof sketch"), and the target's axiom walk. A partial is expected and fine; an
   unreported gap is not.
10. **The pinned base, and no unfolding (user, 2026-10-16).**
    - Cite only declarations public at your base, and your file's own privates.
    - **Never unfold a definition of another file.** Read every definition through its published
      lemmas: the specification API (PR #112), the core API (PR #116), the brief-inventory API
      (PR #118), and the landed lemmas the probe lists.
    - **The machine model's primitives** (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
      `Cfg.mapState`) are read through their existing lemmas. Unfold `step` and `Action.apply`
      only for a leaf defined in your own file. `phaseHostTM`'s table is read through
      `phaseHostTM_run`.
    - Your own file's definitions may be unfolded.
    - If a fact you need about another file's definition has no published lemma, **stop on that
      item and escalate** (ground rule 4), naming the lemma you need.
    - List every declaration you cite outside your file in `REPORT.md`. If you cite more than the
      probe's list, add them to a copy of the probe and run it.
11. **MIG-1 compatibility.**
    - Cite none of the six R3 canonical rows (`copyTM_run`, `transferTM_run`, `clearTM_run`,
      `compareTM_run`, `incrementTM_run_succ`, `incrementTM_run_overflow`); use their framed
      `_ofCfg` forms.
    - Cite no private declaration of `Simulation`, `Composition`, `Build/Wrappers`, `Encoding`,
      `Build/Loop` or `Build/Catalog`.
    - Keep your new privates under the `cw_` prefix.

## Duplication governance (binding)

Run the text-level screen **before and after**, **one run at a time, under `nice -n 10`**
(`audits/TEMPLATE.md` failure mode 5; `policy.md`, **Duplication**).
- **The population** is F2's 21 files, unchanged
  (`audits/evidence/b6-fill-configclock/screen-population.txt`): your file, the files the route
  cites, the known overlaps and the consumers.
- **The screen** is the declaration-keyed `audits/evidence/retrofit/copy-text-screen-v3.py`, on
  the repository paths. v3 labels the two basename collisions (`Build/Seam` with
  `Build/Contract/Seam`, `Build/Embed` with `Build/Contract/Embed`) by full path, so F2's
  flattening is no longer needed.
- **The base**, at the issue tree, is `audits/logs/b6-fill-configclock-screen-base.txt`:
  **1,041 declarations, 510 pairs, 147,693 characters** (MEASURED). The stub's body is under the screen's 60-character floor, so the
  overlay adds nothing.

```sh
P=audits/evidence/b6-fill-configclock
nice -n 10 python3 -I audits/evidence/retrofit/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/screen-population.txt) > /tmp/screen-before.txt
# after your changes, again, only when the first run has finished
nice -n 10 python3 -I audits/evidence/retrofit/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/screen-population.txt) > /tmp/screen-after.txt
```

- **No new cross-file pair** with an owned-file declaration on one side. Nothing is
  pre-disclosed.
- **Known hazards:**
  - `exists_fieldsCopyTM`'s route (`rt_copyMachine`: copy, skip, recurse, skip back). Your writer
    follows the same shape: cite the rows, do not transcribe `RecordTable`'s private proof;
  - F2's runner and loop proofs (`wr_*`, `wl_*`): cite the statement;
  - the phase-host compositions elsewhere: follow the pattern, do not transcribe it;
  - the R1 reconstruction family: cite `embedEmitCfg_eq`;
  - `CounterLoop`'s counter loop: not your host (Route B only).
- List every new in-file pair with a one-line justification. At 90% or more it is a copy: factor
  it. Quote both outputs in `REPORT.md`, which carries **"new copies: none"** (or lists each
  pair).

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake build`**. Use
  `scripts/lean_check_tree.sh` for every check.
- **Bootstrap once** from `briefs/orders/b6-fill-configclock.txt` (**176 modules**: the upstream
  closure of your owned file and of every module downstream of it, without the root `TCSlib`; one
  module is downstream of it, the `SpaceComplexity` facade, since H's import of `WindowClock` into
  `Hierarchy` comes with H):

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < briefs/orders/b6-fill-configclock.txt )
  ```

  **The base sorry-warning set has 28 entries in 11 modules**
  (`audits/logs/b6-fill-configclock-base-sorries.txt`, one per declaration). Yours is
  `SpaceComplexity/WindowClock`'s one, the target. Record the base list by name first, and report
  any difference.
- **Final checks:**
  1. `SpaceComplexity/WindowClock`: zero errors, no sorry warning (for a partial, exactly the open
     declarations'), and no other warning in anything you added.
  2. Every other module of the order list: zero errors, and sorry warnings exactly the base's minus
     yours (**27** for a complete delivery).
  3. Re-run `F3ImportProbe.lean.txt` and `F3ConsumerProbe.lean.txt`: 0 errors.
- **Axiom prints** (in a scratch copy of your module with `#print axioms` appended) for the target
  and every new private: within `[propext, Classical.choice, Quot.sound]`, no `sorryAx` for a
  complete delivery.
- **Lint:** `python3 -I scripts/campaign_style_lint.py TCSlib/Complexity/SpaceComplexity`, 0 FAIL
  (base: 0 FAIL, 81 WARN over 107 files). No new line over 100 characters.

## Out-of-scope sorries you will see (leave every one untouched)

Everything in the base sorry set except your target:
- MIG-1 stage S's sorried specs (`Simulation`, `Composition`, `Build/Wrappers`, `Build/Loop`,
  `Encoding`, `ClassP/TimeConstructible`, `Build/Primitives`);
- `Build/RecordTable`'s four rows;
- `SpaceComplexity/Hierarchy`'s four (H and F6);
- `SpaceComplexity/Savitch`'s two.

If a proof seems to *need* one of these beyond a named citation, that is an escalation, not a
license.

## REPORT.md checklist

- [ ] 1/1, or the phase reached; the base hash and the ancestor check.
- [ ] Every new declaration with its role; the clock writer as recommended or restated; the
      one-cell leaf; the flagged appendix.
- [ ] The constant `c` and the ledger, step by step.
- [ ] Promotion candidates and escalations, or "none".
- [ ] Rule 10: the declarations cited outside your file, and the probe re-run. Rule 11: a grep of
      your diff for the six R3 rows.
- [ ] Duplication: both v3 screens, every new pair justified, "new copies: none".
- [ ] File size; the final sweep tail; the axiom prints; the lint line. The diff touches only your
      owned regions.

## Known pitfalls at this pin (hard-won)

- From F2:
  - `WindowExit` derives only `DecidableEq`. Give a `Fintype` for a phase type containing it
    through `show Fintype WindowExit from ⟨…⟩`.
  - `(Sigma.mk.inj h).2` is a `HEq`: use `eq_of_heq`.
  - A dotted constructor of `WindowExit` in a redirect table needs its type,
    `(WindowExit.halted : WindowExit)`.
- `phaseHostTM_run` gives the prefix up to `T` and the dispatch at `T + 1`; its `hguard` must hold
  strictly before `T`. A row whose entry equals its verdict has `T = 0`.
- **F2's runner takes the native input as digits** (`x.map (RecSym.digitEmb M.State T)`), which is
  your configuration's input; its clock tape is `Fin.last (K + 1)` of `K + 2` tapes. If `rw`
  complains about `K + 2` against `K + 1 + 1`, `show` the goal.
- `Nat.ofDigits 2 (List.replicate W true |>.map Bool.toNat) = 2^W - 1`: prove it once, by
  induction on `W`.
- `RecordAt d 0 fs` includes the blank delimiters at `-1` and at `(joinFields fs).length`.
  `cfgRecord`'s fields are nonempty (`Turing.cfgRecord_field_ne_nil`).
- `Cfg.inputPos` starts at `1`. The writer and the clear never move the input head.
- `omega` with products and powers as atoms (`ring` first to expose them). The linter needs a
  literal "Proof sketch" before every `sorry` (partial only).
