# Ch3–4 fill campaign — C1, wave 1, R continuation 1: the interpreter core for nondeterministic codes (`Turing.exists_ndInterpreterCore`, `NDCodeSimulator.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor @ANCESTOR@ HEAD` succeeds. If it
  fails, **stop**. That commit contains:
  - **your target as a gated statement** (the C1 host-contracts gate,
    `campaign/gates/12-c1-hosts-statements/findings.md`, PASS 0/0/11; resolutions
    `campaign/gates/12-c1-hosts-statements/resolutions.md`; the prefix clause is the repaired one of
    its minor M4);
  - C1's design (`campaign/items/c1/C1-design.md`; `R` is §3.6, the replay route is the user's
    decision 3) and C1's fill plan (`campaign/items/c1/C1-fill-plan.md`; you are wave 1's R);
  - **the hosts:** H1's hosted counter loop over H2's step block (`Build/StepBlockLoop`, PR #94),
    Z1 (`Build/VirtualInput`), the prefix canonizer (`UniversalStartup`), the install call
    (`Build/Loop`), the replay machine (`ChoiceReplay`), R1′'s returning embedding (`Build/Embed`);
  - **the seam layout** (PR #124; its statement gate passed in round 2,
    `campaign/gates/43-seam-layout-statements/`): `Turing.exists_seamLayoutTM`
    (`Build/SeamLayout`, sorried), the one public machine that redistributes a serialization
    `pairEncode a ((q ones, a zero) ++ v)` onto the step block's table and summary tapes. It is
    the user's ruling on your first round's route gap G2;
  - **the API PRs** (the user's "Everything" rule, 2026-10-16): the specification API (PR #112),
    the core API (PR #116), the brief-inventory API (PR #118), the ND inventory API (PR #119: the
    hosted loop's definitions, Z1's `vhostCfg` fields, the replay machine's fields) and its round
    2 (PR #122: **`Turing.counterValue_eq`** and `codeBitsNat_eq`, your first round's escalation
    E1);
  - **the first round** (2026-10-17): the worker's report
    `campaign/fills/c1/reports/core-1-REPORT.md` and the maintainer's review
    `campaign/fills/c1/reviews/core-1/REVIEW.md`, with its draft probe `DraftProbe1.lean.txt`;
  - the fill-agent environment addendum `campaign/standards/fill-environment-addendum.md`
    (**v2**: Part 1, the resources and the cache, applies on every host), and the
    declaration-keyed copy-text screen v3 `scripts/copy-text-screen-v3.py`;
  - **this round's inputs** (`campaign/fills/c1/inputs/c1-fill-core-cont1/`): the import overlay
    (your file with the three imports and the four drafts), the drafts alone (`R-drafts.lean.txt`),
    the import probe and the screen population. Also the order list
    `campaign/fills/c1/orders/c1-fill-core-cont1.txt`, the base sorry set, the screen base and the
    pre-ship log (`campaign/fills/c1/logs/c1-fill-core-cont1-*`).
- **Before anything else, run Part 1 of `campaign/standards/fill-environment-addendum.md`**: the
  preflight, with its stop rule (E-RES). The first round was blocked by its environment (a full
  disk while fetching the cache, then a crash on the first bootstrap module). If Lean cannot
  start, follow Part 2 exactly.
- **Branch at exactly that commit, not at the campaign tip:**

  ```sh
  git checkout -b fill/c1-core-cont1 @ANCESTOR@
  git rev-parse HEAD        # must print @ANCESTOR@
  ```

  Record that hash as your base in `REPORT.md`. Never rebase, merge or cherry-pick.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-c1-core-cont1.zip`. It
  contains:
  - `REPORT.md` and the full modified source;
  - a `git format-patch` series against your base, and a git bundle whose only prerequisite is
    your base;
  - the bootstrap and final sweep logs and the axiom log;
  - both screen outputs, and `SHA256SUMS`.
- **Checkpoint zips.** After each phase below, commit and write `fill-c1-core-cont1-cp<N>.zip`
  with the same contents as of that commit (the final sweep may be your module's check only), so
  that a lost workspace loses at most one phase. Deliver the latest if the session ends early.

## Base, line numbers and what lands around you

- **Your base's Lean content is the campaign tip after #124** (`dac6b3b0`, #124's merge). The
  inputs commit adds no Lean change. `NDCodeSimulator.lean` has 147 lines there, unchanged since
  #94 except its module docstring (the first round's imports and appendix were not landed).
- **Your first edit makes your file equal to the overlay**
  (`NDCodeSimulatorOverlay.lean.txt`): the three imports after line 8, and the four drafts after
  the replay canonizer's `sorry`. **Line numbers below are the overlay's.** Every probe and
  measurement below was run on the overlay, against the olean snapshot of #124's replay
  (`oleans-lseam2`).
- **In flight, merging after your base and invisible to it:** #129
  (`Diagonalization/NTimeHierarchy`, your consumer UN's partial), #130 (`UniversalK`), #131
  (`CodeSimulator`, which your file imports; private lemmas only), #132 (`Build/Primitives`,
  `Simulation`), the ruler device's landing (`Build/InputDevice`), and the fills of
  `Build/InputWindow` (WC, whose target you cite), `Build/SeamLayout` (whose contract you cite),
  `Build/ZoneRebalance`, `Build/CfgRecord` and `ClassNP/ExhaustiveReplay`. Cite nothing they add.
- **Your file's other stub,** the replay canonizer `exists_replayCanonizer` (line 94), is wave
  2's and stays sorried: you cite its statement.

## Parallel batches this round

None in `NDCodeSimulator.lean`. WC (`Build/InputWindow`) and the seam-layout fill
(`Build/SeamLayout`) prove contracts you cite. Your consumers come later: UN (the universal NDTM)
and the diagonalizer's middle rung (C1-E).

## What this is

**C1's interpreter core `R`** (C1's design §3.6): one deterministic machine, uniform over codes,
that runs the coded NDTM's branch along a guessed stream at linear overhead. One target, frozen:
1. **`Turing.exists_ndInterpreterCore`** (line 229): for every effective scheme `c`, a machine `R`
   with a stream tape `j` and verdicts `accept ≠ reject`, such that for every code `α` there is `C`:
   from `entry` on `z = ⟨⟨bits t, α⟩, x⟩` with a stream `s` (`t ≤ |s|`) on tape `j`, `R` reaches
   `accept` iff the decoded machine's branch on `x` along `s.take t` halted with output `[true]`,
   at a time `T ≤ C·(t + 1)` with no earlier verdict, and `T ≤ C·(t' + |x| + |bits t| + 1)` whenever
   the branch along `s.take t'` already halted (the prefix clause).

**The first round** was environment-blocked: it delivered no checked proof, but four drafts that
the review elaborated verbatim (0 errors), the conditional ledger, and two findings that this
brief resolves: E1 (the loop's counter value needs `counterValue_eq`, now published by #122) and
G2 (no public machine split the serialization into the step block's layout, now
`Turing.exists_seamLayoutTM`, by the user's ruling).

**Proved modulo, exactly:** `Turing.exists_replayCanonizer` (your file, wave 2),
`Turing.exists_inputWindowCopyTM` (WC) and `Turing.exists_seamLayoutTM` (the seam-layout fill).
Cite their statements; never their bodies.

**The four drafts** (`R-drafts.lean.txt`; the overlay's lines 99–195), pre-verified at this
base: re-elaborated in the overlay with only the two stubs' sorry warnings; the first three
depend on `[propext, Classical.choice, Quot.sound]`, and `ic_table_call` adds `sorryAx` only
through the cited replay canonizer:
- `ic_header_result`: either prefix pass halts at the suffix with its component (`bits t` or
  `α`), head at `4|bits t| + 2|α| + 7`, time `16|bits t| + 8|α| + 25`;
- `ic_capture_return`: a bounded native-input run captured silently by R1′ with a first live
  return at the first halt;
- `ic_replay_window`: replaying any prefix `r ≤ t` of the stream on the window `x.take t` gives
  the original branch's state and output;
- `ic_table_call`: the replay canonizer called through the install interface, installing the
  whole `serializeK (c.decode α).tm.replayTM`, at a cost depending on `α` alone.

Keep them (you may restate them; report each change).

**The published lemmas your route reads** (ground rule 10):
- **the header** (`UniversalStartup`): `prefixCanonTM`, `prefixCanonTM_eq`, `prefixCanon_complete`;
  `FinTM.pairExtractTM_fst`, `_snd` (`5·(n + 1)` steps); `FinTM.timed_rewind`;
  `pairDecode_pairEncode`, `length_pairEncode`, `pairEncode_eq`;
- **the capture** (`Build/Embed`): `embedSilentRetTM`, `embedSilentRetTM_run`, `embedSilentCfg`
  and `embedSilentCfg_cap`, `embedSilentCfg_*`; `MultiTapeTM.exists_first_halt`,
  `MultiTapeTM.initCfg_eq`, `Cfg.init`'s fields;
- **the installation** (`Build/Loop`): `FinTM.exists_installCallTM`, `stateWord`, stated through
  `Cfg.ofWords` seams (`Cfg.ofWords_state`, `_inputPos`, `_workTapes`, `_workTapePos`, `_output`);
- **the layout** (`Build/SeamLayout`): `exists_seamLayoutTM`, with `serializeK_eq`, `unaryFin_eq`,
  `FinTM.bufferTape_of_neg`;
- **the window:** `Turing.exists_inputWindowCopyTM`, with `counterValue_eq` and `counterValue_bits`;
- **the loop** (`Build/StepBlockLoop`): `StepBlock.hostedLoopTM_run` (the early-escape bound is
  the prefix clause), `StepBlock.hostedLoop_read` (the verdict), with `StepBlock.Rep_iff`,
  `exit_true`, `exit_false`, `summaryTape_eq`, `tableTape_eq`, `outputSummary_nil`,
  `outputSummary_true`, `summaryCells_eq`, `vhostCfg`'s fields and `vhostBank_eq`,
  `counter_cfg_eq`;
- **the code and its replay:** `serializeK_eq`, `tableBitsK` read opaquely,
  `CodeNDTM.serialize_eq_tableBitsK` (proved, your file), `CodeNDTM.toFinNDTM_k`, `_State`, `_tm`,
  `NDTM.replayTM_runFrom`, `replayTM_q₀`, `_tr`, `withChoiceTape`'s fields,
  `NDTM.runWith_initCfg_take` (input locality), `NDTM.initCfg_eq`;
- **composition:** `seamCompTM_run_ofCfg`, `seamReleaseTM_firstReturn`, `phaseHostTM_run`,
  `embedSilentTM_runFrom` and `embedSilentCfg_*`;
- **the model:** `MultiTapeTM.step_of_some`, `step_of_halt`, the run algebra, `Action.apply`'s
  fields, `Cfg.mapState`'s fields, `FinTM.computesInTime_iff`; arithmetic `length_bits_le_self`.

**Read first:**
- the target's docstring, whose proof sketch is binding where this brief does not refine it;
- `StepBlock.hostedLoopTM_run` and `hostedLoop_read`, all their hypotheses and both exits;
- `exists_seamLayoutTM`'s statement, and the seam-layout gate's consumer probe
  (`campaign/items/c1/seam-layout/r2/SeamLayoutConsumerR2.lean.txt`): its derivation 3 assembles
  `Rep`'s table and summary fields from the layout's end through `FinTM.bufferTape_of_neg`,
  `outputSummary_nil`, `summaryCells_eq` and `Rep_iff`. **It is a reference, not a citation**:
  its declarations are probe-local;
- `UniversalStartup`'s `prefixCanon_complete` and the chapter-1 startup it serves
  (`universalCanonTM`, `universalCaptureTM`): the model, not a citation of their privates.

**Pre-ship check** (maintainer, at the base, against `oleans-lseam2`;
`campaign/fills/c1/logs/c1-fill-core-cont1-preship.log`):
- **The overlay** (`NDCodeSimulatorOverlay.lean.txt`) elaborates with your file's two sorry
  warnings (lines 94 and 229) and nothing else; the drafts' axioms are as above. No import cycle:
  none of the three imports' closures contains your file.
- **The import probe** (`C1CoreCont1ImportProbe.lean.txt`, 96 `#check`s: round 1's 77, the drafts'
  12 external citations, `outputSummary_true`, `length_bits_le_self`, `counterValue_eq`,
  `codeBitsNat_eq`, `exists_seamLayoutTM`, `FinTM.bufferTape_of_neg`, `unaryFin_eq`): every public
  declaration this brief cites resolves from the overlay's import context. 0 errors, 0 warnings.
  Re-run it after your delivery.

## Owned regions and targets (modify these and nothing else)

| # | File:line (overlay) | Target |
|---|---|---|
| 1 | `NDCodeSimulator.lean:229` | `Turing.exists_ndInterpreterCore` |

Your regions:
- **(a) the imports**, as your first edit: exactly
  `import TCSlib.Complexity.TuringMachine.Build.InputWindow`,
  `import TCSlib.Complexity.TuringMachine.UniversalStartup` and
  `import TCSlib.Complexity.TuringMachine.Build.SeamLayout`, after line 8. No other import.
- **(b) one home**, for your `private` declarations: the overlay's lines 98–196, between the
  replay canonizer's `sorry` and your target's docstring, holding the four drafts first. `private`
  only, and no `section`, `open` or `variable` that leaks past one.
- **(c) the body**, the `sorry` on line **246**.
- **(d) for a partial only, a paragraph headed `**Implementation status.**` at the end of the
  target's docstring**, before its closing ` -/` (line 228). It is public-facing library text:
  what is proved and what is open, in mathematical terms, with no campaign labels (brief, gate,
  finding or escalation names), no dates and no session narrative. The same holds for the
  docstrings of your new declarations; provenance goes in `REPORT.md`.

Frozen: the module header and docstring, the bridge, **the replay canonizer's statement and its
`sorry`**, your target's statement and its docstring before (d), and every other file. The
maintainer updates the module's status text at integration.

### Route (binding; the host-first rule, `policy.md` §1, `workflow.md` §2)

The docstring's route, refined by the first round's review. Never write a second host, seam,
embedding, loop, clock or layout machine.
- **Startup, the header.** `z = pairEncode u x` with `u = pairEncode (bits t) α`.
  - **Two prefix passes**, `ic_header_result` at `first := true` then `false`: each outputs its
    component and halts with the input head at the suffix's first cell. Rewind the native input
    head between them (`FinTM.timed_rewind`).
  - **Each pass runs silently in a fresh bank, its output captured by R1′**
    (`embedSilentRetTM`, through `ic_capture_return`). R1′'s live return anchor is what a seam
    needs; R1's `embedSilentTM` halts with its source. The source's final work tapes have no
    published description: frame them, and never read them.
  - Join the passes by `seamCompTM_run_ofCfg`. Each costs `O(|u| + 1)`: a per-code constant plus
    `O(|bits t|)`.
  - **Do not run the canonizer through `prefixCanonTM`:** its time bound is a function of `|u|`,
    which grows with `bits t`.
- **Startup, the table and the initial state (G2).**
  - **Install the whole serialization** `serializeK (c.decode α).tm.replayTM` by `ic_table_call`,
    on the captured `α`: the installed word sits at offset `0` with its head at `0`, at a cost
    depending on `α` alone.
  - **Then redistribute it by `Turing.exists_seamLayoutTM`**, with `src` the tape holding the
    installed word and `tbl`, `sm` the step block's table and summary tapes (three distinct
    tapes). By `serializeK_eq` and `unaryFin_eq`, the word is the contract's
    `pairEncode a ((List.replicate q true ++ [false]) ++ v)` at `a = n.bits`, `q = q₀` and
    `v = tableBitsK tr`, with the source head's start `r = 0`. Its end has `tbl` holding `v` and
    `sm` holding the unary state from cell `2`, `src` cleared, every other tape and head
    unchanged, at a time `T ≤ C_L·(|serializeK …| + 1)`, a per-code constant.
  - **`Rep`'s table and summary fields** follow from that end as in the consumer probe's
    derivation 3: `tableTape_eq`, and for the summary `outputSummary_nil`,
    `FinTM.bufferTape_of_neg` (cells `0` and `1`) and `summaryCells_eq` (the rest), assembled by
    `Rep_iff` with the native-input and mirrored-bank fields. **No separate install of the unary
    state is needed.**
- **The window.** Keep a second copy of `bits t` first (the window copy consumes its counter).
  Copy `x.take t` with `exists_inputWindowCopyTM`: the input head is at the start of `x`, the
  native position its contract wants. The window's length reads through
  `(counterValue_eq _).symm.trans (counterValue_bits t)` (E1), and `(pairEncode u x).drop
  (2|u| + 2) = x` follows from `pairEncode_eq` and the length lemmas. Rewind the window.
- **The loop.** `StepBlock.hostedLoopTM_run` at three work tapes, the stream as the mirrored choice
  tape, hosted by Z1 on the window, over the counter `bits t`, from the replay machine's
  represented start. Its counter hypothesis is
  `ht := (counterValue_eq _).symm.trans (counterValue_bits t)` (E1). Establish `Rep` as above and
  Z1's configuration through `vhostCfg`'s fields. **The verdict** reads H2's output summary at the
  live exits (`hostedLoop_read`, `outputSummary_true`).
- **`Cfg.Halted`** is a reducible `abbrev` for `state = none` with no iff lemma. Reading
  `¬ Cfg.Halted c` as `c.state ≠ none` is allowed, as `ic_capture_return` does when it passes
  `embedSilentRetTM_run`'s hypothesis.
- **The semantics.** `ic_replay_window` identifies the simulated run with the coded branch along
  `s.take r` on the window, and with the branch on `x` (input locality). `CodeNDTM.toFinNDTM_tm`
  reads the decoded machine.
- **The ledger** (the first round's, checked by the review, with the layout added):
  - Startup: a per-code constant (`ic_table_call`'s cost and the layout's `C_L·(|s| + 1)`) plus
    `O(|bits t|)` (one pass: `16|bits t| + 8|α| + 25`; both with the rewind: `36|bits t| +
    18|α| + 59`).
  - Window: `w·(min(t, |x|) + 1) + 2|bits t|`.
  - Loop: the escape bound `t'·50·(|table| + 1) + 4t' + 2|bits t|` when the branch halts by `t'`,
    or the full count otherwise.

  That gives both clauses with one per-code `C`: the first round's
  `C = a + b + w + 50(L + 1) + 10` (checked by the review), with the layout's per-code time added
  to the startup's constant, using `length_bits_le_self` (`|bits t| ≤ t`).
- **Promotion candidates** (list each in `REPORT.md`; notes only): the two-pass header split
  (`ic_header_result`; UN's setup and B5a's H1 also need it); the first-halt R1′ capture
  (`ic_capture_return`; three inline uses exist).

## Gate guidance (binding)

- **The C1 host-contracts gate** fixed the statement, including the repaired prefix clause (its
  minor M4; `campaign/gates/12-c1-hosts-statements/resolutions.md`). **The design's ledger** (C1's
  design §3.6) is the intended one; a coarser bound that loses the prefix clause is a statement
  failure, not an option.
- **The seam-layout gate** (round 2, PASS): the layout's time is chosen before the configuration,
  depending on the word and the source head's start only; cite it as stated.
- **Edge cases that must stay true of your proof:**
  - `t = 0`: `bits 0 = []`, the window is empty, the loop runs no round, and `R` rejects, since an
    initial configuration is live (no branch has halted at `t' = 0`);
  - `|x| < t`: the window copy stops early; locality still applies, since `x.take t = x`;
  - `|s| > t`: only `s.take t` matters;
  - a code `α` whose decoding is any machine: `c.decode` is total.

## Cited infrastructure (public and proved at the issue commit, except the three cited stubs; all in `C1CoreCont1ImportProbe.lean.txt`)

The probe's names, in nine groups: the window copier's statement; the header; the capture; the
installation; the layout; the loop; the code and the replay; composition; the model. The target,
the replay canonizer and the bridge are in your file.

## Ground rules (binding)

1. **File ownership, by region.** Only regions (a)–(d) of `NDCodeSimulator.lean`. List every new
   declaration with its role.
2. **Statement freeze** over the target and every landed declaration.
3. **No new public declaration.**
4. **Escalation, item by item:** on anything unprovable as stated, stop **on that item only**,
   record the obstruction mathematically, and continue with every item that does not depend on it.
   The first round's phases 1 and 2 did not depend on its escalation.
5. **No touching other sorries** (the replay canonizer's stays). Cite proved material; never
   re-prove it.
6. **Imports.** Exactly the three in region (a).
7. **One proof per shared argument.** Never write a second loop, step block, Z1, seam, phase host,
   embedding, prefix parser or layout machine. Never re-walk `UniversalStartup`'s or
   `CodeSimulator`'s privates.
8. **Size.** No cap; file size alone is not a driver. Report the final line count and the public and
   private declaration counts (overlay: 249 lines; 3 public, 4 private).
9. **Continuation budget.** A partial zip states the phase reached, the open declarations (each with
   a literal "Proof sketch") and the target's axiom walk. A partial is expected and fine; an
   unreported gap is not.
10. **The pinned base, and no unfolding (user, 2026-10-16).**
    - Cite only declarations public at your base, and your file's own privates.
    - **Never unfold a definition of another file**, and no definitional closure either (a `rfl`,
      `exact`, `show`, `decide` or `simp` step that closes only because another file's definition
      reduces). Read every definition through its published lemmas. In particular read
      `prefixCanonTM` only through `prefixCanonTM_eq` and `prefixCanon_complete`, and
      `counterValue` only through `counterValue_eq`; the buffered composite's configurations
      (`bufferedSecondCfg`) are not on this route.
    - **The machine model's primitives** (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
      `Cfg.mapState`, `NDTM.stepWith`, `NDTM.runWith`) are read through their lemmas. The coded
      machine is arbitrary: read it only through the replay lemma and the replay machine's fields.
      Unfold `step` and `Action.apply` only for a leaf defined in your own file.
    - If a fact you need about another file's definition has no published lemma, **stop on that
      item and escalate** (ground rule 4), naming the lemma you need.
    - **Self-check:** a seal test (a scratch copy of your module with `attribute [local
      irreducible]` on every other-file definition your proofs mention, which must still
      elaborate) and an inspection of every `rw`/`simp`/`simpa`/`unfold` argument in your diff.
    - List every declaration you cite outside your file. If you cite more than the probe's list,
      add them to a copy of the probe and run it.
11. **MIG-1 compatibility.**
    - Cite none of the six R3 canonical rows.
    - Cite no private declaration of another file.
    - Keep your new privates under the `ic_` prefix.

### Phases (for a partial; ground rule 9)

1. The startup: the two prefix passes; the table call and the seam layout, with `Rep`'s table and
   summary fields.
2. The window.
3. The loop and the verdict.
4. The semantics and the ledger, both clauses.

## Duplication governance (binding)

Run the text-level screen **before and after**, **one run at a time, under `nice -n 10`**
(`campaign/standards/TEMPLATE.md` failure mode 5; `policy.md`, **Duplication**). Run the before
screen **after your first edit** (the overlay's state): it must equal the screen base.
- **The population** is 11 files
  (`campaign/fills/c1/inputs/c1-fill-core-cont1/screen-population.txt`): your file; `CodeSimulator`
  (H1's region, the main hazard); `Build/StepBlockLoop`; `UniversalStartup`; `UniversalK` (U2's
  startup, a sibling); `ChoiceReplay`; `Build/InputWindow`; and, for this round's route,
  `Build/SeamLayout`, `Build/Embed` (R1′), `Build/Loop` (the install call) and `Build/CertShell` (an
  inline first-halt capture).
- **The screen** is `scripts/copy-text-screen-v3.py`, on the repository paths.
- **The base** is `campaign/fills/c1/logs/c1-fill-core-cont1-screen-base.txt`, measured on the
  overlay: **407 declarations, 115 pairs, 43,357 characters** (MEASURED).

```sh
P=campaign/fills/c1/inputs/c1-fill-core-cont1
nice -n 10 python3 -I scripts/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/screen-population.txt) > /tmp/screen-before.txt
# after your changes, again, only when the first run has finished
nice -n 10 python3 -I scripts/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/screen-population.txt) > /tmp/screen-after.txt
```

- **No new cross-file pair** with an owned-file declaration on one side. Nothing is pre-disclosed.
- **Known hazards:** the chapter-1 startup (`universalCaptureTM` and its run); U2's startup
  (`UniversalK`); `CodeSimulator`'s H1 assembly; the inline first-halt captures
  (`Build/CertShell`'s `certCore_run`). Follow their pattern, never transcribe it. A pair at 90%
  or more is a copy.
- List every new in-file pair with a one-line justification. Quote both outputs in `REPORT.md`,
  which carries **"new copies: none"** (or lists each pair).

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake build`**. Use
  `scripts/lean_check_tree.sh` for every check.
- **Bootstrap once** from `campaign/fills/c1/orders/c1-fill-core-cont1.txt` (**81 modules**: the
  upstream closure of your owned file, with the three imports, and of every module downstream of
  it, without the root `TCSlib`), after your first edit.

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < campaign/fills/c1/orders/c1-fill-core-cont1.txt )
  ```

  **The base sorry-warning set has 35 entries in 15 modules**
  (`campaign/fills/c1/logs/c1-fill-core-cont1-base-sorries.txt`). Yours is `NDCodeSimulator`'s
  `exists_ndInterpreterCore`; its other entry, the replay canonizer, stays. Record the base list by
  name first, and report any difference.
- **Final checks:**
  1. `NDCodeSimulator`: zero errors, exactly the replay canonizer's sorry warning (for a partial,
     plus the open declarations'), and no other warning in anything you added.
  2. Every other module of the order list: zero errors, and sorry warnings exactly the base's minus
     yours.
  3. Re-run `C1CoreCont1ImportProbe.lean.txt`: 0 errors.
- **Axiom prints** for the target and every new private: within
  `[propext, Classical.choice, Quot.sound]` plus the `sorryAx` of the three cited stubs (the
  replay canonizer, the window copier, the seam layout), and nothing else.
- **Lint:** `python3 -I scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine`, 0 FAIL
  (base: 0 FAIL, 63 WARN over 80 files). No new line over 100 characters.

## REPORT.md checklist

- [ ] The preflight's numbers (addendum v2, Part 1).
- [ ] The target proved (or the phase reached), modulo exactly the three cited stubs; the base
      hash and the ancestor check; the checkpoint zips written.
- [ ] The three imports and the four drafts as the first edit (the overlay, byte for byte), and
      nothing else outside regions (b)–(d); any draft restated, with the reason.
- [ ] Every new declaration with its role; the status paragraph, if a partial.
- [ ] The tapes chosen for the layout (`src`, `tbl`, `sm`) and how `Rep`'s fields were assembled.
- [ ] The per-code constant `C`, and the ledger of both clauses.
- [ ] Promotion candidates and escalations (each stated mathematically), or "none".
- [ ] Rule 10: the declarations cited outside your file, the probe re-run, the seal test and the
      inspection. Rule 11: a grep of your diff for the six R3 rows and for other files' private
      names.
- [ ] Duplication: both v3 screens, every new pair justified, "new copies: none".
- [ ] File size; the final sweep tail; the axiom prints; the lint line.

## Known pitfalls at this pin (hard-won)

- **`Cfg.inputPos` is shifted by one.** In `pairEncode u x` the suffix `x` starts at index
  `2|u| + 2`, native position `2|u| + 3`, which is where `prefixCanon_complete` leaves the head.
- **`pairEncode` doubles its first component:** `u` takes `2|u|` cells, then the separator
  `[false, true]`.
- **The replay machine puts the choice tape last**, and the step block mirrors the source's tapes
  first: the stream is the replay machine's last tape.
- **The seam layout's three tapes must be distinct** (`src ≠ tbl`, `src ≠ sm`, `tbl ≠ sm`), and it
  clears `src`: install the serialization on a scratch tape, not on a tape you still need.
- **`counterLoopOrbit` is an `abbrev`:** `rw` may not fire on it, while `exact` and `simp only` do
  (#118's note N3).
- **`StepBlock.exit k live` is a sigma type:** rewrite it with `exit_true` and `exit_false`.
- `omega` with products as atoms (`ring` first). The linter needs a literal "Proof sketch" before
  every `sorry` (partial only).
