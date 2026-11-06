# Ch3–4 fill campaign — B6's H, the space hierarchy and its corollaries (`Hierarchy.lean`)

Targets: `Complexity.space_hierarchy`, `LOGSPACE_ssubset_PSPACE` and `SPACE_linear_ne_NP`, in
`TCSlib/Complexity/SpaceComplexity/Hierarchy.lean`.

> **Issued** (maintainer, 2026-11-06; drafted 2026-10-27, revised after the brief review
> `campaign/fills/b6/drafts/b6-fill-hierarchy/review-2026-11-06/`: 1 blocker, 5 majors, all
> folded in). PRs #175, #177, #181, #191, #196, #202, #207 and #209 have merged; the pre-ship ran
> on the merged tree (`campaign/fills/b6/logs/b6-fill-hierarchy-preship.log`), and your base is
> `e6bc1968`. **Ruled (user,
> 2026-11-06):** `SPACE_linear_ne_NP` stays H's last checkpoint and may end in a named escalation
> (see the route). **Agent: Codex** (user, 2026-10-27).

> **A single fill** (addendum v2.6, Parts 1 and 2; Part 3, the megafill, does not apply, except
> its one-Lean rule and its no-stop rule, items 5 and 7, which "Environment and verification"
> restates). Deliver a checkpoint zip after each checkpoint: the session may end at any time.

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor e6bc196838b4e2675e4214306c730e7404624ab8 HEAD` succeeds. If it
  fails, **stop**. That commit contains:
  - **your targets as gated statements**: the P4.3 statement gate (`campaign/gates/ch4-p43/`),
    the space hierarchy's statement re-gated on the window route (2026-10-13);
  - **every host the route names, proved** on the standard axioms or fewer. The route's original
    hosts have 17 axiom prints (`campaign/status/2026-10-27-headlines/HHosts.*`): the universal
    machine `Turing.exists_selfUniversal` (`TuringMachine/SelfUniversal`); the record rows
    `Turing.exists_recordInitTM` (`Build/RecordTable`) and `Turing.exists_recordTestTM`
    (`Build/CfgRecord`); the configuration-count runner `Turing.exists_configWindowRunnerTM`
    (`SpaceComplexity/WindowClock`, **its clock inside it**); the window run's facts; the normal
    forms; the space facts and readings. The hosts this revision adds (the returning capture
    embedding and R1 in `Build/Embed`, the seam's general-configuration forms, the contract
    layer, the rewinds, the summary update, the published space clause of the coding step) are
    walked, with the main original hosts, by the extended import probe's 86 axiom prints, every
    one within `[propext, Classical.choice, Quot.sound]` (no `sorryAx`);
  - **`Complexity.spaceConstructible_poly` in `SpaceComplexity/Constructible`** (PR #175, gate 86),
    which your file already imports; `SPACE_linear_ne_NP` needs it at degree two;
  - the fill-agent environment addendum `campaign/standards/fill-environment-addendum.md`
    (**v2.6**), and the copy-text screen v3 `scripts/copy-text-screen-v3.py`;
  - **this round's inputs** (`campaign/fills/b6/inputs/b6-fill-hierarchy/`): the import probe
    (`HImportProbe.lean.txt`, 72 names) and its extension (`HImportProbe2.lean.txt`, 171 checks:
    the 72 and every name this revision newly cites, with the 86 axiom prints), the route probe
    (`HRouteProbe.lean.txt`) with its seal controls, the semantic-duplication probe, the import
    overlay (`HierarchyOverlay.lean.txt`) and the screen population; the order list
    `campaign/fills/b6/orders/b6-fill-hierarchy.txt`, the base sorry set, the screen base and the
    pre-ship log (`campaign/fills/b6/logs/b6-fill-hierarchy-*`). The route's design note is
    `campaign/items/b6hosts/H/H-route-design.md`; where it and this brief differ (the capture
    wrapper, the seam's `Bool` space lemmas, its line numbers), this brief governs.
- **Before anything else, run Part 1 of the addendum**: the preflight, with its stop rule (E-RES).
  Fetch the cache for your roots only (63 Mathlib roots, in the pre-ship log); never run the
  unfiltered `lake exe cache get`. If Lean cannot start, follow Part 2 exactly. **If Lean never
  runs, do not draft proofs blind**: deliver the environment report only.
- **Branch at exactly that commit, not at the campaign tip:**

  ```sh
  git checkout -b fill/b6-hierarchy e6bc196838b4e2675e4214306c730e7404624ab8
  git rev-parse HEAD        # must print e6bc196838b4e2675e4214306c730e7404624ab8
  git rev-parse HEAD:TCSlib/Complexity/SpaceComplexity/Hierarchy.lean
  # must print 287acce8326a1de271dfa6be2cc3776f3a2caa32
  ```

  Record the base hash in `REPORT.md`. Never rebase, merge or cherry-pick.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-b6-hierarchy.zip`, attached in
  your reply, with
  `REPORT.md`, the full modified source, a `git format-patch` series against your base, a git
  bundle whose only prerequisite is your base, the environment logs (`evidence/logs/`), the
  bootstrap and final sweep logs with **each module's time and maximum memory**, the axiom log, the
  seal test's source, its controls and both outputs, both screen outputs, and `SHA256SUMS`.
- **Checkpoint zips.** After each checkpoint below, commit and write
  `fill-b6-hierarchy-cp<N>.zip` (`N` 1 to 8) with the same contents as of that commit. Deliver the
  latest if the session ends early.

## Base, line numbers and what lands around you

- **Your base's Lean content is the campaign's tree after PRs #175, #177, #181, #191, #196, #202
  and #207** (the pre-ship's `d43a1374`). Lines in this brief are those of your base's tree, where
  `Hierarchy.lean` is 317 lines (4 public declarations, no private).
- **The overlay is your first edit** (region (a)): add, after line 10, exactly
  `import TCSlib.Complexity.TuringMachine.SelfUniversal`,
  `import TCSlib.Complexity.TuringMachine.Build.WindowRun`,
  `import TCSlib.Complexity.SpaceComplexity.WindowClock` and
  `import TCSlib.Complexity.ClassNP.PClosure` (for `preimage_mem_NP`; it brings
  `Mathlib.Tactic.Linarith` into the file's environment)
  (`HierarchyOverlay.lean.txt` is the file after it). The pre-ship elaborated it: exactly the four
  sorry warnings, at the overlay's lines 154, 271, 288 and 318 (the base's 150, 267, 284 and 314),
  nothing else. Every host this brief cites is in the overlay's import closure (the extended
  probe imports nothing else).
- **In flight:** #208, the deepening fill's landing: `SavitchARM/Deepen` (new, not in your order
  list) and, in your order list, `Savitch`, `Machines/Bin` (one new lemma,
  `length_bits_succ_le`) and proof-only re-points in `Machines/ARMWidth`,
  `Machines/ARMWidthExample`, `ExpBFS/Main`, `SavitchARM/Correct`, `Logspace/PathHardRegs` and
  `Logspace/ISCountGenCorrect` (no statement changes). It is replayed on the merged tree before it
  merges; cite nothing it adds, and name no private `length_bits_succ_le`. If #208 merges first,
  `savitch` leaves the base sorry set; that is not a difference you need to explain. #211
  (`Robustness/TwoTapes`, G5) is outside your order list. Your base contains #209
  (`NTimeHierarchy`'s docstring, outside your order list); nothing in your closure changes.

## Parallel batches this round

None in `Hierarchy.lean`: **F6** (`Complexity.space_universal`, line 150, the same file) is out of
scope and waits for a later round; leave its statement, docstring and body untouched.

## What this is

**The space hierarchy theorem** ([AB09, Theorem 4.8]; [SHL65] through [AB09]). For
space-constructible `f` and `g` with `∀ A, ∃ N, ∀ n ≥ N, A · f n ≤ g n`: `SPACE f ⊂ SPACE g`. Then
two corollaries in the same file:
- `LOGSPACE_ssubset_PSPACE` ([AB09, §4.3.2]): `space_hierarchy` at `logSpace` and `n + 1`;
- `SPACE_linear_ne_NP` ([AB09, Exercise 3.2], at the normalization `n + 1`).

**Where it stands.** The three bodies are `sorry`. Every host of `space_hierarchy` and
`LOGSPACE_ssubset_PSPACE` is proved; the route probe proves the inclusion half and
`LOGSPACE ⊂ PSPACE` from the hierarchy's statement. **Proved modulo, exactly:** none.
`SPACE_linear_ne_NP` has published hosts for its reduction and its extraction but **none for the
padded language's decider** (see the route): it may end in a named escalation. **A complete
delivery has no `sorryAx` in the three targets**; a delivery whose last checkpoint ends in that
escalation has none in the first two.

**Read first:** the route note `campaign/items/b6hosts/H/H-route-design.md` (it maps the
docstring's sketch onto the published hosts and says where this brief supersedes the sketch); the
three targets' docstrings (lines 163–313); `exists_configWindowRunnerTM`'s statement
(`WindowClock.lean:1503`); `exists_selfUniversal` (`SelfUniversal.lean:143`);
`exists_recordInitTM` (`RecordTable.lean:5805`); `embedSilentRetTM_run` (`Build/Embed.lean:828`)
and the transport's field lemmas after it (`Embed.lean:983–1051`).

**Pre-ship check** (the maintainer, against the replay snapshot of your base's tree; log
`campaign/fills/b6/logs/b6-fill-hierarchy-preship.log`): the overlay as above; the import probe
72 checks of 72 names, 0 errors; the route probe's four lemmas (`hr_inclusion`,
`hr_sq_le_two_pow`, `hr_logSpace_dom`, `hr_logspace_ssubset`) through published readings only,
sealed (5 definitions) with 9 controls (9 pass unsealed, 9 fail sealed), and three axiom prints
on the standard axioms (not `hr_sq_le_two_pow`'s); the duplication probe: of its six `exact?`
calls, only `logSpace_le_succ` (which the route does not need) and `LOGSPACE_subset_PSPACE`
(cited below) close; the order list 220 modules, 63 roots, 26 base sorries in 10 modules; the
screen base (over the 43 files) 1,854 declarations, 1,689 pairs, none on `Hierarchy`; lint 0 FAIL, 80 WARN over 111
files. **This revision** (2026-11-06): the extended import probe, 171 checks, 0 errors, and 86
axiom prints, none outside the standard three, against the campaign's snapshot after #209
(the same closure); the review's probe (`review-2026-11-06/HRevProbe.*`) showed the seam's
`Bool` space lemmas reject a record-alphabet machine and `captureCfg` has no reading under the
seal.

## Owned regions and targets (modify these and nothing else)

`TCSlib/Complexity/SpaceComplexity/Hierarchy.lean`:
- **(a)** the imports, lines 6–10: add exactly the overlay's four;
- **(b)** new private declarations after `space_universal`'s body (line 161) and before
  `space_hierarchy`'s docstring (line 163), in sections of your own if you like;
- **(c)** the three bodies: lines 271 (`space_hierarchy`), 285 (`LOGSPACE_ssubset_PSPACE`) and 315
  (`SPACE_linear_ne_NP`);
- **(d)** the status text and internal labels, rewritten as public-facing text, keeping the
  mathematics and the references:
  - the module docstring (lines 16–80): the intro's "per the P0 convention —
    `AroraBarakChapters3-4Plan.md` §2.4", "Phase P4.3" and the dated restatement and gate history
    (lines 22–28); "design §16b item 3" (line 48) and "(Finding B, recorded in the sketches)"
    (line 58); "(round-1 confirmed, recorded in the sketch)" (lines 61–62) and "while the P4.1
    gate was live; … since that gate closed" (lines 63–65); "(all sorried; phase-P4.3
    statements)" (line 67); **except** `space_universal`'s entry (lines 69–70), which is F6's;
  - `space_hierarchy`'s docstring (lines 163–266): "spec, fill pending — phase P4.3, … RD-3
    statement gate passed 2026-10-13" (lines 164–165), "(recorded here, seeded to the audit)"
    (line 173), "the P0 zero-bound convention" (lines 174–175), the registry names "H2", "H3"
    and "H5" (lines 187, 189, 206, 255–258), "R8.5d; decision O6" (line 198), "design §12.8a
    decision O4" (line 211), "(W1)" (line 212), "§12.7 and R8.0b" (line 213), "(round-1 finding
    5)" (line 227), "design §14" (line 255) and "record-table row 18; row 17" (line 259);
  - `LOGSPACE_ssubset_PSPACE`'s (lines 273–283): "spec, fill pending" (line 274) and "of phase
    P4.1" (line 279);
  - `SPACE_linear_ne_NP`'s (lines 287–313): "per the P0 convention" (line 288), "spec, fill
    pending" (line 289) and "(round-2 finding 5)" (line 298).

  No phase, gate, round, finding, decision, design-section, registry-row or fill names, no
  `audits/` or `campaign/` paths, no dated rulings. `space_universal`'s docstring (lines 86–149)
  is F6's: leave it as it is. Propose an `**Implementation.**` paragraph for each target's
  docstring in `REPORT.md` (the clock is the runner's, not the sketch's step (iii); the capture
  is `embedSilentRetTM`); the maintainer lands them.

**Targets:** `Complexity.space_hierarchy` (line 267), `Complexity.LOGSPACE_ssubset_PSPACE` (line
284), `Complexity.SPACE_linear_ne_NP` (line 314); statements frozen.

### Hosts (binding; the host-first rule, `policy.md` §1, `workflow.md` §2)

Write `e := RecSym.digitEmb Q₀ (Fin 3)` for the digit embedding into the record alphabet.

- **The universal machine** is `Turing.exists_selfUniversal`: one `U₀` for the scheme
  `Complexity.TimeHierarchy.code`, with, per code `α`, a `C > 0` such that a halting run of
  `decode α` on `pairEncode α w` within space `s` is reproduced by `U₀` with the same output within
  space `C · (s + 1)`. Never build a second universal machine.
- **The run** is `Turing.exists_configWindowRunnerTM` at `U₀` with **`T := Fin 3`,
  `upd := Turing.summaryTag` and `hupd := Turing.summaryTag_none`**: the only update
  `windowRun_summary_of_halts` is stated for, with the initial tag `0`. Write no summary update of
  your own. From a radius-`r` record of a configuration in its window on tape 0, **every other tape
  of its bank blank** (`WindowClock.lean:1512`), it reaches an exit `out` within
  `C · 2^(C (L + 1))` steps in space `(K + 1)(2C(L + 1) + 1)`, silently, with `out` the window
  run's verdict at every non-exhausted round count up to `configBound + 1`, and, unless
  `out = exhausted`, the record of the window run's endpoint left on tape 0 for **some** round
  count `N`. **The clock is inside it: build no clock, counter loop or round driver of your own.**
- **The initial record** is `Turing.exists_recordInitTM` (`RecordTable.lean:5805`) at radius
  `s = g n`, `ws = (g n).bits` (its `Nat.ofDigits` premise by `counterValue_eq` and
  `counterValue_bits`) and `τ₀ = 0`, the empty-output tag (`outSummaryCode_nil`). Its premises:
  input head at `1`; `ws.map RecSym.digit` readable from tape 1's head over `[-1, |ws|]`; tape 0
  blank over the record's span; tapes `≥ 2` blank. Its record is of `Cfg.init q₀ x`;
  `MultiTapeTM.initCfg_eq` turns that into `U₀.tm.initCfg x`. Its endpoint changes only tape 0.
- **The radius** is `g`'s constructibility witness `M_g` (`spaceConstructible_iff`), lifted and
  run under the **returning capture embedding**
  `Turing.embedSilentRetTM ι cap (M_g.tm.liftSymbols e)` (`Build/Embed`), the selection `ι` the
  witness bank and `cap` the radius tape:
  - the run: `embedSilentRetTM_run` (lockstep, then the live return anchor `Sum.inr ()` exactly
    at the witness's first halt, its final emission recorded);
  - the readings: `embedSilentCfg_cap` (the captured word `bufferTape (pre ++ c.output)`, the head
    just after it), `embedSilentCfg_unselected`, `embedSilentCfg_selected_tape`/`_pos`, and the
    `simps` equations `embedSilentCfg_state`/`_inputPos`/`_output`;
  - the space: `embedSilentRetTM_visitedByTapeHead` (the returning flavor visits what the closed
    one does), then `embedSilentTM_visitedByTapeHead` (the bank: the witness's own cells),
    `embedSilentTM_visitedByTapeHead_frame` (each other tape: one cell) and
    `embedSilentTM_spaceUsedByTape_cap` (the radius tape: the output's growth plus one);
  - the lift: `MultiTapeTM.liftSymbols_runFrom`, `liftSymbols_initCfg`, `liftSymbols_spaceUsed`
    and the field equations `Cfg.liftSymbols_state`, `_workTapePos`, `_inputPos`, `_workTapes`,
    `_output`.

  With `pre = []` the radius tape starts blank (`FinTM.bufferTape_nil`) and ends holding
  `bufferTape ((g n).bits.map e)`, which is `bufferTape ((g n).bits.map RecSym.digit)` by
  `RecSym.digitEmb_apply`: the form `exists_recordInitTM` reads. **Do not use**
  `Turing.capture_run` or `capture_visitedByTapeHead`: they are `Bool`-only and conclude about
  `captureCfg`, which has no published reading (rule 10). `Contract.liftSymbols` needs an
  input-blind machine and does not apply to the witness.
- **The input validation** is `Turing.inputFoldTM` (`inputFoldTM_run_ofCfg`: entry and exit with
  the input head at `1`, no work head moved): reject at once a rich input that is not an embedded
  word, so `D`'s space is bounded on every input of the rich alphabet.
- **The rewinds** (after the witness):
  - **the input head**, anywhere in `[0, |x| + 1]` at the witness's halt, must be at `1` for
    `exists_recordInitTM`. `inputRewindTM_run` is `Bool`-only and needs `1 ≤ inputPos`: run
    `(inputRewindTM 0).liftSymbols e` (no work tapes; `liftSymbols_runFrom`) on `D`'s tapes by
    R1 along `Fin 0 ↪ Fin K_D` (below), after a **one-step leaf of your own** that moves the input
    head right (`MultiTapeTM.step_of_some`, `moveInputPos_pos_of_ne_right`,
    `moveInputPos_rightBoundary`): from `0` it reaches `1`, from `p ≥ 1` it stays `≥ 1`;
  - **the radius tape**, whose head the capture leaves at `|ws|`: `Turing.rewindTM_run_ofCfg` at
    `n = |ws|` puts it on the word's first cell, as `exists_recordInitTM` reads it.
- **The verdict's test** is `Turing.exists_recordTestTM` (`CfgRecord.lean:5396`) at
  `k := U₀.k` and `P q τ := decide (q = none ∧ τ = 1)`, a one-tape machine run on the record tape
  by R1. The record it reads is the runner's endpoint for some `N`; identify it with
  `windowRun_summary_of_halts`'s at `N = configBound + 1` by `windowRun_stop_unique`. On
  `exhausted` tape 0 is unspecified: answer `true` without the test (and on `left`, either way).
  The answer is written by a **one-step emitter leaf of your own** (`[e b]`, then halt).
- **The composition**, on general configurations over any alphabet (the seam's `Bool`
  corollaries `seamCompTM_spaceUsed_le_add`, `seamCompTM_spaceUsedByTape_le_add` and `_le_max`
  are stated over `MultiTapeTM k Bool _` and `Cfg.ofWords` and **do not apply** to `D`):
  - the seam: `seamCompTM_run_ofCfg`, `seamCompTM_firstReturn_ofCfg`,
    `seamCompTM_visitedByTapeHead_ofCfg`, and `seamCompTM₂_run_ofCfg` for the fold's two verdicts
    and the runner's exits;
  - R1, to host a phase with fewer tapes on `D`'s: `embedEmitTM`, `embedEmitTM_runFrom`,
    `embedEmitTM_frame`, the reconstruction `embedEmitCfg_eq`/`embedEmitCfg_select`,
    `embedEmitCfg_selected_tape`/`_pos`, `embedEmitCfg_unselected`, `Cfg.select`;
  - or the contract layer `Turing.Contract` (`Build/Contract/{Basic,Seam,Embed}`: `Contract.seq`,
    `Contract.embed`, `Contract.within`, `Contract.spaceUsedByTape_le`); `Contract.embed`
    transports output-normalized preconditions only.
- **The space route:** per tape, the union of the phases' visited sets
  (`seamCompTM_visitedByTapeHead_ofCfg`, then the embeddings' visited lemmas above), or head
  envelopes (`Contract.spaceUsedByTape_le`, `MultiTapeTM.spaceUsedByTape_le_card_Icc`,
  `MultiTapeTM.spaceUsed_le_of_abs_le` for the record rows' and runner's displacement bounds),
  summed over the tapes by `MultiTapeTM.spaceUsed_eq_sum`.
- **The packaging** is `Turing.FinTM.decidesInSpace_of_alphabetReduction` (`ConfigCount:568`) at
  `e`: a `Bool` decider of `L_D` in space `c_D · (g n + 1)`, in `SPACE g` by `g`'s floor
  (`SPACE.mono_const`). Define `L_D` through `D`'s output (`MultiTapeTM.indicator` in `hD`), not
  through `windowRun`: the runner pins its exit only for non-exhausted `N ≤ configBound + 1`.
- **The normalization** (for `L_D ∉ SPACE f`):
  `FinTM.ComputesInSpace.computesFunInTime_and_forall_spaceUsed_le` (a time bound and the space
  bound at every time), `Turing.FinTM.one_work_tape_binary_spaceUsed` (one work tape, constant
  `c₁`), and **`Turing.exists_codeTM_spaceUsed`** (`Encoding.lean:741`: a coded machine with the
  same halting runs and the same space at every time), with `MachineCode.decode_encode` for
  `code.decode (code.encode N) = N`. Never re-derive the space clause through
  `relabelState_runFrom_init` and the `M.k = 1` cast (rule 5).
- **The window facts:** `FinTM.inWindow_of_spaceUsed_le`, `windowRun_summary_of_halts`,
  `windowRun_stop_unique`, `FinTM.configBound_le_two_pow`, `outSummary_append_congr`,
  `outSummary_eq_accept_iff`, `outSummaryCode_eq_one_iff` (the tag `1` is exactly the output
  `[true]`), `Cfg.inWindow_init` (the runner's `InWindow` premise at the start, at every radius),
  `FinTM.ComputesInTime.of_spaceUsed_le`, `FinTM.ComputesInTime.spaceUsed_le_of_halt` (the space
  at time `configBound`; `MultiTapeTM.spaceUsed_mono` points the wrong way past the halt),
  `MultiTapeTM.abs_pos_lt_card_visited`, `mem_visited_of_ne_none`; the records' readings
  `recordAt_iff`, `recordLength_eq`, `joinFields_cfgRecord_length`, `posWidth_eq` and
  `Complexity.LogProg.length_bits_le_log` (`posWidth n = O(logSpace n)`, which `g`'s floor
  absorbs); `length_pairEncode` (`n ≥ N₀`) and `length_bits_le_self`.

### The route (binding where it names a row; the rest is the recommended shape)

**The inclusion** (`SPACE f ⊆ SPACE g`): the route probe's `hr_inclusion` (`hfg` at `A = 1` from
some `N` on, `g`'s floor below `N`, `SPACE.mono_const`). Copy it as a private, **renamed
`sph_inclusion`**.

**The diagonalizer `D`**, over the record alphabet `RecSym Q₀ (Fin 3)` (`Q₀` the states of `U₀`),
on the embedded input `x.map e`, as phases composed by the seam host:
1. validate the input (`inputFoldTM`); on a foreign input, halt;
2. the radius: `M_g`, lifted, under `embedSilentRetTM` on the witness bank, writes
   `bits (g n)` on the radius tape (`r = g n`);
3. the rewinds: the radius tape (`rewindTM`), then the input head (the one-step right move, then
   the lifted `inputRewindTM 0` by R1);
4. the initial record of `U₀`'s start on `x` at radius `r`, with the empty-output tag, by R1;
5. the run: `exists_configWindowRunnerTM` at `U₀` with `summaryTag`, by R1;
6. the verdict: on `halted`, the record test, then `false` if it says yes and `true` otherwise; on
   `left` or `exhausted`, `true`; the emitter leaf writes it.

**The tape plan** (recommended; its constraints are binding): tape 0, the record (the record
rows', the runner's and the test's tape 0); tape 1, the radius (the capture tape `cap`,
`exists_recordInitTM`'s tape 1); a blank bank for `exists_recordInitTM`'s tapes `≥ 2` and the
runner's tapes `≠ 0` (one bank of `max(K_I, K_R)` tapes may serve both, since the record
initializer changes only tape 0); the witness bank, `M_g.k` tapes, dirty after the radius phase.
**The runner's bank must not contain the radius tape or the witness bank.** The fold and
`rewindTM` run on `D`'s tapes directly; the input rewind is embedded on no tape.

**`D`'s space**: the witness's `c_g · g n` (its bank), the radius tape's `|bits (g n)| + 2`, the
record's `L = recordLength U₀.k n (g n) = O(g n + log n)`, the record rows' and runner's
displacements `O(L + g n)`, the test's `O(L)`: all `O(g n)` by `g`'s floor, **uniformly in the code
part of `x`**: the window, not `U₀`'s constant, bounds the simulation (the runner's constants
depend only on `U₀` and `Fin 3`).

**`L_D ∉ SPACE f`.** If `M` decides `L_D` in space `c₀ · f`, normalize it (the normal form's
constant `c₁`), take its code `α`, and pad the payload, never the code: on
`x = pairEncode α (List.replicate N₀ true)` with `N₀` from `hfg` at `A := C_α (c₁ · c₀ + c₁ + 1)`
(`C_α` from `exists_selfUniversal`, using `1 ≤ f n`), `U₀`'s run stays in the radius-`g n` window
and halts within `configBound` rounds, so the runner exits `halted` with the summary of `U₀`'s
output, which is `[x ∈ L_D]`; `D` answers the opposite.

**`LOGSPACE ⊂ PSPACE`**: the route probe's `hr_logspace_ssubset` applied to `space_hierarchy`, with
`hr_logSpace_dom` and `hr_sq_le_two_pow`. Copy the three as privates, **renamed
`sph_logspace_ssubset`, `sph_logSpace_dom` and `sph_sq_le_two_pow`**; the inclusion is the
published `Complexity.LOGSPACE_subset_PSPACE` (`SpaceClasses`, after #181), which the probe
already cites: never re-prove it (the ledger's LS-1).

**`SPACE (n + 1) ≠ NP`** (checkpoint 8): by padding and `NP`'s closure under `≤ₚ` (the
docstring's sketch). **It may end in a named escalation** (the user's ruling, 2026-11-06): no
host is published for the **padded language's decider**, that is, for validating the pad's length
and running `L`'s decider on the input's first component within space linear in the padded
length. If you cannot build it from named hosts, **stop on that item only**, leave
`SPACE_linear_ne_NP`'s body `sorry` with a literal "Proof sketch", and state the missing lemma
(its statement, in `REPORT.md`'s escalations). `space_hierarchy` and `LOGSPACE_ssubset_PSPACE`
do not depend on it. What is published:
- **`NP`'s closure**: `Complexity.preimage_mem_NP` (`ClassNP/PClosure`, PR #177: `NP` is closed
  under polynomial-time preimages; with `L ≤ₚ L'` by `p`, `L = p ⁻¹' L'`): cite it, never re-prove
  it; `NP`'s reading is `mem_NP_iff_exists_length_le`, `≤ₚ` is `Complexity.PolyTimeReducible`;
- **the padding map's polynomial time**, if the pad has length `(|x| + 1) ^ 2`, that is
  `p x := pairEncode x (List.replicate (1 * (|x| + 1) ^ 2) true)`:
  `polyTimeComputable_id.pairEncode (polyTimeComputable_polyUnary 1 2)`
  (`PolyTimeComputable.pairEncode`, `ClassNP/PolyTimePairing`); `p ⁻¹' L' = L` by
  `pairEncode_injective` or `pairFstD_pairEncode`/`pairSndD_pairEncode`;
- **parts of the decider**: the first component computed on the native input and installed on
  a work tape, `FinTM.exists_inputCallTM` at `FinTM.computesFunInTime_pairFst` (time only; its
  space by `MultiTapeTM.spaceUsed_le_mul_succ`); a machine run on a buffered word, Z1's
  `vhostEmitTM` (`vhostEmitTM_runFrom`, `vhostEmitTM_spaceUsed_le`: the source's space plus
  `|y| + 2`; the layout `vhostCfg` and its field equations, `vhostCfg_workTapes` and the like).
  **Unhosted:** the pad-length test in space `O(|y|)`, and the assembly of these into a `Bool`
  decider of `L'` in `SPACE (m + 1)`;
- **the strictness extraction**, through `space_hierarchy` at `n + 1` and `n ^ 2 + 1`
  (`spaceConstructible_linear`, `spaceConstructible_poly 2 (by norm_num)`;
  `A · (n + 1) ≤ n ^ 2 + 1` for `n ≥ A + 1`).

**Edge cases that must stay true:** the empty input; an input of the rich alphabet that is not an
embedded word (rejected by the fold, in bounded space); the witness's input head at `0` at its
halt (the one-step right move); `U₀` halting with an output other than `[true]` (`true` from
`D`); the window exit and the clock's exhaustion (`true` from `D`, the latter without the test);
`n` below `N₀` (the padding chooses `n ≥ N₀`); `f`'s floor `1 ≤ f n` (the arithmetic of `A`).

## Gate guidance (binding)

- **The P4.3 statement gate** froze the statements; the hierarchy's constant-factor hypothesis has
  no square and no logarithmic term; both constructibility hypotheses are the book's, and the proof
  uses `g`'s witness and floor but, of `f`'s, only the floor.
- **The route note's rulings:** H first, the corollaries as later checkpoints of the same fill; F6
  after U2's harvest. **The user's ruling (2026-11-06):** `SPACE_linear_ne_NP` stays H's last
  checkpoint and may end in the named escalation above.

## Cited infrastructure (public and proved at the issue commit; all in `HImportProbe2.lean.txt`)

The import probe's 72 names: the targets and the space classes with their readings
(`mem_SPACE_iff`, `SPACE.mono`, `SPACE.mono_const`, `decidesInSpace_iff`, `computesInSpace_iff`,
`spaceConstructible_iff`, `LOGSPACE_eq`, `space_poly_subset_PSPACE`, the three constructible
rows); the universal machine and its code scheme; the runner and the window run with its records,
widths, alphabet and facts; the record rows; the output summary; the alphabet reduction and its
space clause; the input fold; the symbol lift; the seam's `Bool` space lemmas and the `Bool`
capture wrapper (cited there; not used by the route); the space and visited-interval facts; the
normal forms; the counter value's readings; the API of #175, #177 and #181. **The extension's
99 more:** the returning capture embedding and its readings; the lift's field equations; the
seam's general-configuration forms, R1 and the contract layer; the space-from-envelope lemmas;
the rewinds and the one-step leaf's lemmas; the record test; the small readings; the summary
update; `exists_codeTM_spaceUsed`; `NP`'s bounded-certificate reading, `≤ₚ` and the padding's
hosts.

## Ground rules (binding)

1. **File ownership, by region.** Only regions (a)–(d) of `Hierarchy.lean`. List every new
   declaration with its role.
2. **Statement freeze** over the three targets and `space_universal`.
3. **No new public declaration.**
4. **Escalation, item by item:** on anything unprovable as stated, stop **on that item only**,
   record the obstruction mathematically, and **continue with every item that does not depend on
   it**. The corollaries depend on `space_hierarchy`'s statement only, so they may be proved
   before it; nothing depends on `SPACE_linear_ne_NP`.
5. **No touching other sorries**, `space_universal`'s among them. Cite proved material; never
   re-prove it.
6. **Imports.** Exactly the base's five and the overlay's four; add none.
7. **One proof per shared argument.** Never write a second universal machine, clock, counter loop,
   record row, window runner, seam, symbol lift, tape embedding or capture transformer: the
   radius phase runs under the published `embedSilentRetTM`, and your only leaves are the
   one-step input move and the one-step emitter. Never re-walk `TimeHierarchy/Diagonal`'s or
   `TimeHierarchy/Separation`'s privates (a colleague's diagonalization), `WindowClock`'s or
   `RecordTable`'s privates: models to read, not to copy.
8. **Size.** No cap; file size alone is not a driver. Report the final line count and the public
   and private declaration counts (base: 317 lines; 4 public, 0 private).
9. **Continuation budget.** A partial zip states the checkpoints reached, the open declarations
   (each with a literal "Proof sketch") and each target's axiom walk.
10. **The pinned base, and no unfolding (user, 2026-10-16).**
    - Cite only declarations public at your base, and your file's own definitions and privates.
    - **Never unfold a definition of another file**, and no definitional closure either:
      `SPACE` through `mem_SPACE_iff`; `FinTM.DecidesInSpace` and `FinTM.ComputesInSpace` through
      `decidesInSpace_iff` and `computesInSpace_iff`; `SpaceConstructible` through
      `spaceConstructible_iff`; `logSpace` through `logSpace_eq`; `LOGSPACE` through
      `LOGSPACE_eq`; `PSPACE` only through `space_poly_subset_PSPACE`; `NP` through
      `mem_NP_iff_exists_length_le`; the window run, records and summaries through their lemmas;
      the transports `embedSilentCfg`, `embedEmitCfg`, `Cfg.select` and `Cfg.liftSymbols` through
      the field lemmas the hosts list names.
    - **Scope (user, 2026-10-23):** TCSlib's own definitions. Core and Mathlib definitions may
      reduce in a `rfl`, `decide` or `show` step, but are never passed to `simp`, `rw` or `unfold`.
    - **The machine model's primitives** are read through their lemmas; unfold `step` and
      `Action.apply` only for a leaf of your own file, preferring `MultiTapeTM.step_of_some` and
      the `Action.apply_*` field equations.
    - If a fact you need about another file's definition has no published lemma, **stop on that
      item and escalate**, naming the lemma you need.
    - **Self-check by both methods:** a **seal test** (a scratch copy of your module with
      `attribute [local irreducible]` on every other-file TCSlib definition your proofs mention,
      from your first private on: at least the route probe's five (`SpaceConstructible`,
      `SPACE`, `logSpace`, `LOGSPACE`, `PSPACE`) and the transports and record definitions you
      reach (`embedSilentCfg`, `embedEmitCfg`, `Cfg.select`, `Cfg.liftSymbols`, `summaryTag`,
      `outSummaryCode`, `windowRun`, `cfgRecord`, `RecordAt`, `recordLength`, `posWidth`,
      `FinTM.bufferTape`); `attribute [-simp]` on the four `@[simp]` TCSlib definitions
      `Action.apply`, `Cfg.init`, `MultiTapeTM.initCfg`, `NDTM.initCfg`; **with controls**: for
      each sealed definition, a goal that closes by `rfl` with nothing sealed and fails under the
      seal, recursive definitions with usage controls); and an **inspection table** of every
      `rw`/`simp`/`simpa`/`dsimp`/`unfold`/`show`/`change` argument in your diff. **Ship the raw
      outputs.** A seal not run, or without controls, is a checklist failure.
    - List every declaration you cite outside your file; if more than `HImportProbe2`'s, extend a
      copy of it and run it.
11. **MIG-1 compatibility.** Cite none of the six R3 canonical rows (`copyTM_run`,
    `transferTM_run`, `clearTM_run`, `compareTM_run`, `incrementTM_run_succ`,
    `incrementTM_run_overflow`); use the framed `_ofCfg` forms. Cite no private declaration of
    another file. Keep **every** new private under the `sph_` prefix, the route probe's copied
    `hr_*` lemmas included (`Sph`/`sph` for types and definitions; `sph_` is unused in the tree at
    the issue commit, while `sh_` is not: `ExpBFS/Run`'s `sh_run`).

### Checkpoints (for a partial; ground rule 9)

1. **The overlay and the inclusion** (`sph_inclusion`).
2. **`D`'s first phases**, each a framed run on the tape plan (a `Turing.Contract` or the
   `_ofCfg` run lemmas): the validation, the radius under `embedSilentRetTM`, the two rewinds,
   the initial record.
3. **`D`'s run and verdict**: the runner at `U₀` by R1, its exits read through the window run,
   the record test and the emitter.
4. **`D`'s space and the packaging**: `L_D ∈ SPACE g`.
5. **The normalization and the window**: `U₀`'s run on the padded code stays in the window and
   halts within `configBound`.
6. **`space_hierarchy`.**
7. **`LOGSPACE_ssubset_PSPACE`.**
8. **`SPACE_linear_ne_NP`**, or its named escalation (the padded decider's missing lemma).

Each may land alone. **Add no new admission.** **One checkpoint, one commit, one zip, delivered at
once.**

## Duplication governance (binding)

Run the text-level screen **before and after**, **one run at a time, under `nice -n 10`**, each on a
frozen copy of its commit (`git worktree add <dir> HEAD`). **Semantic duplication (required):** for
every private lemma you add, search for a published declaration that states it or a
generalization, in the tree and on every open PR branch, by name and by statement (`git grep`), and
by an `exact?` or `apply?` probe; `REPORT.md` lists the search and result per private. **The
population** is 43 files, all listed in `screen-population.txt`: the pre-ship's 27 (your file;
the 22 other modules declaring the import probe's names, `TimeHierarchy/Diagonal` among them; `ClassNP/NP`; the known
hazards `TimeHierarchy/Separation`, `SpaceComplexity/Savitch`, `ClassNP/Nondeterminism` for the
padding precedent) **plus the 16 modules this revision newly cites**:
`TuringMachine/Build/Embed`, `Build/Contract/Basic`, `Build/Contract/Seam`,
`Build/Contract/Embed`, `Build/InputRewind`, `Build/Rewind`, `Build/InputCall`,
`Build/Primitives`, `Build/VirtualInput`, `TuringMachine/Configuration`,
`TuringMachine/Deterministic`, `TuringMachine/Finite`, `TuringMachine/Simulation`,
`SpaceComplexity/Machines/Bin`, `ClassNP/PolyTime`, `ClassNP/PolyTimePairing`. **The pre-ship
base** is `campaign/fills/b6/logs/b6-fill-hierarchy-screen-base.txt`, over the 43
(`campaign/fills/b6/inputs/b6-fill-hierarchy/screen-population.txt`): 1,854 declarations, 1,689
pairs, 534,736 characters, none on `Hierarchy`. Your before-screen over the 43 files must
reproduce it and is your base for new pairs; `REPORT.md` states both counts. A new cross-file pair with an
owned-file declaration on one side is listed with one disposition (idiom; re-derivation of a
published lemma: cite it instead; re-derivation of another file's private: keep yours and request
a promotion); a pair at 90% or more is a copy. `REPORT.md` carries **"new copies: none"** or lists
each pair, and ships both full outputs.

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; the cache **for your roots only**; **never `lake build`**, never
  the unfiltered `lake exe cache get`; `scripts/lean_check_tree.sh` for every check, one Lean
  process at a time (a screen may run beside one). The cache tool's own compilation inside
  `lake exe cache get` is outside the one-Lean rule. **A process deviation never ends the item.**
- **Bootstrap** from `campaign/fills/b6/orders/b6-fill-hierarchy.txt` (220 modules), right after
  branching, logging each module's time and maximum memory. **The base sorry-warning set** has
  26 entries in 10 modules; yours are `Hierarchy`'s four. Record the base list by name first.
- **Final checks:** `Hierarchy`: zero errors, exactly one sorry warning (`space_universal`'s; for a
  partial or the escalation, also the open targets'); every other module: zero errors and the
  base's sorry warnings; `HImportProbe2` re-run, 0 errors. **After every proof edit**, check
  `Hierarchy` and its only importer, the facade `TCSlib/Complexity/SpaceComplexity`; the final
  sweep runs the order list's tail from your module on (52 modules).
- **Axiom prints** for the three targets and every new private: within
  `[propext, Classical.choice, Quot.sound]`, no `sorryAx` for a complete delivery.
- **Lint:** `python3 -I scripts/campaign_style_lint.py TCSlib/Complexity/SpaceComplexity`, 0 FAIL
  (base: 0 FAIL, 80 WARN over 111 files), and `scripts/style_lint.py` on your file (base: one
  finding, the module docstring's missing `## Main definitions`); no new line over 100 characters.

## Out-of-scope sorries you will see (leave every one untouched)

Everything in the base sorry set except your three targets: `space_universal` (F6, your file),
`Complexity.savitch` (`SpaceComplexity/Savitch`), and the rest of the list in
`campaign/fills/b6/logs/b6-fill-hierarchy-base-sorries.txt`.

## REPORT.md checklist

- [ ] The preflight, the roots and the cache fetch (with the logs), the bootstrap with per-module
      time and memory, the base blob check.
- [ ] The overlay only; nothing outside regions (a)–(d); `space_universal` untouched.
- [ ] The checkpoints reached (1–8), one zip each; the base hash and the ancestor check.
- [ ] Every new declaration with its role; `D`'s phases and its tape plan; the radius under
      `embedSilentRetTM`; the rewinds; the runner's call and the test's.
- [ ] `D`'s space bound, term by term, and its uniformity in the code part of `x`; the constant
      `A` of the contradiction, with `c₁` and `C_α` named.
- [ ] The base sorry list by name; each edge case with the lemma that covers it.
- [ ] Promotion candidates and escalations (for checkpoint 8, the missing lemma's statement), or
      "none"; the proposed `**Implementation.**` paragraphs.
- [ ] Rule 10: the citations outside your file (an elaborated-constant walk), the probe re-run,
      **the seal test with its controls and both raw outputs**, the inspection table. Rule 11: a
      grep of your diff for the six R3 rows and other files' private names; every private `sph_`.
- [ ] Duplication: both v3 screens on the 43-file population, every new pair justified, the
      semantic search per private, "new copies: none".
- [ ] File size; the final sweep tail; the axiom prints; the lint line.

## Known pitfalls at this pin (hard-won)

- **The simps field equations are pointwise**: `funext` before `rw`, or the step closes by
  unfolding and the seal rejects it.
- **`logSpace` is not `Nat.log 2`**: `logSpace n = Nat.log 2 n + 1` (`logSpace_eq`), so it is at
  least `1` everywhere; the floors come from `spaceConstructible_iff`'s first conjunct.
- **`SPACE` absorbs constants** (`SPACE.mono_const`): prove the bound `c · (g n + 1)` and absorb
  it by `g`'s floor, not by unfolding `SPACE`.
- **`PSPACE` has no reading of its own here**: reach it through `space_poly_subset_PSPACE`.
- **The window lemma fixes the update**: `windowRun_summary_of_halts` holds only at
  `upd := summaryTag` and the initial tag `0`; the runner's endpoint clause gives some `N`
  (`windowRun_stop_unique` aligns it).
- **The `Bool`-only rows**: `capture_run`, `inputRewindTM_run` and the seam's space corollaries
  are stated over `Bool`; on `D` use `embedSilentRetTM`, the lifted rewind by R1 and the
  `_ofCfg` forms.
- **No core or Mathlib definition is reduced outside `rfl`, `decide` or `show`.** `omega` with
  products as atoms (`ring` first). The linter needs a literal "Proof sketch" before every
  `sorry` (partial only).
