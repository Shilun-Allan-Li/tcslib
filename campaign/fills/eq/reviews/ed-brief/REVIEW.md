**Verdict: issue after edits.** Do not issue the draft as written. It has one blocker (F1): the route needs one own leaf, which is the maintainer's decision. It also has three majors (F2-F4), nine minors and four notes. Apply `suggested-fix.diff`, which implements option (a) of F1, after deciding F1. The diff applies to the draft at `615e56b4` and also to its later revision at `ae0011e5`. The math (time bound, `K`, `C`, middle, top) is sound, and the pre-ship reproduces exactly.

# Review: the E-D fill brief draft (`eq-fill-diagonalizer.DRAFT.md`, `Turing.NTimeDiag.exists_diagonalizer`)

This is a read-only review by the maintainer's review sub-agent, done on 2026-11-04.

## Inputs and method

- **The draft** is `campaign/fills/eq/drafts/eq-fill-diagonalizer.DRAFT.md` at `615e56b479dff522dd34bd5eca194471e6c9ec33`, SHA-256 `ae31d4fa4d9f3093bea31ed5ad12eec53b7c6cd9dd227f5a0b705ca35c5550b8`. A copy is in `orig/`. While I worked, `wt-hk` moved to `ae0011e5`, where the draft is `3bebdf24…`. That revision changes only the screen-base sentence (draft lines 289-291), which my diff does not touch (out/applycheck.txt).
- **The tree** is `029f3aa92970159c40f5d12e7fdc47c03c6cd61a`: PR #176's head at the time of the pre-ship, with the campaign merged in. The owned blob is `852931eb9347377fcd2e4e3c1e754462b236c1ad`, the same at `cecd76a0` and at `f69b86b9`. I checked every hash with `rev-parse`.
- **The worktree** is `wt/`, detached at `029f3aa9`. I checked that `reviews/ed-brief` was absent first, and linked `.lake/packages`. Probe files went only into `wt/rvprobe/`, with copies in `probe/`.
- **Lean** ran only through `tools/leanelab.sh` against `oleans-lscp3`, one elaboration at a time. I ran no build, no cache command and no copy-text screen. Probes that need #176's file used an overlay copy elaborated as its own module, as the pre-ship did.
- **Python** ran with `python3 -I`. My scripts are in `tools/`: the closure, order, roots and sorry census (`closure.py`, `closure2.py`, `sorries.py`) and the asserted draft edits (`apply_edits.py`). I also ran the repository's two read-only lint scripts at the base.
- **Untouched:** `wt-hk`, the main checkout and `wt-edps` were not modified, and nothing was committed or pushed.
- **Evidence:** every raw output is in `out/`. `out/00-runs.txt` tabulates each Lean run: exit status, time, memory, and whether it is identical to the pre-ship's output.

## (a) The pre-ship, re-run

| # | Check | Result | Evidence |
|---|---|---|---|
| 1 | Overlay (`NTimeDiagonalizerOverlay`) | The overlay is the base file plus exactly the three imports after `Build/WordTests` (diff). It exits 0 with one warning, `5409:8` "declaration uses 'sorry'" (= 5406 + 3), in 16.6 s and 2.36 GB. Its output is identical to the pre-ship's | out/NTimeDiagonalizerOverlay.out |
| 2 | Import probe | 59 `#check`s, exit 0, no errors and no warnings. Its output is byte-identical to the pre-ship's after normalizing paths | out/EDImportProbe.out |
| 3 | Route probe (sealed over 11 definitions, four `@[simp]` erased) | Exit 0 with 12 axiom prints: 8 on the standard three and 4 on `[propext, Quot.sound]`. Identical to the pre-ship's | out/EDRouteProbe.out |
| 4 | Seal controls (17) | Unsealed, 15 pass: the delta goals of the recursive `ladder` and `NDTM.runWith` fail, and their `eqn` controls pass. Sealed, all 17 fail. Both outputs identical | out/EDSealControl_{unsealed,sealed}.out |
| 5 | Duplication probe (9 `exact?`) | 2 close (`length_bits_le_self`, `counterValue_bits`) and 7 errors by design (exit 1). Identical | out/EDDupProbe.out |
| 6 | Order list, roots | I derived the closure of the `Diagonalization` facade with the overlay substituted, independently: **84 modules, the same set**, and the order is topological (0 violations). There are **34 Mathlib roots, the same set**. The overlaid file's closure grows from 37 to 50 modules, **13 joining**. The owned file's reverse dependents are only `NTimeHierarchy`, the facade and `TCSlib`, so there is no cycle. The root `TCSlib` is correctly not in the list | out/closure-*.txt, out/order-*.sorted, out/roots-*.sorted |
| 7 | Base sorries | My comment-stripped census over the 84 modules finds **19 declarations in 9 modules**, the same names | out/base-sorries-derived.txt |
| 8 | Lint | At the base: 0 FAIL, 3 WARN over 5 files, with the file at **5,432** lines. The pre-ship's "base" lint shows 5,435 (style_lint 5,436), so it ran on the overlay commit. The counts are equal (F11) | out/lint-base-Diagonalization.txt, out/style-lint-base.txt |
| 9 | Line numbers and counts | 5,432 lines, 22 public and 214 private declarations. `exists_queryTM`'s proof ends at 5344, the docstring runs 5346-5405, the statement is at 5406 and the `sorry` at 5430. Line 70 holds "(sorried; C1-E's second fill)". "(C1-E; …)" is at 5346, "P3.3 gate's round 2" at 5347 and "(the statement gate, finding 1)" at 5400. All correct | file |
| 10 | Axioms of what the route cites (new) | Every public row the draft cites or this review proposes is free of `sorryAx`. So are `exists_queryTM` and E-Q's leaves in #176's file. Only the target carries `sorryAx`. Nearby, `FinTM.lengthBitsTM_computes` carries `sorryAx`; `computesFunInTime_lengthBits` does not (F13) | out/RVRouteRows.out, out/RVOverlayAx.out, out/RVSorriedRows.out |

## (b) The route: feasibility from published rows, and the mathematics

**What holds.**
- **The host.** `guessRunTM_haltsWithin` and `guessRunTM_accepts_iff` take exactly the draft's shape:
  - a setup `P` with first exit `TP`;
  - `hblock`/`hend`/`hleft` on tape `j` (a nonblank block of `m` cells from the head, blank at `m` and at `-1`);
  - a uniform `T` for every stream's first verdict;
  - acceptance at every `B ≥ TP + 2m + T + 11` iff some stream reaches `acc` with output `[]` (NDHost.lean 1405-1511).
- **Acceptance.** Its left side is `FinNDTM.AcceptsWithin` verbatim (`acceptsWithin_iff`, NTIME.lean 104), so `D` bundles directly.
- **The core.** `exists_ndInterpreterCore` (NDCodeSimulator.lean 894-912) starts from `⟨some entry, 1, fun i => if i = j then FinTM.bufferTape s else fun _ => none, fun _ => 0, []⟩` on `⟨⟨bits t, α⟩, x⟩` with `t ≤ |s|`. It needs no `|x|` term in its total-time clause.
- **The top's input.** The top's tail is exactly `hBF`'s input (`ed_query_top`; the statement's negated `AcceptsWithin` at `1^{ℓᵢ+1}` and `budget f ℓᵢ`).
- **Silence.** Every phase of `Q` can stay silent, so the run's output is `[]` at its verdict:
  - the calls end at `Cfg.ofWords …` with output `[]`;
  - the rows emit nothing;
  - `qyEmitTM` runs under `embedSilentTM`;
  - the clock's host output is the body's, and `vhostSilentTM` is silent.
- **Normalization.** `computesFunInTime_lengthBits` through the **install** call (`exists_installCallTM`, the argument a work-tape word) is the right normalization of `1^b` to `bits b`. Its axioms are the standard three: it comes from `timeConstructible_id`, not from the sorried `lengthBitsTM_computes`.
- **The uniform `T` and `K`.** `T = O(g n + 1)` on every stream:
  - `w_b`'s value is at most `2^L − 1 ≤ 2 g n` (`qy_two_pow_bits_le`);
  - every call is linear in `g n + 1`;
  - the clock bounds both simulators by `5 g n + 2L + 2`;
  - `b = 0` and the off-stage inputs (`query = []`) are immediate.

  So `K = P₀ + P₁ + 15` is uniform (`ed_time`).
- **The per-code constant.** `C = max 1 (max C_R C_BF)` works:
  - `C ≥ 1` gives `t' < g n`, so `bits t'` fits width `L` (`ed_width`, `ed_padded_value`);
  - `C ≥ C_R` puts the core inside the allowance;
  - `C ≥ C_BF` and `n ≤ g n` put `BF` inside the allowance.
- **Middle soundness.** It needs the clock's first stop to be the core's first verdict. It is: a halt before `T` would contradict `state = some accept/reject` at `T`. `t = b ≤ g n = |s|` is ensured by the test.

**What does not hold.**
- **(F1) No published row can split a contiguous word**, and the route splits two:
  - **the guessed block**, into the stream and `w_b`;
  - **the query word**, into its flag and its tail.

  Every framed row that reads a word from a head requires blanks at relative positions `−1` and `|w|`:

  ```lean
  -- copyMapTM_run_ofCfg (Catalog.lean 1315), transferMapTM_run_ofCfg (1260), clearTM_run_ofCfg (1523)
  (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
    d.workTapes src (d.workTapePos src + p) = FinTM.bufferTape w p)
  -- expandTM_run_ofCfg's counter (CounterLoop.lean 1652-1656), the step clock's (StepClock.lean 1104)
  (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape w p)
  ```

  The guessed block is nonblank throughout:

  ```lean
  (hblock : ∀ p : ℕ, p < m → cP.workTapes j (cP.workTapePos j + p) ≠ none)   -- NDHost.lean 1230
  ```

  So `w_b`'s left neighbour (cell `g n − 1`) is a stream bit. "Copy `w_b` off the block and clear its cells (the copy and clear rows)" (draft 139) cannot be done by those rows. `rv_no_left_delim` proves that the hypothesis fails at `p = −1` whenever `s ≠ []`.

  Likewise the query tape holds `bufferTape (flag :: tail)` (the input call's endpoint). Yet `vhostSilentTM`'s buffer must be exactly the buffer of its word:

  ```lean
  workTapes := Fin.addCases (fun _ => FinTM.bufferTape y) c.workTapes   -- VirtualInput.lean 139
  ```

  So `BF` cannot run "on the query word's tail" in place (draft 151-152), and an install call's argument must be at cell `0` too. No published row writes a single blank: `writeConstTM` writes only `some (some w₀[j])` (Scan.lean 136).

  I checked the function-level detours:
  - `computesFunInTime_unaryToken` (sorry-free) splits `false :: tail` but not `true :: tail`, since the top's tail may start with `true`;
  - `computesFunInTime_splitSolve(With)` costs `c (n + 1)^(e + 2)`, resp. `c (n + 1)(TE (n + 1) + n + 2)`, which is superlinear.

  **This is a genuine gap.** The draft's "from published rows and E-Q's leaves, with no new leaf" is false.

  **Smallest fix, a decision for the maintainer.**
  - **(a) Extend the draft's own one-step flag leaf** into `dzTakeTM`: read the cell, write a blank, step right, enter `got o`. Its step lemma is its own, because `qy_step` covers only steps that write nothing. Use it three times:
    1. on the flag, which makes the tail left-delimited, so `copyMapTM_run_ofCfg` copies the tail to a fresh buffer at cell `0`;
    2. on a **separator cell** that `P` adds to the block (`m = g n + 1 + L`, still `≤ 2 (g n + 1)` by `length_bits_le_self`, so `K` and the route probe are unchanged);
    3. to read the top's captured bit after a rewind.

    The block is reached by published rows:
    - `skipBackTM_run_ofCfg` over the empty word moves tape `j`'s head from `0` to `−1` (`rv_skipBack_empty`);
    - `walkTM_run_ofCfg` with a ruler `1^{g n}` (built by `qy_expandHost` in `P`) carries it to the separator, cell `g n` (`rv_walk_to_boundary`);
    - after the blank, `transferMapTM_run_ofCfg` moves the now-delimited `w_b` to a fresh tape and blanks it, leaving tape `j` exactly `bufferTape s`;
    - `skipBackTM_run_ofCfg` over `s` returns the head to `0`.

    The core then finds its stream tape as `exists_ndInterpreterCore` demands.
  - **(b) Commission a public framed "take one cell" row** (read, write blank, step right) in the next shared-file window, and issue E-D after it lands.

  The diff implements (a), marked ⟨the maintainer's decision, review F1⟩.
- **(F2) `α`:** "one hosted call of the second-component extractor on the query word's tail" (draft 143-144) yields `1^{n+1}`, not `α`:

  ```lean
  theorem pairExtractTM_snd : (pairExtractTM false true).ComputesFunInTime
    (fun x => ((pairDecode x).map Prod.snd).getD []) (fun n => 5 * (n + 1))   -- Primitives.lean 1025
  ```

  The route note's machine, `prefixCanonTM (pairExtractTM false true)`, is published only as a native-input run that halts (`prefixCanon_pairExtract_halt`, InterpreterStartup.lean 91-98: `d.state = none ∧ d.output = …`). That is neither a phase (a halt ends the host) nor an argument of a call.

  The published route is one **install call** of the composite `FinTM.computesFunInTime_comp FinTM.pairExtractTM_fst FinTM.pairExtractTM_snd`, linear, on the tail's buffer. `rv_alpha_row` and `rv_alpha_value` prove it, through `pairDecode_pairEncode`.
- **(F4) The hosted runs.**
  - `vhostSilentTM M : MultiTapeTM ((1 + m) + 1) Bool (S × Bool)` (VirtualInput.lean 185), and the clock adds one more tape (`H : MultiTapeTM (k + 1) Γ Q`, StepClock.lean 1098). So "the step clock over `vhostSilentTM R`" is a phase of `Q` only after an **embedding into `D`'s `k` tapes**: `embedEmitTM` (E-Q's `qy_embed`), with a tape plan the draft never states.
  - The plan:
    - the core's stream bank tape goes to tape `j` (`bufferTape s`, head `0`);
    - the virtual buffer goes to the capture tape of the three emissions, rewound to `0` (the buffer head is `inputPos − 1 = 0`);
    - the core's other tapes and `vhostCap` go to blank tapes;
    - the counter goes to a copy of `bits (g n)`.
  - Both runs are the same composition, so they should be **one** generic private lemma, not two copies.
- **(F5) `1^{n+1}`** has no source in `P`. The published `computesFunInTime_prepend [true]` through an input call gives it (`rv_tail_ones`).
- **(F6) The core's input word** is `qy_writer_word` without its flag. It follows in one step (`rv_core_word`, proved in the overlay copy: `W := α ++ [true]`, `List.dropLast_concat`, `List.cons.inj`), so no second word lemma is needed.

**P can leave the block where both consumers need it**, once F1 is fixed. `P` builds `1^{g n} ++ [true] ++ bits (g n)` on a fresh tape `j` with E-Q's wrappers (`qy_expandHost` twice, the second with the counter `[true]` from `qy_writeConst`; then `qy_copy`; then `qy_rewind`). That gives the head at `0`, blank at `−1` and at `m`, which is `guessRunTM`'s setup. After `Q`'s split, tape `j` is `bufferTape s` with its head at `0`, which is the core's start, with `t = b ≤ g n = |s|`. Without the split no row can produce that tape.

**Edge cases.**
- The draft's list is right.
- It misses `g n = 0`, possible only at `n = 0`, which matters for the all-input halting clause (F12). With the separator, the block is one cell, the ruler and the counters are empty, and the walk moves one cell.
- The top's reader may read only cell `0`. Under the top's premise `BF` halts inside the allowance with exactly `[true]` or `[false]`, and halting needs only some verdict.

## (c) Standards and precedent

- **Regions (a)-(d)** are sufficient and minimal for the route as fixed: `dzTakeTM` and every other new private live in (b).
  - The maintainer's landing item, gate 87's finding 2 (`qy_call_bound`'s local `hb`, file 451-461), is correctly outside them. `qy_call_bound` is frozen under rule 2 (F15).
  - Region (d)'s wording leaves unclear who edits the labels (F14).
- **Rule 10.** The discipline is right, but the self-check is under-specified against the precedent (F8):
  - the seal floor is "at least the route probe's 11", none of them a machine-level definition;
  - E-Q cont1's rule 10 listed the readings (`clockCfg_*`, `wordPatch_*`, the R1 transports, `counter_cfg_eq`, `seamReleaseTM_runFrom_pos`, `Cfg.ofWords`/`stateWord`) and a seal floor of about 30 definitions. E-D's code reaches all of those, plus the `vhost*`, `guessRun*`, `walkTM`, `transferMapTM`, `skipBackTM` and `FinTM.VirtualTag` definitions.
- **Rule 11.**
  - The prefix `dz_`/`Dz` is unused in the tree (grep: none).
  - The precedent's sentence on `deriving` for a `private inductive` is missing. Lean names those instances publicly (`workflow.md` §4, counting public names), and E-D's phase types will derive them (F8).
- **Public-facing docstrings:** the rule is stated for new text. Rewriting the existing campaign references in the target's docstring is the deferred cleanup's job, which is consistent (F14).
- **Checkpoints** are sound. With F1 the split belongs to checkpoint 3 and `dzTakeTM` to checkpoint 2 (diff).
- **Duplication.**
  - The population (38 files) covers every file the fixed route cites: `Build/Catalog` (walk, skip-back, transfer), `Composition` (the composite), `Primitives` (the extractors, prepend), `Build/Scan`, `Build/Embed`, `Build/VirtualInput`, `NDHost`, `NDCodeSimulator`.
  - The known hazards are right.
  - Missing: E-Q's own normal-form wrappers by name, with their origin-only preconditions (F3), and the one-lemma rule for the two hosted runs (F4).
- **Environment (addendum v2.6)** is consistent: single fill, Parts 1-2, one-Lean and no-stop rules, roots-only cache, bootstrap logging. The precedent's measured budget for a 4-CPU Claude host and its E-SERIAL sentence are missing (F13).
- **The cited list.** `EDImportProbe` checks the 59 names the draft lists. It does not cover the names the route needs beyond them (F9). The precedent told the agent to extend a copy of the probe; the draft does not.

## (d) Findings

| # | Severity | Where (draft at 615e56b4) | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|
| F1 | **blocker** (decision for the maintainer) | Hosts, `Q` 2 and 4 (138-152); route note revision | The binding route needs two splits of contiguous words: the guessed block into `s` and `w_b`, and the query into its flag and tail. No published row does either. The copy, transfer and clear rows and both counters require a blank at relative position `−1`. The block is nonblank by `hblock`. `vhostSilentTM`'s buffer must be exactly `bufferTape` of the tail, and no row writes a single blank. "From published rows and E-Q's leaves, with no new leaf" is false | Catalog.lean 1260/1315/1523, CounterLoop.lean 1652-1656, StepClock.lean 1104, NDHost.lean 1230, VirtualInput.lean 139, Scan.lean 136; `rv_no_left_delim`, `rv_flag_no_left_delim` (out/RVRouteRows.out). `unaryToken` fails the top; `splitSolve(With)` is superlinear | **Decision.** (a) Extend the licensed one-step flag leaf to `dzTakeTM` (read, blank, step right) and use it on the flag, on a separator cell that `P` adds to the block, and on the top's captured bit. Reach the separator by `skipBackTM` over `[]` and `walkTM` with a ruler `1^{g n}` (`rv_skipBack_empty`, `rv_walk_to_boundary`), then `transferMapTM` and `skipBackTM`. Or (b) commission a public framed take-one-cell row first. The diff implements (a) |
| F2 | major | `Q` 2 (143-144); cited rows (213) | "The second-component extractor on the query word's tail" outputs `1^{n+1}`, not `α`. The route note's `prefixCanonTM` form is a halting native-input run, neither a phase nor a call argument | Primitives.lean 1025-1027; InterpreterStartup.lean 91-98 | An install call of `computesFunInTime_comp pairExtractTM_fst pairExtractTM_snd` on the tail's buffer (`rv_alpha_row`, `rv_alpha_value`). Name both rows and `pairDecode_pairEncode` |
| F3 | major | 24-27, 99-102, cited list (194-219), rule 7, hazards (292-293) | E-Q's normal-form wrappers, the very rows `P` and `Q` are built from, are not named: `qyC`, `qy_step`, `qy_hosted*`, `qy_copy`, `qy_copy_over`, `qy_transfer`, `qy_clear`, `qy_writeConst`, `qy_rewind`, `qy_embed*`, `qy_call`, `qy_callHost`, `QySpec`, `QyInSpec`, `qy_installSpec`, `qy_inputSpec`, `qy_expandHost`, `qy_emit_stop`/`_halt`, `qy_bits_val`, `qy_blank_bank`, `qy_arg_bank`. A fresh agent would re-derive them, which makes same-file copies. Their preconditions put the word at cell `0` under a head at `0` (`hsrc : T src = FinTM.bufferTape w`, `hPs : P src = 0`), so the off-origin steps (the tail at cell `1`, `w_b` at `g n + 1`) must use the framed rows directly. The draft does not say so | NTimeDiagonalizer.lean 493-999, 1932-2165; 658/693/726 for the preconditions; all on the standard axioms (out/RVOverlayAx.out) | List them in the cited infrastructure with the origin caveat. Extend rule 7 ("a second … normal-form wrapper is a copy") |
| F4 | major | `Q` 3-4 (148-153); hosts list (205-207); checkpoint 5; pitfall (337-339) | The clocked, hosted runs live on `((1 + K) + 1) + 1` tapes, so they enter `Q` only through an embedding into `D`'s tapes. The draft names neither the embedding (`embedEmitTM`, `qy_embed`) nor the tape plan the core's start forces: the stream bank on tape `j` as `bufferTape s` at head `0`, the virtual buffer on the rewound capture tape, everything else blank. Two runs of one composition invite two copies | VirtualInput.lean 185; StepClock.lean 1098; NDCodeSimulator.lean 901 | State the embedding and the plan. Require one generic private lemma for the clocked, hosted run (generic in the machine and its stop set), used twice. It composes two registered hosts, so it is no new host, and it is a promotion candidate |
| F5 | minor | `Q` 2's third emission (146); `P` (130-134) | `1^{n+1}` must be a work-tape word for `qyEmitTM` (`hT : T i = FinTM.bufferTape w`), and nothing in `P` or `Q` produces it | Primitives.lean 2333; `rv_tail_ones` | `P`: an input call of `FinTM.computesFunInTime_prepend [true]` |
| F6 | minor | 27; `Q` 2 (144-147) | The core's input is `qy_writer_word`'s word without the flag. The draft does not say how to get it from `qy_writer_word`, so a second word lemma is likely, and that is a same-file copy | `rv_core_word` (out/RVOverlayAx.out, `[propext]`) | "take `W := α ++ [true]` and cancel the flag: no second word lemma" |
| F7 | minor | `Q` 4 (152-153) | After `BF` halts, the captured `[b]` sits on `vhostCap` with its head after it (`embedSilentCfg_cap`: head at `(pre ++ c.output).length`). "Read the captured bit" is no one-step read at that head | Embed.lean 222, 1025-1032 | Rewind it (`qy_rewind`) and read cell `0` with `dzTakeTM`: `false` → `acc`, else `rej`. Under the premise the word is exactly `[true]` or `[false]` |
| F8 | minor | Rule 10 (254-263); rule 11 (264-266) | The seal floor (the probe's 11) and the readings fall well short of E-Q cont1's rule 10, which the draft only references ("as in E-Q's briefs"). The `deriving`-instance sentence of cont1's rule 11 is dropped | cont1 brief rules 10-11; `workflow.md` §4 | Carry the readings and an extended floor (the probe's 11 and 32 more, listed in the diff) into rule 10, and the instance-name check into rule 11 |
| F9 | minor | Cited infrastructure (194-219) | The route needs published names beyond the 59: `walkTM_run_ofCfg`, `embedEmitTM`/`_runFrom`/`embedEmitCfg_eq`, the `vhostCfg_*`/`vhostSilentCfg_eq`/`vhostBuffer_eq`/`vhostBank_eq`/`vhostCap_eq` fields, `FinTM.VirtualTag_iff`, `embedSilentCfg_cap`/`_selected_*`/`_unselected`, `clockCfg_*`, `wordPatch_*`, `Cfg.stopped_iff`, `seamReleaseTM_runFrom_pos`, `computesFunInTime_comp`, `pairExtractTM_fst`/`_snd`, `pairDecode_pairEncode`, `computesFunInTime_prepend`, `phaseHostTM_run(_le)`, `phaseHostTM_q₀`, `initCfg_ofWords`. `FinTM.pairExtractTM` alone and `clearTM_run_ofCfg` are no longer used. Nothing tells the agent to extend the import probe | All resolve, on the standard axioms (out/RVRouteRows.out) | Add them, and add "extend a copy of the import probe by every name you cite beyond it, and run it" |
| F10 | minor | Header (3-5) | "PR #176's head `cecd76a0`" is stale. The PR head was `029f3aa9` at the pre-ship (the tree the pre-ship used) and is `f69b86b9` now (`origin/lean/eq-cont1-landing`). The owned blob `852931eb…` is the same at all three | `git rev-parse` (method) | Name the blob and the three commits (diff). At issue the blob placeholder is `852931eb9347377fcd2e4e3c1e754462b236c1ad` if #176 lands unchanged; re-check then |
| F11 | minor | Lint (308) | The "base" lint figures come from the overlay commit: 5,435 lines vs 5,432 at the base. The counts agree | out/lint-base-Diagonalization.txt vs the pre-ship's | Say "the file is 5,432 lines at the base and 5,435 with the overlay". Add the precedent's no-new-line-over-100 and size-WARN sentence |
| F12 | minor | Edge cases (181-185) | `g n = 0` (only at `n = 0`) is missing, although the halting clause covers every input: the block is the separator alone, the ruler and counters are empty and the clock's allowance is `0` | `TimeConstructible` gives only `n ≤ g n` | Add it (diff) |
| F13 | minor | Environment (295-309); pitfalls (332-342) | Several precedent items that bind E-D are missing:<br>• the 4-CPU Claude host's budget (bootstrap about 20 min, screens 2-3× the base);<br>• the E-SERIAL sentence;<br>• the install call's start (`Cfg.ofWords … (stateWord C.k arg)`, input head `1`);<br>• `P`'s start through `phaseHostTM_q₀`/`initCfg_ofWords` (the host's lemmas take `P.runFrom (P.initCfg z)`);<br>• existential times fixed before the ledger;<br>• the two-delimiter lesson of F1;<br>• `vhostSilentTM`'s exact buffer.<br>Also, `FinTM.lengthBitsTM_computes` carries `sorryAx`, so the agent must cite `computesFunInTime_lengthBits` | cont1 brief 635-750; out/RVSorriedRows.out | Add them (diff, "Known pitfalls", including the sorried-row warning) |
| F14 | note | Region (d) (114-117) | "Rewrite them …; the maintainer lands it" can be read as the maintainer rewriting the labels. Other campaign references stay in the target's docstring: "C1's design §2.5", "§3.6, the fallback", "Fill obligations, named". The deferred cleanup covers them | file 5346-5405 | "Rewrite those labels in place … (the docstring's other campaign references belong to the deferred cleanup)" |
| F15 | note | 8-10 | The landing item (gate 87 finding 2) is correctly the maintainer's and outside the fill's regions. `qy_call_bound`'s local `hb` (451-461) does re-derive `length_bits_le_self` | file 451-461 | none |
| F16 | note | 289-291 | The later revision `ae0011e5` fills the screen base (2,241 declarations, 2,439 pairs). The diff avoids those lines, applies there too, and leaves exactly that line different | out/applycheck.txt | none |
| F17 | note | 82-83 | `NTimeHierarchy` cites more of the file than "the target's statement": `ladder`, `budget`, `stage`, `stageCode_frequently`, `acceptLang_mem_NTIME` and others. All are public and frozen, so the conclusion stands | grep of NTimeHierarchy.lean | Optional: "cites only public, frozen statements" |

**Counts:** 1 blocker, 3 majors, 9 minors, 4 notes.

**Files.**
- `suggested-fix.diff` is `git diff --no-index orig/ edited/`. Apply it from the records root with `git apply -p2 --directory=campaign/fills/eq/drafts suggested-fix.diff`. It reproduces `edited/` byte for byte at `615e56b4` and applies cleanly at `ae0011e5` (out/applycheck.txt).
- `edited/` (SHA-256 `607e741f…`) still carries the draft's issue-time ⟨…⟩ items, plus two new ones:
  - the F1 decision marker;
  - the staging of `probe/RVRouteRows.lean` and `probe/RVOverlayAx.lean` (the appendix alone is `probe/RVOverlayAx.appendix.lean`) as this round's inputs, if the maintainer adopts them.
