# Gate 43 review: PR #124, the seam layout's contract (`Build/SeamLayout`) (FAIL 0/2/1/7)

Reviewer: read-only review sub-agent, 2026-10-17. `$S` is the scratchpad; `$G = $S/review/gate43`.

**Inputs:**
- Findings `audits/seam-layout-statements-findings.md` (`$S/wt-hk`), read as data. SHA-256 `ca645e1b…e114`; equal to the
  blob committed at `a5128d97`.
- Bundle `infra_local/gate-dispatches/43-seam-layout-statements-gate/seam-layout-statements-bundle.md`: `shasum -c SHA256SUMS`
  OK for the bundle (`1ab146c0…4385`) and the README.
- The PR head `lean/seam-layout` at `0355da56` (`$S/wt-seam`, read only). The module's blob is `58263b1d`; the facade's is `55348438`.
- The pack, the C1-R review's G2, the round-1 consumer probe, and the consumers' statements: `StepBlock.Rep`/`Rep_iff`/`summaryCells`,
  `exists_selfStartupTMK`, `exists_ndInterpreterCore`, `embedSilentRetTM_run`/`embedSilentCfg`/`embedSilentCfg_cap`, H1
  (`exists_uniformSimulator`), and the catalog rows.
- The U2-S delivery's `REPORT.md` (`$S/incoming/u2s-startup/`), read only for its split. **It built no split**: "No leaf or
  reusable redistribution lemma was completed", and phases 3–4 are not implemented. Its proved prefix contract ends where
  round 2 starts: the capture tape holds `serializeK` with its head one past it, at a suffix-uniform time `N(α)`.
- My worktree `$G/wt`: detached at `0355da56`, with the Mathlib link and the round-2 patch applied. Elaborations ran one at a time
  through `leanelab.sh` against `$S/oleans-lc1w` (the snapshot below #124).

**Ready to commit to `lean/seam-layout` (#124 round 2): `$G/r2-seamlayout.patch`** (SHA-256 `7d53196e…3a51`). It changes one
file, `Build/SeamLayout.lean`: the contract's statement (the time's quantifier order) and its docstring (the sketch). The contract
stays sorried. Edit script: `$G/scripts/r2_seamlayout.py`; it asserts both anchors are unique and every line is ≤ 100
characters.

**#124: not yet clear to merge.** The statement changes, so round 2 needs the PR commit, the 2-module replay and its own statement gate.

## (a) The findings at the head

| # | Auditor | Mine | Evidence (at `0355da56`) |
|---|---|---|---|
| 1 | major | **true, major** | I reproduced the counterexamples with the rows' actual tables (`out/sim-finding1.txt`). (i) On `s = [F,T,F]`, `skipBackTM` from head `3`, then one step right, ends at `1`. From head `0` alone it ends at `-1`. The contract's hypothesis ("the word ends one blank before the head") holds at **no** head in `[0, \|s\|]`, since `s` has no inner blank. (ii) `copyTM` from the start of `v` (cell `3`, after the terminator `some false`) returns the heads to `0` and `-3`, for `v = []` and for `v = [true]`. (iii) `clearTM` and `copyTM` already restore their heads, and skip-back over the summary word lands at `2`. So "rewind", "then one step right" and "then rewind" are each wrong. A sketch that does not compose its cited contracts is graded major, as in gate 39. |
| 2 | major | **true, major** | In round 1, `∃ T ≤ C·(\|s\|+1)` sits after `∀ {z} (d …)`, so `T` may depend on the native input. The auditor's padding is valid: a fresh pre-entry state reads the input symbol and takes one or two stationary silent steps before an input-independent route. Every round-1 clause holds with `C + 2`, and the exact first-exit time then varies with the input. U2-S needs `∀ α, ∃ T B, ∀ w`, an **exact** first exit (`UniversalK.lean:188–201`). A bound cannot be padded to a common time without knowing the machine. Not a blocker: nothing builds on the contract yet, and R and H1 need only the bound. |
| 3 | minor | **true, minor** | The probe's inline contract equals the module's lines 66–88 (`diff`: identical). But neither example invokes it: they prove `serializeK_eq`/`unaryFin_eq` and the shifted-summary identity. Cell `0` uses a local `bufferTape_of_neg'` that unfolds `FinTM.bufferTape`. #122's `Turing.FinTM.bufferTape_of_neg` (`Simulation.lean:655`) is in `oleans-lc1w`; my probe cites it. The PR body ("derives both … using #122's `FinTM.bufferTape_of_neg`") and the pack ("derives both, reading … through #122's") overstate it. |
| 4 | note | agree | Bundle SHA-256 verified locally; head `0355da56`; one commit, two files. |
| 5 | note | agree (truth) | The literal statement is true. Round 2 uses a different, shorter route than the auditor's (below), checked separately. |
| 6 | note | agree | Confirmed in Lean by my probe's examples 2–4 (U2-S's tapes `k`/`k + 1`; R's `Rep` fields from the R1′ endpoint). |
| 7 | note | agree | Non-vacuity holds in Lean: probe example 5 builds a start configuration for every word, head start and input. |
| 8 | note | agree | Import closure computed from the sources: 17 TCSlib modules including the module, none of `StepBlock`, `CodeSimulator`, `UniversalK`, `NDCodeSimulator`. |
| 9 | note | agree | Records only. |
| 10 | note | agree; **baseline reproduced** | `campaign_style_lint.py TCSlib/Complexity/TuringMachine`: base and round 2 both `0 FAIL, 63 WARN over 80 files`, identical except the module's INFO row (90 → 120 lines). |

## (b) The round-2 repair

### What changes, and why

- **Statement (finding 2).** `T` is now chosen after the word data and the source head's start `r : ℕ`, and **before** the
  configuration (`∀ {z} (d …)`). The head hypothesis `0 ≤ pos ≤ |s|` becomes `r ≤ |s|` (bound before `T`) plus `pos = r`
  (in the configuration). The domain is the same; only the time's dependence is restricted. Everything else is verbatim: the
  start's tape hypotheses, the endpoint, the output and first-exit clauses.
- **Sketch (finding 1).** It is replaced by eight phases. Each is an exact `_run_ofCfg` contract or one of two named leaves, and
  each states the precondition the previous phase's endpoint meets. The exact time is given.
- I did not put an explicit time formula in the statement. That would freeze the construction for no consumer's benefit.

### The exact Lean text (replaces lines 36–88 at `0355da56`)

```lean
/-- **The seam layout from a captured serialization.** For distinct work tapes `src`, `tbl` and
`sm` there is a machine with an entry state `entry`, a live exit `done` and a constant `C` with
the following property. Let `s = pairEncode a ((List.replicate q true ++ [false]) ++ v)` and let
`r ≤ |s|`. There is **one time** `T ≤ C·(|s| + 1)`, depending on `a`, `v`, `q` and `r` only
(chosen before the native input and every other tape), such that: started at `entry` with tape
`src` holding exactly `s` from cell `0` (blank elsewhere), its head at `r`, and tapes `tbl` and
`sm` blank with their heads at `0`, the machine reaches `done` at `T`, and not before, with
* tape `tbl` holding exactly `v` from cell `0`;
* tape `sm` holding exactly the unary word `List.replicate q true ++ [false]` from cell `2`
  (cells `0` and `1` blank);
* tape `src` blank;
* the heads of the three tapes at `0`, and every other tape, head, the input position and the
  output unchanged; it emits nothing.

**Why `T` comes before the configuration.** U2-S (`Turing.exists_selfStartupTMK`) must exit first
at a time that does not depend on its input's suffix (the statement gate, finding 2). R and H1
need only the bound, and the form with `T` chosen per configuration is a corollary.

At `a = n.bits`, `q = M.q₀` and `v = tableBitsK M.tr`, the start word is `serializeK M`
(`Turing.serializeK_eq`, `Turing.unaryFin_eq`), and the end is the step block's table and summary
tapes for an empty output (`Turing.StepBlock.summaryCells_eq`,
`Turing.StepBlock.outputSummary_nil`, `Turing.FinTM.bufferTape_of_neg`). (A row of the
construction layer; [AB09, §1.4].)

**Proof sketch.** Write `m = List.replicate q true ++ [false]` and `h = 2|a| + 2` for the length
of the header `pairEncode a []`. So `s` is the header on `[0, h)`, `m` on `[h, h + q]` and `v`
from `h + q + 1`, and `n = |s| = h + q + 1 + |v|`. Eight phases are composed by
`Turing.phaseHostTM` (`Turing.phaseHostTM_run`: one silent stationary dispatch step between
consecutive phases). Each is a catalog row through its `_run_ofCfg` contract, whose hypothesis
the previous phase's endpoint meets, or one of two leaves:
1. `Turing.skipTM_run_ofCfg` on `src` at `w = s.drop r`: the cells `r, …, n` are `s.drop r` and
   its right blank. `n - r + 1` steps; the head ends at `n + 1`.
2. `Turing.skipBackTM_run_ofCfg` on `src` at `u = s`: the cells `-1, …, n` are `s` between two
   blanks, ending one blank before the head. `n + 3` steps; the head ends at `0`.
3. **Leaf `pairSkip`** (read-only on `src`): from cell `0` of `pairEncode a _`, read aligned pairs.
   An equal pair continues; `false, true` exits one cell past it. `h` steps; the head ends at `h`.
   No row serves it: the seek rows stop at blanks and none reads pairs.
4. **Leaf `unarySplit`** (on `src` and `sm`): move the head of `sm` right twice. Then, while `src`
   reads `true`, write `true` on `sm` and move both heads right. At the `false`, write `false` on
   `sm` (its head stays) and blank that cell of `src` (its head moves right). `q + 3` steps. Now
   `src` has its head at `h + q + 1` and a blank at `h + q`, and `sm` holds `m` from cell `2`,
   its head at `q + 2`. No row serves it: the copy row stops at a blank, not at a `false`.
5. `Turing.walkTM_run_ofCfg` with ruler `sm`, `moved = (· = sm)` and `dir = .neg`, at
   `w = m.reverse`: the cells `q + 2, …, 2` read leftward, then the blank cell `1`. `q + 2`
   steps; the head of `sm` ends at `0`.
6. `Turing.transferTM_run_ofCfg` from `src` to `tbl` at `w = v`: phase 4's blank at relative
   `-1`, then `v`, then the right blank at relative `|v|`. `2|v| + 2` steps. `tbl` becomes
   `bufferTape v` (it was blank), `v` is erased from `src`, and both heads return, to `h + q + 1`
   and `0`.
7. `Turing.skipBackTM_run_ofCfg` on `src` at `u = s.take (h + q)`: all that remains on `src`,
   ending one blank before the head. `h + q + 3` steps; the head ends at `0`.
8. `Turing.clearTM_run_ofCfg` on `src` at `w = s.take (h + q)`. `2(h + q) + 2` steps; `src` is
   blank and the row returns its head to `0`. This row's `done` is the exit `done`.

In all, with the seven dispatch steps, `T = 2n - r + 4h + 5q + 2|v| + 23 ≤ 7n + 18 ≤ 18(n + 1)`,
a function of `a`, `v`, `q` and `r`: no phase reads the native input or a tape other than `src`,
`tbl` and `sm`, so the run on those three tapes, and hence `T`, is the same for every frame.
Fill obligations, named: the two leaves' framed contracts; the word identities for `s.drop r`,
`s.take (h + q)` and the cells of `m` and `v` (from `Turing.pairEncode_eq`); the phase joins;
and the endpoint's frame. -/
theorem exists_seamLayoutTM (k : ℕ) (src tbl sm : Fin k) (hst : src ≠ tbl) (hss : src ≠ sm)
    (hts : tbl ≠ sm) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (L : MultiTapeTM k Bool Q)
      (entry done : Q) (C : ℕ),
      ∀ (a v : List Bool) (q r : ℕ),
        let s := pairEncode a ((List.replicate q true ++ [false]) ++ v)
        r ≤ s.length →
        ∃ T ≤ C * (s.length + 1), ∀ {z : List Bool} (d : Cfg k Bool Q z),
          d.state = some entry →
          d.workTapes src = FinTM.bufferTape s → d.workTapePos src = r →
          d.workTapes tbl = (fun _ => none) → d.workTapePos tbl = 0 →
          d.workTapes sm = (fun _ => none) → d.workTapePos sm = 0 →
          (L.runFrom d T).state = some done ∧
          (L.runFrom d T).inputPos = d.inputPos ∧
          (L.runFrom d T).workTapes =
            Function.update (Function.update (Function.update d.workTapes src (fun _ => none))
              tbl (FinTM.bufferTape v))
              sm (fun p => FinTM.bufferTape (List.replicate q true ++ [false]) (p - 2)) ∧
          (L.runFrom d T).workTapePos =
            Function.update (Function.update (Function.update d.workTapePos src 0) tbl 0) sm 0 ∧
          (∀ u ≤ T, (L.runFrom d u).output = d.output) ∧
          ∀ u < T, (L.runFrom d u).state ≠ some done := by
  sorry
```

### The phases and their joins

Write `m = 1^q 0`, `h = 2|a| + 2` and `n = |s| = h + q + 1 + |v|`. The header is on `[0, h)`, `m` on `[h, h + q]`, and `v` from
`h + q + 1`. The start has `src = bufferTape s` with its head at `r`, and `tbl`, `sm` blank at `0`.

| # | Row / leaf | Hypothesis, and why it holds | Steps | End |
|---|---|---|---|---|
| 1 | `skipTM_run_ofCfg src (s.drop r)` | cells `r + p` for `p ∈ [0, n − r]` are `bufferTape (s.drop r) p` (start tape) | `n − r + 1` | src head `n + 1` |
| 2 | `skipBackTM_run_ofCfg src s` | cells `p ∈ [−1, n]` are `bufferTape s p`; `(n+1) − n − 1 = 0` | `n + 3` | src head `0` |
| 3 | leaf `pairSkip` (read-only) | from cell `0` of `pairEncode a _`; the aligned pairs are `bb`, then `01` | `h` | src head `h` |
| 4 | leaf `unarySplit` (src, sm) | src from `h` reads `1^q 0 …`; sm is blank | `q + 3` | src head `h + q + 1`, cell `h + q` blanked; sm holds `m` from `2`, head `q + 2` |
| 5 | `walkTM_run_ofCfg sm (· = sm) .neg m.reverse` | sm cells `q + 2 − p` are `bufferTape m.reverse p` for `p ≤ q + 1` (cell `1` blank) | `q + 2` | sm head `0` |
| 6 | `transferTM_run_ofCfg src tbl v` | src relative `−1` is phase 4's blank, then `v`, and relative `\|v\|` is cell `n`, blank | `2\|v\| + 2` | `tbl = bufferTape v` (it was blank), `v` erased, heads `h + q + 1` and `0` |
| 7 | `skipBackTM_run_ofCfg src (s.take (h+q))` | src is exactly `bufferTape (s.take (h+q))` and the head is at `h + q + 1`, one blank past the word | `h + q + 3` | src head `0` |
| 8 | `clearTM_run_ofCfg src (s.take (h+q))` | blank at `−1`, the word, blank at `h + q` | `2(h+q) + 2` | src blank, head `0` (exit) |

With 7 dispatch steps (`phaseHostTM_run`), `T = 2n − r + 4h + 5q + 2|v| + 23 ≤ 7n + 18 ≤ 18(n + 1)`.

- **Why `T` depends only on `(a, v, q, r)`.** Every row's table has the shape `fun q _ w`: it ignores the input symbol and reads
  only its own tapes. The leaves read only `src`, and the dispatch is unconditional. So the run on the three tapes is fixed by the
  start word and `r`, and every other tape, head, the input position and the output are untouched.
- **What the round-2 route drops from round 1.** No rewind follows copy or clear (they return their heads). There is no
  skip-back from inside the word. `transferTM` replaces "copy, then clear `v`" (the pair `copyTM_run_ofCfg` + `clearTM_run_ofCfg`
  at `v` is equivalent, at `+2|v| + 3` steps, if the fill prefers it). `sm` is rewound by the walk row with its own word as the ruler.
- **The leaves, honestly.** `pairSkip` exists because no row reads aligned pairs; the seek rows stop at blanks. `unarySplit` exists
  because the copy row stops at a blank, not at a `false`. Each is a finite controller of at most four states. Both are fill
  obligations with framed contracts.
- **Case checks** (`out/sim-route.txt`, `out/sim-contracts.txt`; scripts in `$G/scripts`). The simulations use the rows' tables
  transcribed from `Build/Catalog.lean`, the leaves as specified and `phaseHostTM`'s dispatch. At every phase start the cited
  contract's hypothesis is checked literally, and each phase's time and endpoint are checked against the contract.
  - All binary `a`, `v` of length ≤ 3, `q ≤ 4` and every `r ∈ [0, |s|]`: 14,400 instances pass.
  - Length ≤ 4 and `q ≤ 6`: 110,887 instances pass.
  - The time formula is exact on every instance.
  - These are finite checks, not kernel proofs.

### Truth, non-vacuity, sufficiency of the round-2 statement

- **True:** by the route above; `T` is a closed formula in `(a, v, q, r)`.
- **Not vacuous:** probe example 5 constructs, for every `s`, `r`, `z` and any state type, a configuration meeting all seven
  hypotheses.
- **Sufficient** (probe `evidence-r2/SeamLayoutConsumerR2.lean.txt`, against `oleans-lc1w`; the contract inline and verbatim,
  everything else published):
  1. `seamLayout_round1`: the round-1 statement is a corollary, so R, H1 and UN lose nothing.
  2. `seamLayout_u2s`: for `E : EffectiveCodeK kk`, `∀ α, ∃ T, ∀ w (d : Cfg K Bool Q (pairEncode α w))`. The capture tape holds
     `serializeK (E.machine α)` with its head one past it. The conclusion is the exit at `T`, no earlier exit and silence, with
     `tbl = bufferTape (tableBitsK …)` and `sm = fun p => bufferTape (unaryFin q₀) (p − 2)`, U2-S's tapes `k` and `k + 1`
     exactly. It also gives `src` blank, the three heads `0` and the input position unchanged.
  3. `seamLayout_rep_fields`: from the R1′ capture endpoint (`embedSilentCfg_cap`, `pre = []`, recorded output `serializeK M`),
     `T ≤ C·(|serializeK M| + 1)`. The end has `Rep`'s table field `bufferTape (tableBitsK M.tr)`, its summary field
     `summaryCells (outputSummary (M.initCfg x).output) (((M.initCfg x).state.map unaryFin).getD [])`, and both auxiliary heads
     at `0`. It cites #122's `FinTM.bufferTape_of_neg` (no stand-in).
  4. Those fields give `StepBlock.Rep M.tr (M.initCfg x) d` through `StepBlock.Rep_iff`.
  5. Non-vacuity, as above.

### Checks (`$G/out/`, copied with hashes to `$G/evidence-r2/`)

| Check | Result |
|---|---|
| Module elaboration (`elab-r2.out`) | exit 0; one warning, the contract's `sorry` (line 96) |
| Consumer probe (`consumer-r2.out`) | exit 0; one warning, the inline contract's `sorry`. Axioms of the three theorems: `propext`, `Quot.sound`, `Classical.choice` (not in `seamLayout_round1`) and `sorryAx`, the last only through the inline contract |
| Probe statement verbatim | the module's statement occurs exactly once in the probe (scripted check) |
| Lint (`lint-base.txt`, `lint-r2.txt`) | `0 FAIL, 63 WARN` both; no delta except the module's INFO row |
| Patch | 1 file, 55+/25−; `git apply --check` clean on `0355da56`; the module's new blob is `dc0cc110757c67adae3400d769eaeb215c63a690` (SHA-256 `bd83f02d…6ce8`) |
| Replay closure | unchanged: the module and the `TuringMachine` facade, 2 modules (not the root) |

### Records (minor 3, and round 2's evidence)

- **New evidence folder** `audits/evidence/c1/seam-layout/r2/` (non-`.lean`, straight to the campaign branch): copy
  `$G/evidence-r2/` as is (the probe as `.lean.txt`, the two `.out` files, the simulations and their outputs, the patch and the
  edit script, `SHA256SUMS`).
- **The PR body:** replace "The consumer probe (`audits/evidence/c1/seam-layout/`) derives both through published equations, using
  #122's `FinTM.bufferTape_of_neg`." with:
  > **Round 2 (gate 43).** The time `T` is chosen before the configuration (U2-S's suffix-uniform first exit; finding 2), and the
  > sketch composes eight exact `_run_ofCfg` contracts and two named leaves (finding 1). The round-1 probe only proved the two
  > identities, with a local stand-in for `bufferTape_of_neg` (finding 3). The round-2 probe (`…/seam-layout/r2/`) applies the
  > contract: it recovers the round-1 form, U2-S's code-uniform exit with its tapes `k` and `k + 1`, and, from R1′'s capture
  > endpoint (`embedSilentCfg_cap`), `Rep`'s table and summary fields for `M.initCfg x` through #122's `FinTM.bufferTape_of_neg`,
  > assembled by `Rep_iff`.

  Also, in the "What" row, change "within `C·(|s| + 1)` steps and not before" to "at one time `T ≤ C·(|s| + 1)`, depending on the
  word and the head's start only, and not before".
- **Round 1's pack** is not edited (it is the dispatched record). The round-2 pack restates the attestation from the round-2 probe.

**Commit message (draft, `lean/seam-layout`):**

```
SeamLayout round 2 (gate 43): the time before the configuration, and a composing sketch

- exists_seamLayoutTM: T is chosen after the word data and the source head's start r and before
  the configuration (U2-S's suffix-uniform first exit; finding 2); the head hypothesis becomes
  r ≤ |s| and pos = r. The round-1 form is a corollary.
- the proof sketch: eight phases, each an exact _run_ofCfg contract (skip, skip back, walk,
  transfer, skip back, clear) or a named leaf (pairSkip, unarySplit), with each join's
  hypothesis; T = 2n - r + 4h + 5q + 2|v| + 23 ≤ 18(n + 1) (finding 1).

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>
```

## (c) Effect on the stack and the consumers

- **The stack above: untouched.**
  - #125 (`wt-g4l`, `0355da56..4ab012d9`) changes only `Build/ZoneRebalance.lean`. #126 (`wt-x2`, `..5333b29b`) changes only
    `Diagonalization/NTimeDiagonalizer.lean`.
  - At both tips the module's blob is still `58263b1d` and the facade's `55348438`, so the patch applies there too and a rebase is
    conflict-free.
  - No module imports `Build/SeamLayout` except the facade, and only the root imports the facade. So #125's and #126's replayed
    modules do not depend on it, and their replay results stand.
  - Only the snapshots' two oleans (`SeamLayout`, the facade) in `oleans-lseam` and its descendants `oleans-lg4l`/`oleans-lx2` go
    stale. Refresh them with round 2's 2-module replay.
- **R** (`exists_ndInterpreterCore`) cites the contract at `r = |serializeK replayTM|` after R1′ (probe example 3). Its per-code `C`
  absorbs `18(|s| + 1)`. No route change beyond naming the round-2 form.
- **U2-S** (`exists_selfStartupTMK`): probe example 2. The in-flight delivery has no split to promote. Its proved
  `ss_capturedPrefix_run` ends exactly at round 2's start hypotheses (`r = |serializeK|`, a suffix-uniform `N(α)`), so the total
  `N(α) + T(α) + …` depends on `α` alone. Its continuation brief must name the round-2 shape (time before the configuration), as a
  private leaf or as the citation (decision 2).
- **H1** (`exists_uniformSimulator`): after `exists_installCallTM` the captured word sits at `Cfg.ofWords` heads, so `r = 0`, and
  it needs only the bound (corollary). **UN:** the bound only, as R.

## (d) Bottom line

- **The round-2 object:** `$G/r2-seamlayout.patch` (SHA-256 `7d53196e…3a51`), one file. The statement changes (the time before
  the configuration), with the new sketch. The module elaborates with only the contract's `sorry`. The round-2 probe passes and
  applies the contract for R, U2-S and H1's corollary.
- **#124: not yet clear to merge.** It needs the round-2 commit (a PR change you merge), the 2-module replay (module and facade,
  chained from `oleans-lc1w`; update the replay script's blob pin to `dc0cc110…`), and the round-2 statement gate. The gate's prompt
  asks for `seam-layout-statements-r2-findings.md`; the bundle attaches TEMPLATE, policy and workflow, the patch, the round-2 probe
  and the simulations.
- **#125, #126:** no change needed. They are clear of the patch; merge order is unchanged after #124.
- **Decisions for you:**
  1. **Accept the statement change** (the time's quantifier order; the head as `pos = r`). This is the auditor's first option and,
     I think, the minimal one. The alternative, an explicit time formula in the statement, would freeze the construction for no
     consumer.
  2. **Who proves it.** Your ruling has U2-S's private leaf promoted, but U2-S's delivery built no leaf. Either:
     - (i) U2-S's continuation writes it, as a private leaf in the round-2 shape, promoted at integration; R cites the sorried
       contract meanwhile;
     - or (ii) a standalone fill of `exists_seamLayoutTM` now, along the eight-phase sketch (two small leaves). U2-S's
       continuation would then be authorized to import `Build/SeamLayout`, which needs no cycle (finding 8).

     I lean to (ii): one proof for three consumers (ground rule 7), and no promotion churn. It is your call, since it revisits
     the ruling.
