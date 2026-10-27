"""Apply the review's recommended edits to a copy of the E-Q brief draft and its screen
population. Every replacement is asserted to match exactly once (review sub-agent, 2026-10-26)."""
import sys

draft_src, draft_dst, pop_src, pop_dst = sys.argv[1:5]

E = []  # (finding, old, new)

E.append(("F16", """<!-- DRAFT (maintainer, 2026-10-25), from `campaign/items/c1/c1e/EQ-route-design.md` and the user's
rulings on it. To fill at issue (the later of #164's and #167's landings), from the pre-ship run
there: every ⟨…⟩ (the issue commit is @ANCESTOR@; the base's Lean content; the blob; the order
list, roots and base sorry set; the screen base; the probes' counts; the lint base). Then a review
sub-agent, then issue. Remove this comment at issue. -->""",
"""<!-- DRAFT (maintainer, 2026-10-25), from `campaign/items/c1/c1e/EQ-route-design.md` and the user's
rulings on it. To fill at issue (#164 and #167 are in; the base is now also after #166 and #168,
`13120e00` or later), from the pre-ship run there: every ⟨…⟩ (the issue commit is @ANCESTOR@; the
base's Lean content; the blob; the in-flight list; the order list, roots and base sorry set, on
the eight-import overlay; the screen base on the widened population; the probes' counts; the lint
base). Stage `drafts/eq-fill-query/` as `inputs/eq-fill-query/`: the route probe citing
`Complexity.timeConstructible_iff` (stand-in removed), the import probe extended (the review's
`probe/` has both). Then issue. Remove this comment at issue. -->"""))

E.append(("F5", """    `NTimeDiagonalizerOverlay.lean.txt` (your file with the seven imports of region (a)), the""",
"""    `NTimeDiagonalizerOverlay.lean.txt` (your file with the eight imports of region (a)), the"""))

E.append(("F16", """- **Your base's Lean content is ⟨the campaign's tree after #164 and #167⟩** (@ANCESTOR@ adds""",
"""- **Your base's Lean content is ⟨the campaign's tree after #164, #166, #167 and #168⟩**
  (@ANCESTOR@ adds"""))

E.append(("F5", """- **Your first edit makes your file equal to the overlay**: `import Mathlib.Data.Nat.Log` before
  line 6, and six imports after line 8 (region (a)). **Line numbers below are the base's; the
  overlay's are 7 more** (the target at 270, overlay 277).""",
"""- **Your first edit makes your file equal to the overlay**: `import Mathlib.Data.Nat.Log` before
  line 6, and seven imports after line 8 (region (a)). **Line numbers below are the base's; the
  overlay's are 8 more** (the target at 270, overlay 278)."""))

E.append(("F16", """- **In flight, merging after your base and invisible to it:** ⟨at issue: the A+ PR
  (`Build/InterpreterStartup`, `NDCodeSimulator`), U2's landing (`UniversalK`), #166
  (`SpaceComplexity/Savitch`), #135 (chapter 7 onto `main`)⟩. Cite nothing they add.""",
"""- **In flight, merging after your base and invisible to it:** ⟨at issue: the A+ PR #169
  (`Build/InterpreterStartup`, `NDCodeSimulator`). #166 and U2's landing #168 are merged, in your
  base. #135 (chapter 7) is merged into `main`, not this branch: `ClassP/BinaryArith` is not in
  your tree⟩. Cite nothing they add."""))

E.append(("F17", """The statement and its docstring, **frozen verbatim** (lines 248–273):""",
"""The statement and its docstring are **frozen verbatim** (lines 248–273: the docstring 248–269;
the statement):"""))

E.append(("F1", """- `exists_stepClockTMVia`, `exists_installCallTM`, `exists_inputCallTM`, `computesFunInTime_cond`,
  `Round.iterate_seq` with `Round`/`round_iff`, `expandTM_run_ofCfg`, `copyMapTM_run_ofCfg`,
  `writeAdvTM_run_ofCfg`.""",
"""- `exists_stepClockTMVia`, `exists_installCallTM`, `exists_inputCallTM`, `computesFunInTime_cond`,
  `Round.iterate_seq` with `Round`/`round_iff`, `expandTM_run_ofCfg`, `copyMapTM_run_ofCfg`,
  `writeAdvTM_run_ofCfg`;
- the release adapter `seamReleaseTM_runFrom_pos`, the input seek `exists_inputSeekTM`, and
  `exists_inputCallTM`'s proof (its split on `entry = exit`): a call's exit may be its entry."""))

E.append(("F5", """- **The overlay** elaborates with exactly the file's two sorry warnings (overlay lines 277 and
  342; at the drafting base, re-checked at issue). The imports create no cycle: their closure contains no `Diagonalization` module.""",
"""- **The overlay** elaborates with exactly the file's two sorry warnings (overlay lines 278 and
  343; at the review, against the post-#167 snapshot; re-checked at issue). The imports create no
  cycle: their closure contains no `Diagonalization` module."""))

E.append(("F4", """- **The import probe** (`EQImportProbe.lean.txt`, **121 checks of 121 names**: megafill D's 76
  after dropping the virtual-input host's five, the route's 43 more, and at issue
  `timeConstructible_iff` and `Round.iterate_seq`): 0 errors, 0 warnings. **Re-run it after your delivery**, extended by every further name you cite.""",
"""- **The import probe** (`EQImportProbe.lean.txt`, **⟨182⟩ checks of ⟨182⟩ names**: megafill D's
  76 after dropping the virtual-input host's five, the route's 43 more, `timeConstructible_iff`
  and `Round.iterate_seq`, and 61 for the release adapter, the input seek, the scan, fold and
  emitter rows, `BufferWords` and the layout equations): 0 errors, 0 warnings. **Re-run it after
  your delivery**, extended by every further name you cite."""))

E.append(("F12", """- **The route probe** (`EQRouteProbe.lean.txt`, 14 lemmas), sealed over 7 TCSlib definitions""",
"""- **The route probe** (`EQRouteProbe.lean.txt`, 16 lemmas, 14 of them axiom-printed, and the
  decision `qyDecide` over `QyStep`), sealed over 7 TCSlib definitions"""))

E.append(("F12", """  - `qy_stage_lt_log` (with `qy_two_pow_le_ladder`): `stage f n < log₂ n`.""",
"""  - `qy_stage_lt_log` (with `qy_two_pow_le_ladder`): `stage f n < log₂ n`.

  Its docstrings are probe records: `qy_ladder_succ_eq` has none, and two name campaign items
  ("A1's reading", "the dossier's `eqDecide`"). Give every declaration you copy a public-facing
  docstring."""))

E.append(("F5", """- **(a) the imports**, as your first edit: exactly `import Mathlib.Data.Nat.Log` before line 6, and
  after line 8 `import TCSlib.Complexity.TuringMachine.Build.StepClock`, `…Build.InputCall`,
  `…Build.Contract.Catalog`, `…Build.Contract.Seam`, `…Build.Primitives`, `…Build.Rewind` (the
  overlay). No other import.""",
"""- **(a) the imports**, as your first edit: exactly `import Mathlib.Data.Nat.Log` before line 6, and
  after line 8 `import TCSlib.Complexity.TuringMachine.Build.StepClock`, `…Build.InputCall`,
  `…Build.Contract.Catalog`, `…Build.Contract.Seam`, `…Build.Primitives`, `…Build.Rewind`,
  `TCSlib.Complexity.TuringMachine.BufferWords` (the overlay; `BufferWords` carries the cell
  identities of concatenated words, `FinTM.bufferTape_append_shift` and its siblings). No other
  import."""))

E.append(("F17", """Frozen: the module header (lines 14–68: the maintainer updates its""",
"""Frozen: the module header (lines 14–69: the maintainer updates its"""))

E.append(("F1", """  Run `C_f` under the clock with the stop states `{exit}`. **Never run the witness through
  `vhostSilentTM` or a hand-built bank:** a passed round would leave its work tapes dirty, and
  only the install call's tracked banks restore them.""",
"""  **Its `entry` and `exit` may coincide** (the statement quantifies them separately), so run
  `C_f` released at its entry: `seamReleaseTM C_f.tm entry` from the fresh state `Sum.inl ()`,
  which at every positive time is `C_f`'s run right-tagged (`seamReleaseTM_runFrom_pos`), under
  the clock with the stop state `Sum.inr exit`. **Never run the witness through `vhostSilentTM`
  or a hand-built bank:** a passed round would leave its work tapes dirty, and only the install
  call's tracked banks restore them.
- **Every call you sequence** (install or input; a seam and the phase host dispatch at an exit
  before its action): release it at its entry the same way, or split on `entry = exit` as
  `exists_inputCallTM`'s proof does."""))

E.append(("F4", """  - **L1, the guard decider**: `x ↦ [decide (x = replicate |x| true ∧ 3 ≤ |x|)]`, linear time.""",
"""  - **L1, the guard decider**: `x ↦ [decide (x = replicate |x| true ∧ 3 ≤ |x|)]`, linear time,
    composed from the framed input fold `Turing.inputFoldTM` (`inputFoldTM_run_ofCfg`) and a
    verdict emission over `Turing.emitAction` (`FinTM.emit_halts`), or from the function-level
    rows (`computesFunInTime_incFixed` with `incFixed_eq_none_iff_replicate`,
    `computesFunInTime_ifEq`, `computesFunInTime_cond`): not a hand-written scan of the input."""))

E.append(("F8", """  - **L2, the binary `≤`** of two tape-resident `Nat.bits` words (lengths first, then from the top
    bit; `Nat.bits` has no trailing `false`).""",
"""  - **L2, the binary `≤`** of two tape-resident `Nat.bits` words (lengths first, in lockstep, then
    from the top bit; `Nat.bits` has no trailing `false`), **within a constant times
    `|bits n| + 1` steps whatever `|bits (f a)|` is**: no published lemma bounds `|bits (f a)|`
    by the call's time."""))

E.append(("F9", """    `1^{min (u·v) K}` from unary `u`, `v` and a unary cutoff `K`.""",
"""    `1^{min (u·v) K}` from unary `u`, `v` and a unary cutoff `K`, within
    `O((u + v + K + 1)²)` steps."""))

E.append(("F4", """  - **L4, the power-of-two scan** of `bits n` (`bits n = replicate L false ++ [true]`).""",
"""  - **L4 is not a leaf.** The power-of-two test (`bits n = replicate L false ++ [true]`) and the
    setup's `n ≥ 3` test are folds over `bits n`: the fold instance of the framed scan
    `Turing.scanTM` (`scanTM_run_ofCfg` or `scanTM_contract`, with `scanFold` and `scanKeep`;
    `scanResult_fold`: the verdict `done (w.foldl δ a₀)` at exactly `2|w| + 2`, the word intact)."""))

E.append(("F9", """  - **L5, the unary `Nat.unpair`**: `(Nat.unpair h).1` in unary from `h` in unary (`h < log₂ n`;
    any polynomial-time scan).""",
"""  - **L5, the unary `Nat.unpair`**: `(Nat.unpair h).1` in unary from `h` in unary (`h < log₂ n`),
    within `O((h + 1)³)` steps, composed from L3 and the rows above."""))

E.append(("F3", """  - **L6, the writer's emitter**: emit a tape word raw, or each bit doubled, optionally omitting
    its last symbol (for `α = (bits (j + 1)).dropLast`), and emit fixed words.

  **Any further leaf is an escalation.**""",
"""  - **L6, the writer's emitter**: emit a tape word with each bit written `r ∈ {1, 2, 4}` times,
    optionally omitting its last symbol (for `α = (bits (j + 1)).dropLast`); fixed words over
    `Turing.emitAction` (`FinTM.emit_halts`, `FinTM.emit_run`).

  L2 and L3 say in their docstrings why `compareTM_contract` (equality, at `compareStop`) and
  `walkTM_run_ofCfg` (the lockstep ruler) do not serve. **Any further leaf is an escalation.**"""))

E.append(("F2", """- **No input rewind is needed** (every phase reads the native input at most once, through the input
  calls). If your route needs one, cite `Turing.inputRewindTM` (`Build/InputRewind`); never write
  one.""",
"""- **The input head after a timeout.** Every call starts at `Cfg.ofWords`, with the input head at
  `1`. After the clock's timeout the input head is the call's at some time before its exit, which
  no published clause determines, and the call's bank and the counter tape are dirty. So, after
  the loop and before any call, return the input head to `1` by the input seek
  `Turing.exists_inputSeekTM` at `p = 1` (`Build/InputCall`), on two dedicated tapes written at
  the setup (`[true]` and a blank one), within `C (1 + pos + 2) ≤ C (n + 4)` steps. A timed-out
  call is silent: its output is a prefix (`MultiTapeTM.output_prefix`) of its exit's, which is
  `[]`. No later phase touches the call's bank or the counter. Never write an input rewind;
  `Turing.inputRewindTM` is outside your imports and needs the head at `1` or more."""))

E.append(("F4", """reads only `|x|`, and must halt within its bound on **every** `x`, including `n ≤ 2`: its setup
tests `n ≥ 3` on `bits n` and outputs `[]` otherwise, which is `F x` there (`query_of_not_guard`).""",
"""reads only `|x|`, and must halt within its bound on **every** `x`, including `n ≤ 2`: its setup
tests `n ≥ 3` on `bits n` (the scan fold) and outputs `[]` otherwise, which is `F x` there
(`query_of_not_guard`)."""))

E.append(("F7", """- the rung `ℓ₀ = 2` and the stage index `h = 0` in unary;
- the clock's counter: the all-ones word of width `m = |bits n| + |bits D₀|`, of value
  `2^m − 1 ≥ D₀ (n + 1)` (`qy_ones_val`). `D₀` is a constant such that, whenever `f a ≤ n` and
  `a ≤ n`, `C_f` returns within `D₀ (n + 1)`, by its bound
  `c' (c_f (f a + 1) + a + |bits (f a)| + 1)` and `|bits (f a)| ≤ f a`
  (`Turing.length_bits_le_self`).""",
"""- the rung `ℓ₀ = 2` and the stage index `h = 0` in unary;
- the input seek's two tapes (`[true]`, and a blank one);
- the clock's counter: the all-ones word of width `m = |bits n| + |bits D₀|`, of value
  `2^m − 1 ≥ D₀ (n + 1)` (`qy_ones_val`, `qy_ones_ge`). `D₀` is a constant such that, whenever
  `f a ≤ n` and `a ≤ n`, `C_f` returns within `D₀ (n + 1)`, by its bound
  `c' (c_f (f a + 1) + a + |bits (f a)| + 1)` and `|bits (f a)| ≤ f a`
  (`Turing.length_bits_le_self`): `D₀ = c' (c_f + 2)` (`qy_call_bound`). Write it by `copyMapTM`
  from `bits n` (every symbol mapped to `true`), then `writeAdvTM` of the fixed word
  `replicate |bits D₀| true`, its head back at the word's start."""))

E.append(("F1", """1. Install `1^a` on `C_f`'s tape `0` (a copy of the rung, one more cell). Run `C_f` under the clock.
   - **Timeout** (no return within `2^m − 1`): `n < f a` by the call's bound (`qy_call_bound`). The escape is
     interior.
   - **Finish:** `bits (f a)` on `C_f`'s tape `0`, every other tape of the call blank. The clock
     leaves the counter as "some word of the same width": restore it by `copyMapTM` from `bits n`,
     every round.""",
"""1. Install `1^a` on `C_f`'s tape `0` (a copy of the rung, one more cell). Run `C_f`, released at
   its entry, under the clock (stop state `Sum.inr exit`).
   - **Timeout** (no return within `2^m − 1`): `n < f a` by the call's bound (`qy_call_bound`). The
     escape is interior; the input head is then unknown and the call's bank dirty (the input
     seek, above).
   - **Finish:** `bits (f a)` on `C_f`'s tape `0`, every other tape of the call blank, the input
     head at `1`. The clock leaves "some word of the same width" on all `m` counter cells:
     rewrite the whole width every round (`copyMapTM` from `bits n` and the fixed tail again)."""))

E.append(("F6", """3. `X = f a + a + 1` in unary: `expandTM` with the counter `bits (f a)`, then the rung twice and
   one cell.""",
"""3. `X = f a + a + 1` in unary: `expandTM` with the counter `bits (f a)`, then one copy of the rung
   and two cells (`X = f a + ℓ + 2`)."""))

E.append(("F4", """   - `X⁴ < L`, or `X⁴ = L` with `n` not a power of two (L4): **next**;""",
"""   - `X⁴ < L`, or `X⁴ = L` with `n` not a power of two (the scan fold, `qy_pow_two_bits`): **next**;"""))

E.append(("F12", """(`eq_ladder_succ_eq`'s""", """(`qy_ladder_succ_eq`'s"""))

E.append(("F9", """The ledger: `∑_{h < s} ℓ_{h+1} ≤ 2ℓ_s < 2n` (`qy_ledger`), plus `s · O((L + 1)²)` with
`s < log₂ n` (`qy_stage_lt_log`), plus the last round's `O(n)`. All of it is `O(n)`; state it as
`≤ A (n + 1)` for a constant `A`.""",
"""The ledger: `∑_{h < s} ℓ_{h+1} ≤ 2ℓ_s < 2n` (`qy_ledger`), plus `s · O((L + 1)²)` with
`s < log₂ n` (`qy_stage_lt_log`), plus the last round's `O(n)`. All of it is `O(n)`; state it as
`≤ A (n + 1)` for a constant `A`. The polylogarithmic terms (this one and L5's `O((L + 1)³)`) are
linear by `(L + 1)³ ≤ 8 · 2^L` (a private arithmetic lemma) and `2^L ≤ n` (`Nat.pow_log_le_self`)."""))

E.append(("F2", """**After the loop** (checkpoints 5 and 6).
- **The stage code:**""",
"""**After the loop** (checkpoints 5 and 6).
- **The input head:** the input seek at `p = 1` (above), `O(n)`.
- **The stage code:**"""))

E.append(("F3", """- **The writer** (L6). Emit, in order:
  - the flag (`true` at the top, `false` in the middle);
  - the budget field's bits, each doubled;
  - `[false, true]`;
  - `α` doubled;""",
"""- **The writer** (L6). The outer pairing doubles the whole inner pair, its separator included:
  `pairEncode (pairEncode B α) t` is `B.flatMap (fun b => [b, b, b, b])`, then
  `[false, false, true, true]`, then `α.flatMap (fun b => [b, b])`, then `[false, true] ++ t`
  (`pairEncode_eq` twice, `List.flatMap_append`, `List.flatMap_assoc`). Emit, in order:
  - the flag (`true` at the top, `false` in the middle);
  - the budget field's bits, each written four times;
  - `[false, false, true, true]`;
  - `α` doubled;"""))

E.append(("F3", """  This is exactly `query_eq`'s word (`pairEncode_eq`). Cost""",
"""  This is exactly `query_eq`'s word. Cost"""))

E.append(("F2", """- `f a > n` reached by a timeout, and by a fast witness with a large output;""",
"""- `f a > n` reached by a timeout (then the input seek, and a silent dirty bank), and by a fast
  witness with a large output (L2's bound);"""))

E.append(("F4", """  the pure function (D1, D2, D4, D5 internal), and its arithmetic rows are private leaves with
  promotion requests. This brief's L1–L6 are those rows, in unary where the note says so.""",
"""  the pure function (D1, D2, D4, D5 internal), and its arithmetic rows are private leaves with
  promotion requests. This brief's leaves (L1–L3, L5, L6) and the scan folds are those rows, in
  unary where the note says so."""))

E.append(("F4", """The probe's 121 names: the target and the stages' laws; A1's reading and the function-level API;
the calls; the clock; the expansion, copy, clear, skip, write and rewind rows; the seams, the phase
host, R1 and the contract layer; `Nat.bits`, `Nat.log` and `Nat.unpair` facts.""",
"""The probe's ⟨182⟩ names: the target and the stages' laws; A1's reading and the function-level API;
the calls, the release adapter and the input seek; the clock; the expansion, copy, clear, skip,
write, rewind, scan, fold, compare and walk rows and the emitter; the seams, the phase host, R1,
the layout equations and the contract layer; `BufferWords`; `Nat.bits`, `Nat.log` and
`Nat.unpair` facts."""))

E.append(("F5", """6. **Imports.** Exactly the seven in region (a).""",
"""6. **Imports.** Exactly the eight in region (a)."""))

E.append(("F10", """      - `counterLoopCfg`: through its field equations.""",
"""      - `counterLoopCfg`: through `Turing.counter_cfg_eq` (the body bank, then the counter) and
        `counterLoopCfg_body`; it has no per-field equations.
      - A released call: through `seamReleaseTM_runFrom_pos`."""))

E.append(("F1", """        `embedEmitTM`, `embedSilentTM`, `pairEncode`. Add `attribute [-simp]` on the `@[simp]`
        definitions among them. The copy must still elaborate, **with controls**: for each sealed""",
"""        `embedEmitTM`, `embedSilentTM`, `pairEncode`, `seamReleaseTM`, `phaseHostTM`,
        `Cfg.mapState`, `Cfg.Stopped`, `embedEmitCfg`, `FinTM.bufferTape`, `scanTM`, `inputFoldTM`,
        `writeAdvTM`, `clearTM`, `rewindTM`, `dbl`. Add `attribute [-simp]` on the `@[simp]`
        definitions among them. A reducible `abbrev` (`Cfg.Halted`, `counterLoopOrbit`) cannot be
        sealed: read it through its body (`policy.md`). The copy must still elaborate, **with
        controls**: for each sealed"""))

E.append(("F12", """    another file. Keep your new privates under the `qy_` prefix (unused in the tree at the
    drafting base).""",
"""    another file. Keep your new privates under the `qy_` prefix (`Qy`/`qy` for types and
    definitions, as `QyStep`, `qyDecide`; unused in the tree at the drafting base)."""))

E.append(("F4", """2. **The setup** as a contract, with its `O(n)` bound.""",
"""2. **The setup** as a contract (the `n ≥ 3` scan, `bits n`, `L`, the rung, the seek's tapes, the
   counter), with its `O(n)` bound."""))

E.append(("F2", """5. **The stage code:** `α` on a tape.""",
"""5. **The input seek and the stage code:** the input head at `1`, then `α` on a tape."""))

E.append(("F13", """- **The population** is 21 files (`campaign/fills/eq/inputs/eq-fill-query/screen-population.txt`):
  - your file;
  - the files the route cites: `Build/StepClock`, `Build/Loop`, `Build/InputCall`,
    `Build/Wrappers`, `Build/Primitives`, `Build/CounterLoop`, `Build/Scan`, `Build/Catalog`,
    `Build/Rewind`, `Build/Seam`, `Build/Embed`, `Build/Contract/Basic`,
    `Build/Contract/Catalog`, `Build/Contract/Seam`, `Composition`, `Finite`;
  - the known hazards: `ClassNP/ExhaustiveReplay` (capped replays over the same clock),
    `TimeHierarchy/ClockLoop` (a colleague's clocked loop), `Diagonalization/NTimeHierarchy`, and
    `Simulation` (the input-rewind family; this item writes none).""",
"""- **The population** is 29 files (`campaign/fills/eq/inputs/eq-fill-query/screen-population.txt`):
  - your file;
  - the files the route cites: `Build/StepClock`, `Build/Loop`, `Build/InputCall`,
    `Build/Wrappers`, `Build/Primitives`, `Build/CounterLoop`, `Build/Scan`, `Build/Catalog`,
    `Build/Rewind`, `Build/Seam`, `Build/Embed`, `Build/Contract/Basic`,
    `Build/Contract/Catalog`, `Build/Contract/Seam`, `Build/Convention`, `Composition`, `Finite`,
    `Encoding`, `StateRenaming`, `BufferWords`, `ClassP/TimeConstructible`;
  - the known hazards: `ClassNP/ExhaustiveReplay` (capped replays over the same clock),
    `TimeHierarchy/ClockLoop` (a colleague's clocked loop), `Diagonalization/NTimeHierarchy`,
    `Simulation` (the input-rewind and emitter family), `Build/SeamLayout` (a phase-host composite
    over catalog rows and private leaves: a model to read, not to copy), and `ClassNP/TMSAT` and
    `ClassNP/Nondeterminism` (private unary deciders, L1's neighbours)."""))

E.append(("F14", """  - the `Cfg.mapState_mapState` field-equation idiom (two accepted idiom pairs: say so if yours is
    a third).""",
"""  - the `Cfg.mapState_mapState` field-equation idiom (two accepted idiom pairs: say so if yours is
    a third);
  - `ClassP/BinaryArith` (#135, merged into `main`, not in your tree): its polynomial-time `le` and
    `lt` (`AddSub`) and unary `mulU` (`Loops`) are the nearest statements to L2 and L3. Ledger L2
    and L3 against them in `REPORT.md`, and include `origin/main` in the semantic search."""))

E.append(("F18", """- **Lint:** `python3 -I scripts/campaign_style_lint.py TCSlib/Complexity/Diagonalization`, 0 FAIL
  (base: ⟨…⟩). No new line over 100 characters.""",
"""- **Lint:** `python3 -I scripts/campaign_style_lint.py TCSlib/Complexity/Diagonalization`, 0 FAIL
  (base: ⟨0 FAIL, 2 WARN over 5 files⟩). No new line over 100 characters. Your file will pass 1000
  lines: the size WARN that follows is expected, not a failure (file size alone is not a driver)."""))

E.append(("F15", """- [ ] Every new declaration with its role; `M₁`'s tapes (the call's, the clock's counter, the
      rung, `L`, `h`, the scratch); each leaf L1–L6 and its run.""",
"""- [ ] Every new declaration with its role; `M₁`'s tapes (the call's, the clock's counter, the
      rung, `L`, `h`, the seek's, the scratch); each leaf (L1–L3, L5, L6) and its run, and each
      scan fold.
- [ ] Each call's release (or its `entry = exit` split); the input seek after the loop; the
      timed-out call's silence.
- [ ] The base sorry list by name; each edge case with the lemma that covers it."""))

E.append(("F2", """- **The install call's start is `Cfg.ofWords (input := x) entry (stateWord C.k arg)`**: every tape
  of the call blank except tape `0`, all heads at `0`. Embed the call (R1) on tapes that are blank
  there, and read its endpoint through `Cfg.ofWords`'s equations.""",
"""- **The install call's start is `Cfg.ofWords (input := x) entry (stateWord C.k arg)`**: every tape
  of the call blank except tape `0`, all heads at `0`, the input head at `1`, the output empty.
  Embed the call (R1) on tapes that are blank there, and read its endpoint through `Cfg.ofWords`'s
  equations."""))

E.append(("F1", """- **The clock's stop states:** with `stopAt s := decide (s = exit)`, a first stop at `τ` needs
  `∀ u < τ, ¬Stopped`. That is the call's cut for `0 < u < τ`, `entry ≠ exit` at `u = 0`, and "not
  halted before `τ`" (a halted run stays halted: `MultiTapeTM.runFrom_of_halt`), read through
  `Cfg.stopped_iff`.""",
"""- **The clock's stop state:** on the released call, with `stopAt s := decide (s = Sum.inr exit)`,
  a first stop at `τ` needs `∀ u < τ, ¬Stopped`: at `u = 0` the state is the fresh `Sum.inl ()`;
  at `0 < u < τ` it is the call's, right-tagged (`seamReleaseTM_runFrom_pos`,
  `Cfg.mapState_state`), off `exit` by the call's cut, and live since the call reaches `exit`
  (`MultiTapeTM.runFrom_state_ne_none_of_le`); read through `Cfg.stopped_iff`. **`entry ≠ exit`
  is not available**: neither call's statement excludes `entry = exit`. The clock's exits are the
  injective families `finish r` and `timeout r` over the body's state: route the whole timeout
  family through the phase host."""))

E.append(("F11", """- **A seam's or phase host's initial state has no equation:** use the `with q₀` override and
  `MultiTapeTM.initCfg_with_q₀`/`runFrom_with_q₀`.""",
"""- **A seam's initial state has no equation:** use the `with q₀` override and
  `MultiTapeTM.initCfg_with_q₀`/`runFrom_with_q₀`. The phase host's is `phaseHostTM_q₀`, and a
  machine's initial configuration is the blank seam `Cfg.ofWords q₀ (fun _ => [])`
  (`initCfg_ofWords`).
- **`writeAdvTM` returns to its own anchor** (state `0`): a seam or the phase host would dispatch
  it at time `0`. Sequence it through `ReturnContract.release` (`seamReleaseTM`).
- **The round times are existential** (the calls' and the clock's `∃ t ≤ …`): choose them before
  `Round.iterate_seq`, whose `τ : ℕ → ℕ` comes first. The head relation can be
  `P := fun _ => True`: no space bound is needed."""))

t = open(draft_src, encoding="utf-8").read()
for i, (f, old, new) in enumerate(E):
    c = t.count(old)
    assert c == 1, f"edit {i} ({f}) matched {c} times: {old[:70]!r}"
    t = t.replace(old, new)
open(draft_dst, "w", encoding="utf-8").write(t)

p = open(pop_src, encoding="utf-8").read()
old_head = "# The E-Q brief's screen population (draft; fixed at issue). One repository path per line.\n"
assert p.startswith(old_head)
assert p.endswith("TCSlib/Complexity/TuringMachine/Simulation.lean\n")
add = [
    "TCSlib/Complexity/TuringMachine/Build/Convention.lean",
    "TCSlib/Complexity/TuringMachine/Encoding.lean",
    "TCSlib/Complexity/TuringMachine/StateRenaming.lean",
    "TCSlib/Complexity/TuringMachine/BufferWords.lean",
    "TCSlib/Complexity/ClassP/TimeConstructible.lean",
    "TCSlib/Complexity/TuringMachine/Build/SeamLayout.lean",
    "TCSlib/Complexity/ClassNP/TMSAT.lean",
    "TCSlib/Complexity/ClassNP/Nondeterminism.lean",
]
for a in add:
    assert a not in p
p = p + "".join(a + "\n" for a in add)
assert len([l for l in p.splitlines() if l and not l.startswith("#")]) == 29
open(pop_dst, "w", encoding="utf-8").write(p)
print(f"applied {len(E)} draft edits; population 29 files")
