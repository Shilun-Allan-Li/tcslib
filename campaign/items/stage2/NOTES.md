# Stage 2 statement draft: PROG-4, PROG-3 and PROG-2 signatures

Draft only. Nothing in the worktree `wt-s2` was edited. The Lean files below are new and
self-contained, they import only modules that already have oleans, and they put every new
definition under `TCSlib.Draft.Stage2` (and `TCSlib.Draft.Stage2.Lang`). Every theorem is
`sorry`. Each one has a docstring with a natural-language statement, a tag where a source exists,
and a proof sketch.

## 1. Files

| File | Lines | Contents |
|---|---|---|
| `Stage2Draft.lean` | 723 | The draft extended word RAM (`XInstr`, `XCfg`, `xstep`, `XSteps`, `CoinFree`, `XProgram.proj`) and conservativity over the vendored RAM. Footprints along runs (`baseTouches`, `XInstr.touches`, `XStepsIn`, `StepsIn`). The start convention and halting (`startMem`, `XCfg.init`, `HaltsWithin`). The word-size hypothesis (`WordSizeComputable`) with two bridges. **Stage 2** (`exists_simulation`, `exists_ndSimulation`). The corollaries for DTIME/P, SPACE/L, transducers, Savitch's shape, NSPACE/NL. **PROG-3 at the compiler level** (`Touchable`, `FinishedIn`, `sim_in`, `region`, `compileProgram_footprint`, `haltsWithin_compileProgram`). |
| `ExtensionsDraft.lean` | 415 | **PROG-2's signatures**, as a mirror: `XStmt` (the 7 constructors plus `inBit`, `emit`, `coin`, `half`), `XLimits` (adds `input`), `XExec` (indices `o`, `r`; 9 + 4 rules), the restated inductions (`ofExec`, `append`, `loc_eq_of_notMem_assigns`, `bounded`, `mem_outside`), `coins_length_le`, `output_length_le`, the determinism lemma `XExec.det`, `XEnds`, `EndsIO` and its 15 rules, `MeetsIO` with `EndsIO.callLast`, `AcceptsND`, `acceptProb`, and `XFits` (the input-length clause). |
| `probes/Stage2Sanity.lean` | | `Stage2Draft.lean` plus 13 `example`s that evaluate the draft semantics (see §2). |
| `probes/ExtensionsSanity.lean` | | `ExtensionsDraft.lean` plus 8 `example`s (see §2). |
| `probes/Probe1.lean` | | Design probe. Its one error is intended: it shows that `⟨…⟩` does not fill default fields. Also checks `Int` division and `BitVec.sshiftRight`. |
| `probes/Probe2.lean` | | Design probe: an inductive relation exposed under a derived `∃` name, with leading-dot and dot notation still resolving (PROG-2 option B, §5). |
| `probes/*.out` | | The elaboration outputs. |

**What is copied** (also recorded in each file):
- `xstep` restates the match of `WordRAM.step` (`WordRAM/Steps.lean:116-129`) for the nine
  vendored instructions. The six straight-line ones go through `WordRAM.effect` (`Steps.lean:249`)
  rather than copying their arms.
- `XSteps` and `StepsIn` restate `WordRAM.Steps` (`Steps.lean:134-136`).
- `XStmt` copies `Light.Stmt` (`Light/Syntax.lean:80-88`). `XExec` copies the nine rules of
  `Light.Exec` (`Syntax.lean:155-174`), adding indices.
- `XEnds` copies `Light.Ends` (`Logic.lean:94`). `XStmt.assigns` copies `Light.Stmt.assigns`
  (`Assigns.lean:44`).
- `xmainStmt` copies `Light.mainStmt` (`Compiler/ProgramCode.lean`). `XFits` extends
  `Light.Compiler.Fits` (`Cells.lean:79`) rather than copying it.

No proved material is copied: every copied item is a definition, and every theorem is new and
sorried.

## 2. What I checked, and how

Each file was checked only with `bash tools/leanelab.sh wt-s2 oleans-m1 <file>` (read-only, no
oleans written). The final run, after every edit:

| File | Exit | Errors | Warnings | Of which `declaration uses 'sorry'` |
|---|---|---|---|---|
| `Stage2Draft.lean` | 0 | 0 | 34 | 34 |
| `ExtensionsDraft.lean` | 0 | 0 | 25 | 25 |
| `probes/Stage2Sanity.lean` (draft + 13 examples) | 0 | 0 | 34 | 34 |
| `probes/ExtensionsSanity.lean` (draft + 8 examples) | 0 | 0 | 25 | 25 |
| `probes/Probe2.lean` | 0 | 0 | 0 | 0 |
| `probes/Probe1.lean` | 1 | 1 (intended) | 0 | 0 |

Other checks:
- **Every warning is a `sorry` warning.** `grep -vc "declaration uses 'sorry'"` is 0 on all four
  `.out` files of the drafts and sanity copies.
- **Semantic sanity.** The `example`s are proved by `rfl` or `decide` against the draft definitions:
  - accept, reject, and reject past the end;
  - `emit` of a nonzero and of a zero cell;
  - `rdIn` on the input, off the input, and at a negative position;
  - `coin` with a stream, and with an empty stream (reads 0);
  - `half` (-3 ↦ -2);
  - `bltz` jumping;
  - `add` through `WordRAM.effect`;
  - `HaltsWithin [.base .accept] x ρ W 1 true [] 0`, which shows the predicate is satisfiable;
  - `XProgram.proj`;
  - `XExec` derivations of a coin then an emit, for both coin values;
  - an `EndsIO` instance for a coin;
  - `inBitVal`;
  - `XStmt.ofStmt`.
- **Negative controls.** Two deliberately false variants were each rejected with 1 error, and then
  deleted: one changed an `emit` result, the other an `inBitVal` result. So the examples really
  are checked.
- **Line widths.** At most 100 characters per line (counted in characters, not bytes).
- **Docstrings.** Every declaration has one.

The counts and grep figures quoted below were taken from `wt-s2` with `grep`. Where a figure is a
regex estimate, it says so.

## 3. Stage 2 (PROG-4): the statement and the design choices

### The statements

- `exists_simulation P fn hW : ∃ M A, ∀ x t f v o, HaltsWithin P x [] (W |x|) t v o f →`
  `M.ComputesInTime x (outputOf fn v o) T ∧ M.tm.spaceUsed (M.tm.initCfg x) T ≤ S`.
- `exists_ndSimulation P hW : ∃ N A, ∀ x t f, (∀ ρ, ∃ v o, HaltsWithin P x ρ (W |x|) t v o f) →`
  `N.tm.HaltsWithin x T ∧ (∀ w, |w| = T → N.tm.spaceUsedWith w … ≤ S) ∧`
  `(N.AcceptsWithin x T ↔ ∃ ρ o, HaltsWithin P x ρ (W |x|) t true o f)`.

Both use the following bounds, with `n = |x|` and `W = W n`:
- `T = TW n + A·(t+1)·(f·(W+1) + W² + n + 1)`;
- `S = SW n + A·(f·(W+1) + W + logSpace n + 1)`.

### Choices

1. **The bound's shape: three changes from §15a, each read off the code.**
   - *No separate address width `a`.* Addresses are words: `load` reads `m (m j).toInt` and
     `store` writes at `(m i).toInt` (`WordRAM/Basic.lean:62-63`). Immediate addresses are
     constants of `P`. So a table entry has `W + O_P(1)` bits, and `f·(W + a)` becomes
     `f·(W + 1)` with the constant folded into `A`.
   - *The seek term is `n`, not `n·log n`.* R8.5b `Turing.exists_inputSeekTM`
     (`Build/InputCall.lean:294`) seeks position `p` within `C·(|w| + pos + p + 1)` steps, with
     work envelope `C·(|w| + 1)`. Here `|w| ≤ W` and `pos, p ≤ n + 1`. A range test against `|x|`
     comes first (the row needs `p ≤ |x| + 1`), at `O(W + log n)` cost.
   - *The word size's own cost is added once*: `TW n` and `SW n`. §15a's shape has no term for
     it.
2. **The word-size hypothesis: `WordSizeComputable W TW SW`.** Some `FinTM Bool` outputs
   `Nat.bits (W |x|)` from `x` within `TW |x|` steps and `SW |x|` visited cells. Reasons:
   - *Why not `SpaceConstructible` itself?* It has no time bound, so the P corollary could not use
     it. It also carries the conjunct `logSpace ≤ S`, which stage 2 does not need.
   - *Why binary output?* It is `SpaceConstructible`'s and `TimeConstructible`'s convention.
   - *The two consumers are bridges:*
     - `wordSizeComputable_logSpace c`: `W = c·logSpace`, time `a(n+1)`, space `a·logSpace`,
       from R8.5c `exists_inputLengthTM`;
     - `wordSizeComputable_of_spaceConstructible`: `W = c·S`, space `a·S`; its time is some
       function, the maximum over the finitely many inputs of each length.
   - *Alternatives considered:* a fixed form `W = c·logSpace n` only (too narrow for Savitch); a
     unary word size (an awkward interface); `SpaceConstructible` with a separate
     time-constructibility clause (two hypotheses where one suffices).
3. **The start convention: `startMem W n`.** Cell `-1` holds `|x|` mod `2^W` and every other cell
   holds 0.
   - Cell `-1` is `Light.Compiler.cARG1`, so a compiled program receives `|x|` as its first
     argument, as §15c decided (`inLen` from an argument cell, no `len` instruction).
   - Alternative: a `len` instruction and an all-zero start memory. That makes the RAM cleaner but
     adds a tenth kind, and §15c defers it until a consumer needs it.
4. **The RAM extension is a wrapper.** `XInstr.base : Instr → XInstr`, and `XCfg` extends
   `WordRAM.Cfg` with `out` and `rd`. The input and the coin stream are parameters of `xstep`.
   - **`XProgram.proj` with `XSteps.of_steps_proj` and `XStepsIn.of_stepsIn_proj`** replaces the
     new instructions by `reject`. A verdict-free run of the projection is then a run of the mixed
     program, so every vendored segment lemma (`steps_straight`, the dispatcher, the tests, the
     calls) applies unchanged to compiled code that contains the new instructions. See open
     question Q1 for the in-place alternative.
5. **Coins.** The configuration counts consumed coins (`rd`). The coin read is `ρ.getD rd false`,
   so quantifying over all lists `ρ` covers every stream.
   - Alternative: an NDTM-style choice bit at every step. It is closer to `FinNDTM`, but stage 1
     would then have to say which steps' bits are the coins. The consumed-count form matches
     §15c's consumed word `r` exactly.
   - The deterministic form runs on `ρ = []`, so coins read 0. That is more general than requiring
     `CoinFree`, and `HaltsWithin.coin_irrel` covers coin-free programs.
6. **The two new instructions' semantics.**
   - **`emit i` appends `[i] ≠ 0`.** Alternative: the low bit. The two agree on 0 and 1. "Nonzero"
     is robust when programs emit test results, and costs an `O(W)` scan, which is within the
     bound.
   - **`half` is `BitVec.sshiftRight 1`.** `toInt_sshiftRight` gives `⌊v/2⌋` exactly. Its
     language twin is `e.val σ / 2`: `Int./` rounds down for divisor 2, and the probe checks
     `-3/2 = -2` by `decide`.
7. **Footprints.**
   - **What counts:** the cells *touched*, read or written. `load`/`store` count the address they
     read from memory. Stage 2's table needs only the *written* cells, so "touched" is
     conservative. It is chosen because it is what PROG-3 delivers for compiled code: every read
     there also stays in the region (§4).
   - **How it is stated:** `XStepsIn P x ρ K n c c'` is the run with every step inside `K`, and
     `HaltsWithin … f` asks for some `K : Finset ℤ` with `K.card ≤ f`. A footprint function was the
     alternative. The `K`-indexed form composes by `∪` (`StepsIn.trans`) and is what the
     simulation proofs produce.
8. **Output modes.** `fn = false` writes `[v]`, which is what `DecidesInTime`, `DecidesInSpace`
   and `AcceptsWithin` read. `fn = true` writes the emitted word, which is what `ComputesInSpace`
   reads, for log-space transducers.
9. **The nondeterministic form.**
   - The bounds are uniform over all coin streams, as §15c decided. Acceptance is "some stream
     accepts", stated at the same uniform `t`.
   - Each `coin` is a single choice step; every other step has equal transitions.
   - The fill needs one infrastructure lemma not present today. On states where
     `tr false = tr true`, `runWith w` agrees with the deterministic `fixChoice` run. Without it,
     the deterministic `Contract`s of the other phases cannot be applied to NDTM branches. This is
     the ND variant that §16 lists as "later" for MIG-0.
10. **The corollaries** go through `Complexity`'s own classes:
    - `mem_DTIME_of_decides` and `mem_P_of_decides` (polynomial `TW + W`, `t`, `f`), and
      `mem_P_of_decides_logWord`;
    - `mem_SPACE_of_decides` (general `s`), and `mem_LOGSPACE_of_decides` (`O(1)` cells,
      `W = c·logSpace`);
    - `computesInSpace_of_computes` (transducers), and `mem_SPACE_mul_of_decides` (Savitch's shape:
      `S` space-constructible, `W = c·S`, `f ≤ c·S`, giving `SPACE(S·S)`);
    - `mem_NSPACE_of_accepts` and `mem_NL_of_accepts`.

### Proof architecture (the fill plan, as sketched in `exists_simulation`)

1. **Start-up.** Run the word-size witness with its output redirected to a work tape (R1). Build
   a unary ruler of `W` cells. Count `|x|` (R8.5c) into a private binary copy, and install the
   table entry `-1 ↦ |x| mod 2^W`.
2. **Phase host.** One phase per position of `P`.
3. **Per-instruction `Turing.Contract`s** (MIG-0a). Their index `ι` is the RAM data. The
   precondition is "the tapes encode the RAM configuration": the table, the pc phase, the ruler,
   the length copy. The endpoint encodes `xstep`. The time is at most
   `A·(f·(W+1) + W² + n + 1)` per step, and the envelopes are the table extent plus `O(W)`. The new
   rows are those §15a lists:
   - find-by-key with the key on another tape;
   - two-tape add/sub mod `2^W`;
   - multiplication;
   - the sign test;
   - in-place field overwrite;
   - plus the arithmetic shift for `half`.
4. **The simulation induction** over `XStepsIn`. The table holds only cells of `K ∪ {-1}`, so at
   most `f + 1` entries.

## 4. PROG-3: the footprint along a run

**The code's region notion is exactly §15c's.** `Light.Compiler.lowCell`
(`Compiler/WholeProgram.lean:134`) is `max (2·stackCells) (25 + 4·dispPos)`, and
`Outcome.far` (`WholeProgram.lean:232`) says the cells `a < -lowCell` and `a ≥ lim.space` are
unchanged *at the end*. The draft's `region P dec lim = Finset.Ico (-lowCell) lim.space` is that
complement, with `card_region = lowCell + lim.space`.

**What it strengthens.**
- `Light.Compiler.sim` (`Simulation.lean:483`) becomes **`sim_in`**: its `Finished`
  (`Simulation.lean:182`; `run : Steps …`, `agree : AgreeOutside (Writable …) m m'`) becomes
  `FinishedIn`, which adds `runIn : StepsIn S.code (Touchable S.toSizes q) n …`.
- `Light.compileProgram_correct` (`WholeProgram.lean:241`) becomes
  **`compileProgram_footprint`**: the run up to the verdict, within the region, with `n <
  ramSteps`.
- With `StepsIn.agreeOutside`, every intermediate memory then agrees with the initial one outside
  the region.
- `Touchable Z q = Writable Z q ∪ Constants Z.disp`, because compiled code also *reads* the
  constants and the pool. I traced every instruction of `compileExpr`, `compileCond`,
  `compileStmt`, `callCode`, `epilogue`, `dispatcher`, the start-up and `tailCode` against
  `Cells.lean`'s sets. Reads stay inside too:
  - a local variable's cell is `cStack (q + x)` with `x < F`;
  - a light load reads `a.val σ`, which `Safe` puts below `lim.space`;
  - the return slot is `cStack (q + F)`;
  - the temporaries reach `cT (2F)`, and `2F + 17 ≤ dispPos` places them above the pool's end.
- **Bridge:** `haltsWithin_compileProgram` turns a light run of the outermost call on `(|x|, 0)`
  into stage 2's hypothesis. It needs `startMem` to satisfy `Input lim 0 |x| 0`, which holds:
  `cARG2 = -2` holds 0. The hypothesis it gives is `t = ramSteps`, `f = lowCell + lim.space`.

**The language level needs no new lemma.** `Exec`'s rules already confine every access:
- `Expr.Safe` asks `lim.Addr` for every load (`Syntax.lean:129`);
- `Exec.store` asks it for every store (`Syntax.lean:159`);
- every intermediate state of a run is the final state of a sub-run, so `Exec.mem_outside`
  (`RunsStayInLimits.lean:99`) covers it.

The gap is entirely at the RAM level: `Steps` records no intermediate memories, and `Finished`
frames only the last one.

**Porting `Footprint.lean` versus strengthening `Steps`.** I cannot assess upstream's
`Machine/Footprint.lean`: it is not vendored and I have not seen it. From what is visible, the
draft recommends this:
- **Add** `StepsIn` beside `Steps` (vendored `Steps` untouched).
- **Add the field** `runIn` to `Finished`, or keep `FinishedIn` as a separate structure.
- **Give footprint twins** to the segment lemmas: `stepsIn_straight`, the jump and `steps_setVar`
  (`Cells.lean:329-337`), the tests (`Conditions.lean:65-95`), the dispatcher
  (`Dispatcher.lean:74-109`), the expressions, the call frames, the start-up
  (`StartUp.lean:256`), and the tail (`WholeProgram.lean:82`).

Strengthening `Steps` itself would retype every `Steps` statement (22 signature lines with literal
configurations, grep estimate). If upstream's `Footprint.lean` turns out to be a run-indexed
footprint of the same kind, porting it replaces `StepsIn` and changes nothing else in this draft.

## 5. PROG-2: the signatures, and the edit list

### The signatures

The signatures are in `ExtensionsDraft.lean` (mirror). Three findings came from writing them:
- **`Exec.bounded` gains a hypothesis `1 ≤ lim.word`.** `inBit` and `coin` write `1` with no
  `Safe` premise; `Light.Std` gives it (`100 ≤ word`, `Logic.lean`). `half` needs nothing, since
  `|⌊v/2⌋| ≤ |v|`.
- **`Fits`' input-length clause is not needed by `inBit`.** Off-input positions read 0. It is
  needed only for the argument cell holding `|x|`, and there `Input.arg1_le`
  (`WholeProgram.lean:216`) already demands `|i| ≤ lim.word`. The draft keeps it as `XFits` (as
  §15c says), but it is redundant once the compile theorem takes `i = |lim.input|`.
- **`Ends` hides coin choices existentially.** For programs with coins, `XEnds` means "some coin
  outcome". Specifications meant for every stream must use `EndsIO`. This is a semantic caveat
  for the 14 routines only if they are ever run with coins, which they are not.

### Two edit strategies for `Exec`

Both keep `Ends`' type.

- **A (as §15c decided):** add the indices to `Exec` in place, and set
  `Ends := ∃ σ' o r c, …`.
  - About 32 witness lines change mechanically: Logic 22, Rules 8, Assigns 2 (grep:
    `⟨σ', c, he, …⟩` patterns).
  - The six `cases` inversions in `Rules.lean` keep working.
- **B (probe-tested in `Probe2.lean`):** a new inductive `ExecIO` carries the indices, and
  `Exec := ∃ o r, ExecIO …` keeps the old name, with constructor lemmas `Exec.skip`, ….
  - The leading-dot and dot notation in the 32 witness lines still resolve, so those lines stay
    textually unchanged.
  - The six `cases` inversions in `Rules.lean` (`:191`, `:193`, `:205`, `:207`, `:275`, `:278`)
    need inversion lemmas.
  - The four inductions are re-proved over `ExecIO`.

The compiler needs `ExecIO` under either option.

### Every exhaustive definition or induction the real edit set must extend

The list was found by grep and read; line numbers refer to `wt-s2`.

`Stmt`: 4 new constructors each.

| Site | Kind |
|---|---|
| `Light/Syntax.lean:80` `inductive Stmt` (`deriving Repr`) | the type |
| `Compiler/StatementCode.lean:205` `Stmt.size` | match, 7 arms |
| `Compiler/StatementCode.lean:215` `compileStmt` | match, 7 arms (new code: `compileExpr e 0 ++ [rdIn/half (cT 0) (cT 0)] ++` store-into-`x`; `emit (cT 0)`; `coin (cT 0)` …) |
| `Compiler/StatementCode.lean:287` `length_compileStmt` | induction |
| `Compiler/StatementCode.lean:337` `Stmt.width` | match |
| `Compiler/StatementCode.lean:361-377` `Stmt.width_*_le_iff` | one lemma per constructor (4 new) |
| `Light/Assigns.lean:44` `Stmt.assigns` | match (new: `inBit x`, `coin x`, `half x` assign `x`) |
| `Light/Rules.lean:154` `Ends.of_blockSafe` | exhaustive term match, 7 arms: 4 new arms (`hs.elim`, or real arms if `inBit`/`half` become blocks) |
| `Light/Rules.lean:64` `Stmt.after`, `:73` `Stmt.blockCost`, `:81` `Stmt.BlockSafe` | wildcard; no arm needed (new statements are then non-blocks; decide whether `inBit`/`half` should be blocks) |
| `Compiler/Simulation.lean:70-104` `codeAt_set/seq/ite/while/call` | one per constructor (4 new: `codeAt_inBit`, `codeAt_emit`, `codeAt_coin`, `codeAt_half`) |

`Exec`: 4 new rules, plus the indices. Exactly the six files that §15c names mention `Exec`.

| Site | Kind |
|---|---|
| `Light/Syntax.lean:155` `inductive Exec` | the type |
| `Light/Logic.lean:78` `Exec.append` | induction |
| `Light/Logic.lean:94` `Ends` (and the rule proofs `Ends.skip` … `Ends.call`, `:110-218`) | witnesses (option A) |
| `Light/Assigns.lean:54` `Exec.loc_eq_of_notMem_assigns` | induction |
| `Light/RunsStayInLimits.lean:83` `Exec.bounded` | induction (new hypothesis, §5) |
| `Light/RunsStayInLimits.lean:99` `Exec.mem_outside` | induction |
| `Compiler/Simulation.lean:483` `sim` | induction: 4 new `sim_*` lemmas, and `o`/`r` threaded through `Start`/`Finished` (`:167`, `:182`) and all 9 existing `sim_*` (`:223-437`) |
| `Light/Rules.lean:191, 193, 205, 207, 275, 278` | `cases` inversions on `Exec` (fine under A; lemmas under B) |
| `Compiler/WholeProgram.lean:241` `compileProgram_correct` | takes `Exec` (restated with the stream and the output) |

`Instr`: if extended in place; under the wrapper (Q1) these stay unchanged.

| Site | Kind |
|---|---|
| `WordRAM/Basic.lean:40` `inductive Instr` | the type |
| `WordRAM/Basic.lean:53` `exec` | match, 9 arms |
| `WordRAM/Steps.lean:116` `step` | match, 9 arms |
| `WordRAM/Steps.lean:163` `exec_succ` (`cases P.getD …`, `:168`) | cases |
| `WordRAM/Steps.lean:244` `Straight`, `:249` `effect`, `:412` `WritesIn` | wildcard (decide whether `rdIn`/`half`/`coin` are `Straight`: `rdIn` and `coin` are not memory-only) |
| `WordRAM/Steps.lean:271` `step_straight`, `:417` `WritesIn.mono`, `:420` `agreeOutside_effect` | `cases i` |
| `ComputationalModels.lean:87` | docstring "nine" |

Not affected: the `Expr`/`Cond`/`Op` inductions (`Compiler/Expressions.lean:52, 132`,
`Conditions.lean:161`, `StatementCode.lean:118`). The new constructs are statements, not
expressions. Lib, Frames and Calls neither match on `Stmt` or `Exec` nor destructure `Ends`
witnesses (grep).

## 6. Open questions for the user (each with a recommendation)

- **Q1. How is the RAM extended?**
  - *Wrapper (drafted):* `XInstr.base`, with `XCfg` extending `Cfg`. The vendored `WordRAM/` stays
    byte-identical, and the projection lemma lets the vendored run calculus serve mixed code.
  - *In place:* constructors in `Instr`, fields in `Cfg`. `Probe1.lean` shows that `⟨pos, m⟩`
    does not fill default fields, so every anonymous `Cfg` literal breaks: about 50 in 8
    Compiler and WordRAM files (regex estimate: it has a few false positives and misses some
    literals inside proofs).
  - **Recommendation: the wrapper.** The compiler's code type becomes `List XInstr`, and its
    segment lemmas apply through `proj`.
- **Q2. Which `Exec` edit strategy, A or B (§5)?** **Recommendation: A**, as §15c decided. Its 32
  witness edits are mechanical and scriptable, and the six inversions stay valid. B is the fallback
  if the fidelity gate wants the fewest edited vendored lines.
- **Q3. Which word-size hypothesis?** `WordSizeComputable W TW SW` (drafted, with bridges from
  R8.5c and from `SpaceConstructible`), or `SpaceConstructible` directly. **Recommendation: the
  drafted one.** The P grade needs its time clause, and the bridges keep both consumers one line
  away.
- **Q4. What do `emit`'s bit and stage 2's footprint count?** The draft emits "nonzero", and its
  footprint counts *touched* cells. **Recommendation: keep both.** The alternatives are the low
  bit, and *written* cells, which is tighter but not what PROG-3 produces.

## 7. Where the design document and the code disagree

1. **§15a's bound** has `f·(W + a)` and `|x|·log|x|`. In the code, the address width is the word
   width (`Basic.lean:62-63`), and the seek row is linear (`InputCall.lean:294`). The bound is also
   missing the cost of computing `W`. All three are corrected in the draft (§3.1).
2. **§15c, "`Fits` gains `|x| ≤ word`"** (for `inBit`). `inBit` does not need it, and
   `Input.arg1_le` already covers the argument cell (§5).
3. **§15c, "`Ends` keeps its type … so `Meets` and the 14 routines are untouched".** This is true
   for `Meets`, Lib, Frames and Calls. But Logic (22 lines), Rules (8) and Assigns (2) build or take
   apart `Ends` witnesses, and Rules has 6 `cases` inversions on `Exec`. Under option A those 32
   lines change.
4. **`Exec.bounded`** cannot be extended unchanged. It needs `1 ≤ lim.word` (§5); §15c does not
   mention it.
5. **§15c obstacle 1, "every intermediate memory inside `[-lowCell, lim.space)`".** The code
   confirms the region (`Outcome.far`). The draft proves more: every *read* stays inside too, so
   the stage-2 footprint is `lowCell + lim.space` cells.
6. **§16 lists the nondeterministic `Contract` variant as "later".** Stage 2's ND form needs at
   least the slice lemma of §3.9 before its fill.
7. Confirmed as written:
   - six files mention `Exec`;
   - no vendored file constructs `Limits` (grep finds no literal), so adding `input` to it breaks
     nothing;
   - the RAM has nine instruction kinds.

## 8. Size estimate for the real implementation (ESTIMATE)

| Item | Estimate (lines) | Basis |
|---|---|---|
| PROG-2 vendored edits (Syntax, Logic, Rules, Assigns, RunsStayInLimits, StatementCode, Simulation, WholeProgram) | 600–1,000 | §15c's figure; consistent with the edit list above (4 constructors × ~9 sites, 32 witness lines, 9 `sim_*` threaded) |
| PROG-2 new: `EndsIO` and its rules, `MeetsIO`, determinism, acceptance, 4 `sim_*` cases, the RAM run calculus with `x`/`ρ` | 800–1,300 | the mirror has 15 rules and 6 lemmas; `det` ~150; each new `sim_*` 80–150 |
| PROG-3: `StepsIn` and its lemmas, footprint twins of the segment lemmas, `sim_in`, `compileProgram_footprint` | 750–1,350 | ~10 segment lemmas × 40–80; `sim_in` adds a component to 9 cases |
| Stage 2: start-up 500–900; table rows 1,500–2,500; arithmetic rows 1,500–2,500; `rdIn`/`emit`/`coin` phases 400–800; encoding invariant, dispatcher and induction 1,500–2,500; ND slice lemma and ND form 400–800; corollaries 300–500 | 6,100–10,500 | §15a's 6,000–10,000, itemized |
| Statement files at landing (these drafts, restyled) | ~1,100 | the drafts' 723 + 415 lines |

**Total: about 9,500–15,000 lines** beyond MIG-0a. This is ESTIMATED, not measured.

## 9. Process note

In one command I ran a read-only `git log -1` inside `wt-s2` while listing the probe outputs. It
was the only git command in this task. It changed nothing, and nothing here depends on its output.
The brief forbids git operations of any kind, so I am recording it here.
