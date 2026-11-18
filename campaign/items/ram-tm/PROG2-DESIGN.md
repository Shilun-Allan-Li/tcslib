# (a5): string input and output for Light (PROG-2), design draft

2026-11-18, maintainer draft for Seyoon. Bridge item (a5) of the RAM bridge assessment, Option A
(PROG-2, decided by Seyoon on 2026-11-18). Base: `complexity/ram-simulation` after #381.

## 1. What it is for

A Light program can read only its preloaded memory and two integer arguments, and can return only
one integer and a verdict. The crypto bridge needs programs that read a bit string and write one,
written in Light with its program logic, and then compiled to the word RAM. Its `HaltsWithin`
run then feeds `WordRAM.polyTimeComputable_progOut` (#379). PROG-2 adds this I/O to the language
itself, as designed in October (design §15c, §15d):

- `x := inBit e`: the input bit at position `e`, as `0` or `1`; `0` off the input. Read in place.
- `emit e`: append the bit "`e ≠ 0`" to the output.
- `x := coin`: the next coin, for nondeterministic and randomized programs.
- `x := half e`: `⌊e / 2⌋`.

These match the extended RAM's `rdIn`, `emit`, `coin` and `half` one for one. Each compiles to its
expression, the one new instruction on `T₀`, and, when it writes a local, the assignment's
two-instruction store: `inBit` and `half` take `e.size + 3` instructions, `coin` 3, `emit`
`e.size + 1` (G167-06).

## 2. What was decided in October (Seyoon, 2026-10-12, "all four as recommended"), still binding

- **Option A:** the I/O indices are added to `Light.Exec` **in place**, with `o` (bits emitted) and
  `r` (coins consumed). `Light.Ends` keeps its type: `∃ σ' o r c, Exec … ∧ c ≤ T ∧ Q σ'`. So
  `Meets`, the 14 library routines and their proofs are untouched apart from witness lines.
- **The RAM is extended by a wrapper,** which is already done: `WordRAM.XInstr`. The compiler's code
  type becomes `List XInstr`, and the vendored segment lemmas over `Instr` apply through
  `XProgram.proj` and `XSteps.of_steps_proj` (tier 0, proved).
- `emit` appends "nonzero". The input is a new field of `Light.Limits`, which no vendored file
  constructs.

## 3. The signatures

October's mirror (`campaign/items/stage2/ExtensionsDraft.lean.txt` on the chapters 3–4 branch, 415
lines, elaborated then) states every new declaration over mirror types. In place they become:

| Mirror (October) | In place |
|---|---|
| `XStmt`: 7 constructors and 4 new | `Light.Stmt` gains `inBit`, `emit`, `coin`, `half` |
| `XLimits extends Limits` with `input` | `Light.Limits` gains the field `input : List Bool` |
| `XExec … σ σ' o r c` | `Light.Exec` gains the indices `o r`, and four rules |
| `XEnds` | `Light.Ends`, same type, with `∃ σ' o r c` |
| `XStmt.silent`, `XProgram.SilentSet`, `EndsIO.ofXEnds`, `MeetsIO.ofXMeets` | new, in `Light/IO.lean` (round 2, G167-01) |
| `EndsIO`, `MeetsIO`, the 13 `EndsIO.*` rules, `EndsIO.callLast` | new, in a new vendored-adjacent file `Light/IO.lean` |
| `XExec.det`, `coins_length_le`, `output_length_le` | new, in `Light/IO.lean` |
| `AcceptsND`, `acceptProb` | new, in a Complexity-side file (gate 10's auditor preferred that home) |
| `XFits` | removed (round 2, N2): `Fits` is unchanged; `|x| ≤ lim.word` is a separate hypothesis |
| `xcompileStmt` … `xcompileProgram_correct`, the deliverables | the in-place compiler (round 2, G167-02) |

**New since October:**
- **`Light/Renumber` (#381):** `Stmt.shift` gains four arms; `Exec.shift` gains four cases and
  the indices.
- **`Light/TMProc` (#382, job G in flight):** its statement uses only `Meets`, whose type is
  unchanged. Its proof is safe provided it reasons through `Ends` rules and does not invert `Exec`
  directly (§6, risk 1).
- **The deliverables** (round 2, after gate 167; Seyoon, 2026-11-18: "all three now"). The
  mirror `prog2/PROG2Mirror.lean.txt` states them over concrete compiler definitions:
  - `haltsWithin_compileProgram`: a Light run of the outermost call on `x` that emits `o` and
    consumes `r` makes the compiled program halt on `x`, on **every RAM stream that agrees with
    `r`** (past its end read as `false`), within `ramSteps P true c` steps, with the verdict
    "the result is positive", the output `o`, and the footprint `lowCell + lim.space`, which
    **does not grow with time**. Coin-free runs qualify for every stream.
  - `haltsWithin_of_streams`, `acceptsND_iff_haltsWithin`: Light halting on all streams of length
    `T` gives RAM halting on every stream, and nondeterministic acceptance transfers: the two
    hypotheses of `WordRAM.mem_NSPACE_of_accepts` (so `mem_NL_of_accepts`, with the constant
    footprint).
  - `acceptProb_eq_randProb`: acceptance probabilities transfer, for BPP consumers.
  - `polyTimeComputable_of_runs`: a Light program whose coin-free runs emit `g x` within
    polynomial Light cost computes a `PolyTimeComputable` `g`, **given** a length-dependent word
    size `W` with a `WordSizeComputable` witness and `TW n + W n` polynomial. Round 1 claimed this
    followed from polynomial cost alone, which is false: `Fits` gives only lower bounds on a
    sufficient word size, and a loop of `n` squarings forces `W` exponential (G167-04).
- **Lifting library routines** (G167-01): an `Ends` fact lifts to `EndsIO` for code that emits and
  consumes nothing and calls only into a **silent set** of procedures, a condition stable under
  appending and relocation, so `Light.Std`'s routines stay usable inside I/O programs.

## 4. The edit set (from October's `NOTES.md` §5, rechecked against today's tree)

- **`Stmt`, four new arms or cases each:**
  - `Syntax` (the type);
  - `Assigns` (`Stmt.assigns`);
  - `Rules` (`Ends.of_blockSafe`);
  - `Renumber` (`Stmt.shift`);
  - `Compiler/StatementCode` (`Stmt.size`, `compileStmt`, `length_compileStmt`, `Stmt.width`,
    four `Stmt.width_*_le_iff`);
  - `Compiler/Simulation` (four `codeAt_*`).
- **`Exec`, the indices and four rules:**
  - `Syntax` (the type);
  - `Logic` (`Exec.append`, `Ends`, and the rule proofs: about 22 witness lines);
  - `Rules` (8 witness lines, and 6 `cases` inversions, which keep working under Option A);
  - `Assigns` (`Exec.loc_eq_of_notMem_assigns`, plus 2 witness lines);
  - `RunsStayInLimits`:
    - `Exec.bounded`, with the new hypothesis `1 ≤ lim.word`, given by `Light.Std`;
    - `Exec.mem_outside`;
  - `Renumber` (`Exec.shift`);
  - `Compiler/Simulation` (`sim`: four new `sim_*`, with `o` and `r` threaded through `Start`,
    `Finished` and the nine existing `sim_*`);
  - `Compiler/WholeProgram` (`compileProgram_correct` restated, plus the theorem of §3).
- **Code type** (round 3, after gate 167's G167-02):
  - `compileStmt`, `bodiesCode` and `compileProgram` become `List XInstr`, as does the code field
    of `Setting`.
  - The straight-line code (`compileExpr`, `compileCond`, the call frames, the epilogue, the
    dispatcher, the start-up and verdict code) stays `List Instr`. It reaches the extended code
    through `XCodeAt.proj`; its runs lift by `XSteps.of_steps_proj` and
    `XStepsIn.of_stepsIn_proj`.
  - **Changed in `ProgramCode`** (round 4, after gate 167 round 3):
    - `mainCode` (the outermost statement's `compileStmt`, then `tailCode`) becomes
      `List XInstr`, with `tailCode` under `.base`;
    - the code-location lemmas (`codeAt_headCode`, `codeAt_mainStmt`, `codeAt_tailCode`,
      `codeAt_dispatcher_dispPos`, `codeAt_startCode`) are restated over the extended code;
    - so are `codeAt_bodiesCode` and `codeAt_bodies`: its `code` becomes an `XProgram`, with
      `XCodeAt` throughout. Its one caller is `WholeProgram`'s `bodyAt`.
  - **Unchanged in `ProgramCode`:** the layout definitions (`frameSize`, `mainPos`, `tailPos`,
    `firstBody`, `entries`, `endPos`, `dispPos`, `codeLayout`) and the `List Instr` parts
    (`headStraight`, `headCode`, `tailCode`, `poolCode`, `zeroCode`, `frameCode`,
    `startStraight`, `startCode`).
  - **Changed in `StartUp`:** `steps_start` is stated over `compileProgram`. It is restated over
    the projection, and as an extended run with its footprint (`xsteps_start` in the mirror).
    Its memory calculations stay.
  - `Dispatcher`, `Expressions`, `Conditions`, `CallFrames` and `Cells` are untouched.
- **The footprint** (round 3, G167-07): `Finished.run` becomes an `XStepsIn` run within the
  setting's cells.
  - The base-instruction lemmas keep their statements. H2 **adds** footprint companions beside
    them for the expression, condition, call-frame and dispatcher runs, with state-dependent
    address bounds for indirect loads and stores. `stepsIn_straight` exists; the start-up's is
    `xsteps_start`.
  - `Programs/WordRAM/Extended` gains `XStepsIn.mono` and `XStepsIn.trans`.
- **Mirror only:** `XStmt.ofStmt`, `XExec.ofExec` and `XSetting.xlim`. In place `Light.Limits`
  carries the input, so `xlim` is the setting's limits themselves (round 4, G167-05).
- **Vendored headers:** each edited file lists the change as a local modification. Rule 10 does
  not apply between vendored files (Seyoon, 2026-11-18).

Not affected: the `Expr`, `Cond` and `Op` inductions; `Lib`, `Frames` and `Calls`, which neither
match on `Stmt` or `Exec` nor destructure `Ends` witnesses (October's grep, to recheck).

## 5. Jobs

Definitions change in place, so a sorried statements PR cannot land first. Every exhaustive
proof must be extended in the same change. Instead:

0. **A statement gate first, on a mirror** (Codex audit). I update October's mirror to the list
   in §3, with the deliverable of §3 stated over a mirror compiler, and elaborate it as a scratch
   file. The gate audits the signatures before any vendored file changes.
1. **Job H1, the language core** (Codex, about 1,000–1,600 lines):
   - `Syntax`, `Logic`, `Rules`, `Assigns`, `RunsStayInLimits` and `Renumber`, in place;
   - the new `Light/IO.lean`: `EndsIO`, `MeetsIO`, the rules, `det`, and the length bounds.

   Its PR builds with the compiler's files still on `List Instr` and their four new
   `Stmt`/`Exec` cases left as `sorry`. That is a disclosed, temporary admission in vendored
   proofs, removed by H2.
2. **Job H2, the compiler** (Codex, about 1,800–3,000 lines with round 2's scope): the code type
   moves to `List XInstr`, with the four new `compileStmt` and `sim_*` cases, `sim` with streams,
   `compileProgram_correct` with the footprint, and the deliverables of §3, padding and
   probabilities included. Its gate checks that the vendored compiler is back to 0 admissions.
3. **(a4) and (b2) follow:** generic views and codecs as Light routines with `MeetsIO` specs, and
   `PolyTimeComputable g ⇒` a word-RAM program, from (b1) and this.

**Size:** about 2.8k–4.6k lines after round 2's scope (October's 1.4k–2.3k, the compiler cases,
streams, the footprint, and the padding and probability transfers).

## 6. Risks

1. **Job G** proves `Light.exists_tmProc` against today's `Exec`. If its proof inverts `Exec` or
   builds witnesses by hand, H1 breaks it. Either land G before H1 starts, or tell G now to reason
   only through `Ends`/`Meets` rules and the `light_*` tactics. **Recommendation: sequence H1
   after G lands** (H1 starts with the mirror gate anyway).
2. **Tier 2 jobs A–E** do not touch Light. No conflict.
3. **`Ends` hides coins existentially.** Specifications meant for every coin stream must use
   `EndsIO`. Crypto programs are coin-free (coins are read from the input), so this does not
   arise for them.
4. **Vendored drift:** after PROG-2, the Light files diverge from upstream beyond the
   module-syntax edits. Their headers list it. Upstream ports later must be merged by hand.

## 7. Decisions (Seyoon, 2026-11-18: "go with your recommendations")

Ruled: the process of §5, with a mirror statement gate (gate 167) first; H1 after job G lands;
`AcceptsND` and `acceptProb` stated in this round. The deliverable also needs `|x| ≤ lim.word`,
for the argument cell holding `|x|` (`Input.arg1_le`); the mirror carries it. The mirror is
`items/ram-tm/prog2/PROG2Mirror.lean.txt`. It elaborates with 0 errors and 27 sorried statements
(`mirror.log`).

### The decisions as posed

1. **The process of §5:** a mirror statement gate (Codex audit), then H1 and H2 in sequence, with
   H1's temporary compiler admissions. *Recommended.*
2. **Sequencing against job G:** H1 after G lands (*recommended*), or brief G now to avoid `Exec`
   inversions.
3. **`AcceptsND` and `acceptProb`:** state them in this round, as October did (*recommended*: they
   cost little and serve NL and BPP consumers), or defer them.

### Round 2 (gate 167 HOLD: 0/4/2)

Seyoon, 2026-11-18: H2's compiler theorem covers **all three** of the auditor's parts: coin
streams, a footprint independent of time, and the padding and probability interface. The
round-2 mirror answers G167-01 to G167-06 (`gates/167-prog2-statements/resolutions.md`).

### Round 3 (gate 167 round 2 HOLD: 0/1/3)

The mirror adds:
- `StartUp` to the edit set: `steps_start_proj`, `xsteps_start` and the `xcodeAt_*` lemmas
  (G167-02);
- complete readers for `silent`, `calls`, `xcells`, `xcellCount` and `xstoreLocal` (G167-05);
- the footprint inside the simulation contract (`XSetting.cells`, `XFinished.run` over
  `XStepsIn`, `xStepsIn_mono`, `xStepsIn_trans`; G167-07);
- the two remaining N8 checks (G167-08).

The H2 size estimate grows by the footprint versions of the segment lemmas, about 300–600
lines.
