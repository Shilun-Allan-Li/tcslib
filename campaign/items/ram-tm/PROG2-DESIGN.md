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

These match the extended RAM's `rdIn`, `emit`, `coin` and `half` one for one, so each compiles to
one instruction after its expression.

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
| `EndsIO`, `MeetsIO`, the 13 `EndsIO.*` rules, `EndsIO.callLast` | new, in a new vendored-adjacent file `Light/IO.lean` |
| `XExec.det`, `coins_length_le`, `output_length_le` | new, in `Light/IO.lean` |
| `AcceptsND`, `acceptProb` | new, in a Complexity-side file (gate 10's auditor preferred that home) |
| `XFits` | not needed: `Input.arg1_le` already bounds `|x|` |

**New since October:**
- **`Light/Renumber` (#381):** `Stmt.shift` gains four arms; `Exec.shift` gains four cases and
  the indices.
- **`Light/TMProc` (#382, job G in flight):** its statement uses only `Meets`, whose type is
  unchanged. Its proof is safe provided it reasons through `Ends` rules and does not invert `Exec`
  directly (§6, risk 1).
- **The deliverable for the bridge**, which October did not state:

```lean
/-- (proposed) A Light program run on the input `x` (the input is `lim.input`, `|x|` is argument
1, argument 2 is `0`, memory `0`) that ends with output `o`, emits it from its compiled
extended-RAM program, which halts within `ramSteps P true c + 1` steps: a constant plus a constant times the Light run's cost.
`K₀` and `K₁` depend on the program text only, as `startCost` and `stepsPerStep` do. -/
theorem Light.Compiler.haltsWithin_compileProgram {W : ℕ} {lim : Limits} {P : Program} {p0 : ℕ}
    {x o : List Bool} {σ' : State} {c : ℕ}
    (hx : lim.input = x)
    (h : Exec lim P 0 (mainStmt p0) ⟨frame [0, x.length, 0], fun _ => 0⟩ σ' o [] c)
    (hfit : Fits W lim (dispPos P true) (stackCells P lim)) :
    ∃ t, t ≤ ramSteps P true c + 1 ∧
      WordRAM.HaltsWithin (compileProgram P p0 true) x [] W t (decide (0 < σ'.loc 0)) o (3 * t)
```

With `progOut_eq` this gives `WordRAM.progOut (compileProgram P p0 true) (fun _ => W) x = o`.
With `polyTimeComputable_progOut`, a Light program that halts within a polynomial cost on every
input computes a `PolyTimeComputable` function.

- **Why `HaltsWithin` directly.** The compiler's proof (`compileProgram_correct`) already
  composes `Steps` runs (`steps_start`, `sim`, `steps_tail`) before converting to `exec`. Stated
  at the `XSteps`/`HaltsWithin` level, it needs no converse from `exec` back to `Steps`.
- **The footprint** `3·t` is `HaltsWithin.touches_le` (tier 0). The word size `W` is the
  caller's, and `Fits` constrains it.

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
- **Code type:** `List Instr` becomes `List XInstr` in `ProgramCode`, `StartUp`, `Dispatcher`,
  `StatementCode`, `Simulation` and `WholeProgram`. The straight-line segment lemmas transport
  through `XProgram.proj`.
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
2. **Job H2, the compiler** (Codex, about 1,200–2,000 lines): the code type moves to
   `List XInstr`, with the four new `compileStmt` and `sim_*` cases, `compileProgram_correct` with
   the indices, and the deliverable of §3. Its gate checks that the vendored compiler is back to 0
   admissions.
3. **(a4) and (b2) follow:** generic views and codecs as Light routines with `MeetsIO` specs, and
   `PolyTimeComputable g ⇒` a word-RAM program, from (b1) and this.

**Size:** about 2.2k–3.6k lines, close to October's 1.4k–2.3k plus the compiler cases.

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

## 7. Decisions for Seyoon

1. **The process of §5:** a mirror statement gate (Codex audit), then H1 and H2 in sequence, with
   H1's temporary compiler admissions. *Recommended.*
2. **Sequencing against job G:** H1 after G lands (*recommended*), or brief G now to avoid `Exec`
   inversions.
3. **`AcceptsND` and `acceptProb`:** state them in this round, as October did (*recommended*: they
   cost little and serve NL and BPP consumers), or defer them.
