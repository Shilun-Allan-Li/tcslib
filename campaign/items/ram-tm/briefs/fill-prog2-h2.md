# PROG-2 fill H2 (Codex): the Light compiler with input, output and coins, and its deliverables

Read `COMMON.md` (bundled). Its rules bind **except where this brief replaces them**: H2 edits
vendored definitions in place, as H1 did. **Fill name:** `fill-prog2-h2`. **Base:** the commit
given in the dispatch prompt, on `complexity/ram-simulation`, with job H1 merged.

## What this is

Job H1 added `inBit`, `emit`, `coin` and `half` to the light language and the output and coin
indices to `Light.Exec`, and left the compiler's four new cases as disclosed admissions. H2
finishes the compiler, so that a Light program with input and output compiles to the extended
word RAM. It also proves the deliverables that connect Light to the complexity classes.

The signatures are **frozen** by gate 167's mirror:
`campaign/items/ram-tm/prog2/PROG2Mirror.lean.txt` (bundled). Its header gives the compiler's
type boundary: what moves to `List XInstr`, what stays `List Instr`, and the footprint. The design
is `campaign/items/ram-tm/PROG2-DESIGN.md` (bundled; §3–§5). H1's delivery report is bundled
for the landed names.

## Targets: what lands

Land every mirror declaration below under its in-place name, with the mirror's statement after
the renaming in the mirror's header and docstrings. Where a mirror docstring names its in-place
counterpart (`in place, …`), use that name. Otherwise drop the `x`/`X` prefix in the home
namespace, and list the name in `REPORT.md`'s landing table. Mirror line numbers are given for
finding them.

1. **The compiled statements** (753–851, `Compiler/StatementCode`): `xstoreLocal` and its reader,
   the four new arms of `compileStmt` (now `List XInstr`, old constructs under `.base`),
   `length_compileStmt`, and the four `Stmt.width_*_le_iff`.
2. **Code locations and the simulation** (853–965, `Compiler/Simulation`, and
   `Programs/WordRAM/Extended` for the two run lemmas): `XCodeAt`, its reader and `XCodeAt.proj`;
   `Setting` with the extended code field and `cells` (and `cells_eq`);
   `WordRAM.XStepsIn.mono` and `.trans`; `Start`, `Finished` (an `XStepsIn` run within the
   setting's cells, with the two traces), `Simulates`, and `sim` with all its cases, the four new
   ones included.
3. **Whole programs** (967–1150, `Compiler/ProgramCode`, `Compiler/StartUp`,
   `Compiler/WholeProgram`):
   - the layout (`frameSize` … `compileProgram`, now `List XInstr`), and `mainCode`;
   - the five code-location lemmas over the extended code, `codeAt_bodiesCode` and
     `codeAt_bodies` (the mirror's header, round 4, lists this migration);
   - `steps_start_proj` and `xsteps_start` (`StartUp`);
   - `startCost`, `ramSteps`, `stackCells`, `lowCell`, the cell interval and its count with
     their readers, `card_xcells`;
   - `Outcome` and `compileProgram_correct`.
4. **The deliverables** (1151–1261):
   - in `Compiler/WholeProgram`: `xstartState` and its reader, `haltsWithin_compileProgram`,
     `haltsWithin_of_streams`;
   - in the **new file `TCSlib/Complexity/RAMSimulation/LightIO.lean`**, namespace `Light`
     (Seyoon, 2026-11-19): `AcceptsND`, `acceptProb`, their readers (`acceptsND_iff`,
     `acceptProb_eq`), `acceptProb_eq_of_le`, `acceptsND_iff_haltsWithin`,
     `acceptProb_eq_randProb` and `polyTimeComputable_of_runs`. `xmainStmt` is the existing
     `Light.mainStmt`.
5. **Permanent checks** (1295–1311): `check_emit_vs_verdict`, `check_missing_entry`,
   `check_zero_depth`, in `LightIO.lean` or `Compiler/WholeProgram` (beside `mainStmt` and
   `verdictOf`'s users).

**Not landed:** the mirror-only declarations `XStmt.ofStmt`, `XExec.ofExec` and `XSetting.xlim`.

## Rules for this round (in place of COMMON rules 1 and 3)

- **Statements.** Every landed declaration's statement is the mirror's after the renaming. Every
  other existing statement stays byte-identical, except where the code type `List XInstr` forces
  a change; list each such change in `REPORT.md` with its reason. A mirror statement you believe
  false is an **E-STATEMENT** stop.
- **Public surface:** exactly the declarations above, plus pure `rfl`/`Iff.rfl` readers beside a
  definition in its home file, plus the **footprint companions** the mirror's header names. These
  are the expression, condition, call-frame and dispatcher runs as `XStepsIn` runs within a cell
  interval, with state-dependent address bounds for indirect loads and stores. Each companion
  sits beside the base lemma it extends and is listed in `REPORT.md`. Everything else is
  `private`.
- **Owned files:**
  - `TCSlib/Programs/Light/Compiler/*`;
  - `TCSlib/Programs/WordRAM/Extended.lean`: the two run lemmas and readers only;
  - the new `TCSlib/Complexity/RAMSimulation/LightIO.lean`, and its line in the `RAMSimulation`
    facade (imports and contents);
  - witness lines only, no statement change, anywhere else the code type reaches.

  Keep each file under 600 lines, and split a compiler file if needed (`Compiler/<Name>/*.lean`).
- **Admissions: none.** H1's temporary compiler admissions are all removed, and nothing in the
  Light closure, the compiler, `LightIO` or their users reaches an admission. The final-head
  admission walk must be empty for every root below.
- **Vendored headers.** Each edited vendored file's header gains a "Local modifications" bullet
  naming the change. `LightIO.lean` is a TCSlib file with the repository's standard header,
  citing [AFM26] and [AB09].
- **Rule 10.** Proofs between vendored files are exempt (Seyoon, 2026-11-18). `LightIO.lean` and
  `Programs/WordRAM/Extended.lean` are TCSlib files: they read other files' definitions through
  published equations, adding a pure reader beside a definition where one is missing.
- **Cite, do not re-prove.** The base segment lemmas over `List Instr` apply to the projection
  (`XCodeAt.proj`), and their runs lift by `WordRAM.XSteps.of_steps_proj` and
  `XStepsIn.of_stepsIn_proj`. Do not copy a base lemma's proof for its footprint companion: derive
  the companion from it, or factor a private helper. The transfers to the classes cite
  `WordRAM.mem_NSPACE_of_accepts`, `Randomized.randProb` lemmas and
  `WordRAM.polyTimeComputable_progOut`.

## REPORT.md, in addition to COMMON's checklist

- **The landing table:** every target, its in-place name and file, and its statement's diff
  against the mirror's after renaming (empty).
- **Forced changes** to existing statements, and the footprint companions, each with its base
  lemma.
- **The walk:** an admission walk (types and values) for `haltsWithin_compileProgram`,
  `haltsWithin_of_streams`, `acceptsND_iff_haltsWithin`, `acceptProb_eq_randProb`,
  `polyTimeComputable_of_runs`, `compileProgram_correct` and `Light.exists_tmProc` (all empty);
  and confirmation that H1's `sorry` sites are gone.
- **The axiom prints** for every landed theorem.
- **The copy screen:** `scripts/copy-text-screen-v3.py` over your owned files and the base
  compiler lemmas they extend. Report every pair at or above half, with the reason it remains.
- **Size:** line counts per file, before and after.

## Downstream check

Every module that imports `TCSlib.Programs.Light.Compiler.Simulation`, directly or not, and the
`RAMSimulation` facade with its users (`Simulation`, `Classes`). Each must elaborate with no
error and reach no admission.
