# PROG-2 fill H1 (Codex): input, output and coins in the Light language core

Read `COMMON.md` (bundled). Its rules bind **except where this brief replaces them**: H1 edits
vendored definitions in place, so the statement freeze and the no-new-surface rule are replaced
by the frozen mirror below. **Fill name:** `fill-prog2-h1`. **Base:** the commit given in the
dispatch prompt, on `complexity/ram-simulation`.

## What this is

The light language gains four constructs, as the extended word RAM already has them:
`x := inBit e` (the input bit at position `e`, `0` off the input), `emit e` (append the bit
"`e ≠ 0`"), `x := coin` (the next coin) and `x := half e` (`⌊e / 2⌋`). `Light.Exec` gains two
indices, the bits emitted `o` and the coins consumed `r`. `Light.Ends` keeps its type, so `Meets`
and the library routines keep working. A new file `Light/IO.lean` holds the stream-aware logic.

The signatures are **frozen**. A statement gate on a mirror (gate 167) cleared them after three
rounds: `campaign/items/ram-tm/prog2/PROG2Mirror.lean.txt` (bundled, 1,311 lines). Its header
maps every mirror name to its in-place name. The design is `campaign/items/ram-tm/PROG2-DESIGN.md`
(bundled; §1–§4). Gate 167's findings and resolutions are bundled for context.

H1 is the **language core**. Job H2 follows with the compiler: it moves the code type to
`List XInstr` and proves the compiler's new cases and the deliverables. H1 leaves those cases
as disclosed admissions (below).

## Targets: what lands

Land every mirror declaration below under its in-place name, with the mirror's statement after
the renaming (`XStmt` ↦ `Light.Stmt`, `XExec` ↦ `Light.Exec`, `XEnds` ↦ `Light.Ends`,
`XLimits` ↦ `Light.Limits`, `XProgram` ↦ `Light.Program`, `XMeets` ↦ `Light.Meets`, and so on).
The mirror's line numbers are given for finding them.

1. **Syntax and semantics, in place** (`Light/Syntax.lean`): the four constructors of `Stmt`
   (134); the field `input : List Bool` of `Limits` (163); `inBitVal` and `inBitVal_eq`
   (169–172); `Exec` with the indices `o r` and the four new rules (180).
2. **The six inductions over `Exec`, in place** (219–330): `Exec.append` (`Logic`),
   `Exec.loc_eq_of_notMem_assigns` (`Assigns`), `Exec.bounded` with its new hypothesis
   `1 ≤ lim.word` and `Exec.mem_outside` (`RunsStayInLimits`); and, new in `Light/IO.lean`,
   `Exec.coins_length_le`, `Exec.output_length_le`, `Exec.det` and the four inversions
   `Exec.inBit_inv`, `emit_inv`, `coin_inv`, `half_inv`.
3. **The logic** (334–512): `Ends` redefined in place with the same type (`Logic`); new in
   `Light/IO.lean`: `EndsIO`, `MeetsIO`, their readers (`endsIO_iff`, `meetsIO_iff`), the
   rules `EndsIO.toEnds`, `mono`, `skip`, `set`, `store`, `seq`, `ite`, `whileStep`,
   `whileDone`, `call`, `inBit`, `emit`, `coin`, `half`, `EndsIO.callLast`, and `Ends.coin`.
   `xEnds_iff` and `xMeets_iff` land as new readers beside `Ends` and `Meets`
   in `Logic` (it has none today); name them `ends_iff` and `meets_iff`.
4. **Relocation, in place** (555–597, `Light/Renumber.lean`): `Stmt.shift` gains four arms and
   `Exec.shift` four cases and the indices. `XProgram.behind` is the existing
   `Program.behind`, unchanged.
5. **Lifting I/O-free code** (599–727, new in `Light/IO.lean`): `Stmt.silent`, `Stmt.calls`,
   their readers (`silent_seq` … `calls_leaf`), `Program.SilentSet` and `silentSet_iff`,
   `Exec.traces_nil`, `SilentSet.append`, `silent_shift`, `calls_shift`, `SilentSet.behind`,
   `EndsIO.ofEnds`, `MeetsIO.ofMeets`.
6. **Streams** (738): `EndsIO.take_iff`, in `Light/IO.lean`.
7. **Permanent checks** (1265–1293), as theorems in `Light/IO.lean`: `inBitVal_boundary`,
   `half_boundary`, `check_two_coins`, `check_det_length`, `check_bounded_needs_word`.

**Not in H1:**
- the mirror-only declarations `XStmt.ofStmt`, `XExec.ofExec` and `XSetting.xlim`;
- `xmainStmt` (it is the existing `Light.mainStmt`);
- `AcceptsND`, `acceptProb` and their readers, and `acceptProb_eq_of_le`: H2 lands them in a
  Complexity-side home;
- everything from line 753 on except the five checks above: the compiler, H2.

## Rules for this round (in place of COMMON rules 1 and 3)

- **Statements.** Every landed declaration's statement is the mirror's, after the renaming,
  byte for byte up to that renaming and whitespace. Every other existing statement stays
  byte-identical, except where the four new constructors or the two new indices force a change.
  Each forced change is listed in `REPORT.md` with its reason: an added match arm, the indices
  in an `Exec` hypothesis, or the new hypothesis of `Exec.bounded`. A mirror statement you
  believe false is an **E-STATEMENT** stop.
- **Public surface:** exactly the declarations above, plus pure `rfl`/`Iff.rfl` readers beside a
  definition in its home file. Everything else you add is `private`.
- **Owned files:**
  - in `TCSlib/Programs/Light/`: `Syntax`, `Logic`, `Rules`, `Assigns`, `RunsStayInLimits`,
    `Renumber`, and the new `IO.lean`;
  - **witness lines only** (no statement change) in `Calls`, `Frames`, `Regions`, `TMProc`
    and `Lib/*`, wherever the new indices reach an `Exec` witness or a `cases`;
  - **the compiler, minimally:** `Compiler/StatementCode`, `Compiler/Simulation` and
    `Compiler/WholeProgram`. In them, thread the indices through the existing proofs and give
    `Stmt.size` and `Stmt.width` their final values for the new arms (the mirror's table at
    lines 84–93 and `xcompileStmt`'s widths). The code type stays `List Instr`.
  - Keep each file under 600 lines; split `IO.lean` if needed (`Light/IO/*.lean`).
- **Temporary admissions, and only these:** the compiler cases for the four new constructors:
  `compileStmt`'s four new arms, and the four new cases of `length_compileStmt`, the
  `Simulation` lemmas and `sim`. H2 replaces them all. List every `sorry` site in `REPORT.md`.
  Nothing outside `Compiler/` may reach an admission.
- **Vendored headers.** Each edited vendored file's header gains a "Local modifications"
  bullet naming the change (the four constructs; the indices), in the style of the existing
  bullets. `IO.lean` is new: give it the repository's standard header, citing [AFM26] as the
  language it extends.
- **Rule 10.** Proofs between vendored files are exempt (Seyoon, 2026-11-18). `IO.lean` is a
  TCSlib file: it reads Light definitions through published equations and lemmas. Add a
  missing pure reader beside its definition in the home file.
- **Cite, do not re-prove.** `Ends`'s rules and the `light_*` tactics stay the route for
  I/O-free code; `EndsIO.ofEnds` lifts them. Do not copy an `Ends` rule's proof for its
  `EndsIO` twin: derive the twin from the rule, or factor a private helper.

## REPORT.md, in addition to COMMON's checklist

- **The landing table:** every target, its in-place name and file, and its statement's diff
  against the mirror's after renaming (it should be empty).
- **Forced changes:** every existing statement that changed, and why.
- **Admissions:** every `sorry` site, all within the compiler's new cases. Give an admission
  walk (types and values) for the IO roots `EndsIO.ofEnds`, `MeetsIO.ofMeets`, `Exec.det`,
  `EndsIO.take_iff` and `EndsIO.callLast` (empty), and for `Light.exists_tmProc` (empty).
- **The axiom prints** for every landed theorem.
- **The copy screen:** `scripts/copy-text-screen-v3.py` over your owned files, `Light/Logic`
  and `Light/Rules` included. Report every pair at or above half, with the reason it remains.
- **Size:** line counts per file, before and after.

## Downstream check

Every module that imports `TCSlib.Programs.Light.Syntax`, directly or not: the Light closure,
the compiler, `TMProc` and its users in `Complexity/RAMSimulation`. Each must elaborate with no
new error. Each must have no new admission outside the compiler's new cases.
