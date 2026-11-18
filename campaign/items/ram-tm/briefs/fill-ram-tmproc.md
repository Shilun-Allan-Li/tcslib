# RAM fill (Codex), bridge job G: a Turing machine as a Light procedure (`Light/TMProc`, 1 admission)

Read `COMMON.md` (bundled), its tier 2 addendum included; its rules bind, the reader rule among
them. **Fill name:** `fill-ram-tmproc`. **Base:** the commit given in the dispatch prompt: PR #382's
head, branch `ram/tmproc-statement`.

## What this is

`TCSlib/Programs/Light/TMProc.lean` states `Light.exists_tmProc`. For every finite binary Turing
machine `M` there is a Light program `Q` with a procedure that runs `M` on a bit string in memory,
writes `M`'s output to memory, and returns its length, within `A·(t + len + 1)` steps. It is
specified by `Meets` wherever `Q` is placed (`Program.behind Pre Q ++ Post`). **This job proves
it.** It is the reverse of stage 2: Light programs, and through them word-RAM programs, can call any
polynomial-time function given only by a machine. It reaches no admission.

## Route

Read the statement's proof sketch, and the vendored Light layer it builds on:
- `Light/Syntax`: `Stmt`, `Expr`, `Exec`, `Limits`;
- `Light/Logic`, `Rules`, `Calls`, `Frames`, `Regions`: `Ends`, its rules, `Meets`, `SameOutside2`;
- `Light/Tactics`: `light_keep`, `light_time`, `light_side` and the rest;
- `Light/Lib`: worked procedures with loops and their specifications. `Copy.lean` and `Pass.lean`
  are short models of a loop proved with `Ends`.

**The encoding.**
- **State and symbols.** The state is a number, by `Fintype.equivFin` on `M.State`. Cells hold `0`
  for blank and `1`, `2` for `false`, `true`.
- **Tapes.** Lay out each work tape in the scratch region so that the cells reachable in `t` steps
  occupy `O(M.k·(t + 1))` cells with no bound known in advance: cell `z` of tape `j` at
  `sc + c₀ + ((2|z| + [z < 0])·M.k + j)`, after a constant header `c₀`.
- **Input.** The input head reads `x` at `a` in place. Its position runs from `0` to `len + 1`,
  with `Turing.Cfg`'s shift by one.

**One step.** Two routes; choose one and say which in the report.
- **A table.** A prologue writes `M`'s transition table into the header, generated from
  `M.tm.tr` over the finite domain. One generic interpreter loop is then proved once.
- **Code branches.** A finite case split per `(state, scanned symbols)`, generated from `M`.

The table route is recommended: one invariant, one loop.

**The invariant.** After `i` iterations, the memory and locals encode
`M.tm.runFrom (M.tm.initCfg x) i`: the state, the work tapes' cells, the heads, the input head,
and the output written so far at `b`. Read `Turing.Cfg`, `MultiTapeTM.step` and `runFrom` through
their published readers (`Configuration`, `Deterministic`, `Finite`; for instance `runFrom_one`,
`step_of_some`, `Cfg.init`'s equations). Use the reader rule for any missing one.

**Termination and time.** `M.ComputesInTime x out t` gives a halt by time `t` with output exactly
`out` (`Turing.FinTM.computesInTime_iff`). Each iteration costs `O_M(1)` Light steps, and the setup
costs `O(len)` plus the prologue.

**Placement.** Prove the specification for `Q` itself, then carry it to
`Program.behind Pre Q ++ Post` by `Ends.shift_append` (`Light/Renumber`).

## Owned file

`TCSlib/Programs/Light/TMProc.lean`: the statement byte-identical. The program, its procedures
and all helpers are `private` in this file; a public definition of `Q` is not needed. If the file
passes about 1,500 lines, keep going and say so: the maintainer splits it at landing. You may add
imports of existing `TCSlib/Programs/Light/*` and `TCSlib/Complexity/TuringMachine/*` modules, each
listed in `REPORT.md` with its reason.

Rule 10 applies to this file, which is not vendored. It reads Light's definitions through their
rules and lemmas, as the vendored `Lib` procedures do, and `Turing`'s through their readers.

## Admitted dependencies allowed

None.

## Downstream check

The `TCSlib/Programs/Light.lean` facade.
