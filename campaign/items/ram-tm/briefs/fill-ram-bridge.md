# RAM fill (Codex), bridge job F: polynomial-time functions from programs (4 admissions, 2 files)

Read `COMMON.md` (bundled), its tier 2 addendum included; its rules bind, the reader rule among
them. **Fill name:** `fill-ram-bridge`. **Base:** the commit given in the dispatch prompt: PR #379's
head, branch `ram/bridge-statements`.

## What this is

The first wave of the bridge from word-RAM programs to the library's polynomial-time functions,
for the cryptography campaign. Programs written for the word RAM become `PolyTimeComputable`
functions through stage 2's simulation. PR #379 states four results. **This job proves them:**

1. `WordRAM.wordSizeComputable_of_timeConstructible` (`RAMSimulation/WordSize`): a
   time-constructible `T` is a word size computable within `a·(T n + 1)` steps and cells.
2. `WordRAM.wordSizeComputable_poly` (`RAMSimulation/WordSize`): `n ↦ C·(n+1)^(c+1)`, for `C > 0`,
   within `a·(n+1)^(c+1)`.
3. `WordRAM.polyTimeComputable_of_computes` (`RAMSimulation/Classes`): a program that emits `g x`
   on every input within `C·(|x|+1)^d` steps, with `TW n + W n ≤ C·(n+1)^d`, makes `g`
   `Complexity.PolyTimeComputable`.
4. `WordRAM.polyTimeComputable_progOut` (`RAMSimulation/Classes`): the same for `progOut P W`, from
   halting alone.

Each has a proof sketch.

## Route

- **Target 1:**
  - `Complexity.timeConstructible_iff` gives `c > 0` and a machine writing `(T |x|).bits` within
    `c·(T |x| + 1)` steps;
  - space: `Turing.MultiTapeTM.spaceUsed_le_mul_succ` (`TuringMachine/Finite`), at most
    `k·(t + 1)` cells;
  - take `a = (k + 1)·(c + 1)` or similar; `WordSizeComputable` is in the same file and may be
    unfolded.
- **Target 2:** target 1 at `Complexity.timeConstructible_poly C c hC`
  (`ClassP/TimeConstructiblePoly`), then `WordSizeComputable.mono` with
  `C·(n+1)^(c+1) + 1 ≤ (C + 1)·(n+1)^(c+1)`.
- **Target 3:** follow `mem_P_of_decides`'s proof in the same file, in function mode.
  - **The machine:** `exists_simulation P true hW`, read through `outputOf_true` and
    `simTime_eq`.
  - **The bounds:** `HaltsWithin.touches_le` and `HaltsWithin.mono` give `C·(n+1)^d` steps and
    `3·C·(n+1)^d` cells.
  - **The arithmetic:** the existing private `polynomial_time_bound` bounds the deadline by
    `(A + 1)·a·(n+1)^(3d+1)`.
  - **Packaging:** `Turing.FinTM.ComputesInTime.mono` enlarges each run's deadline, and
    `Complexity.polyTimeComputable_iff` and `Turing.FinTM.computesFunInTime_iff` package the
    machine.
- **Target 4:** target 3 with `g := progOut P W`. `WordRAM.progOut_eq` (`Programs/WordRAM/Output`)
  turns each halting run's output into `progOut P W x`.

## Owned files

- `TCSlib/Complexity/RAMSimulation/WordSize.lean`: targets 1 and 2.
- `TCSlib/Complexity/RAMSimulation/Classes.lean`: targets 3 and 4.

Statements byte-identical. Private helpers in each file; factor any arithmetic shared by targets 3
and 4, or with `mem_P_of_decides`, rather than copying it.

## Admitted dependencies allowed

`WordRAM.exists_simulation`, for targets 3 and 4 only, and whatever it reaches. Targets 1 and 2
reach no admission.

## Downstream check

The `RAMSimulation` facade.
