# RP-1: exhaustive rule-10 check (gate evidence)

Branch `lean/dedup-rp1`, worktree `/home/user/tcslib-scratch/wt-rp1`, base `4c7dffce`, commit
`f200144b`. The probes were run on 2026-11-06 with
`devtools/seyoon/leanelab.sh <wt-hk> /home/user/tcslib-scratch/oleans-lnth <probe>`. They ran one
at a time, and no `lake` command was used.

## Method

Rule 10: no proof outside a definition's home file reads it by unfolding or by definitional
equality. The check makes each sealed definition `irreducible` in a copy of every module that can
see it, then elaborates the copy. Any proof that still reads the body fails to elaborate. That
covers `exact h` across the definition, `cases`/`rcases`/`rintro` on it, anonymous constructors and
`Or.inl`/`Or.inr` built against it, and `show`/`change` through it. Explicit `simp [Def]` or
`rw [Def]` unfolds use equation lemmas and still work under `irreducible`, so those were found by
grep and re-pointed separately; the commit has none left. The published `Iff.rfl` equations live in
the home files, which are already compiled, so a proof that goes through them passes.

## The seven sealed definitions

| Definition | Home file | Equation(s) |
|---|---|---|
| `Complexity.WalkLe` | `Logspace/PathWalk` | `walkLe_zero_iff`, `walkLe_succ_iff_head` |
| `Complexity.Codec.StepRel` | `Codec/Bridge` | `stepRel_iff_mem` |
| `Complexity.ExpBFS.RCode` | `ExpBFS/Radius` | `rcode_iff_reflTransGen` |
| `Complexity.ExpBFS.WinRun` | `ExpBFS/Radius` | `winRun_iff` |
| `Complexity.LogProg.SavitchARM.Rel` | `SavitchARM/Recursion` | `rel_iff_orc` |
| `Complexity.LogProg.SavitchARM.InitO` | `SavitchARM/Search` | `initO_iff_orc` |
| `Complexity.LogProg.SavitchARM.AccO` | `SavitchARM/Search` | `accO_iff_orc` |

## How the 52 probe copies were generated

The generator is `mkprobes.py.txt`.

1. **Choosing the modules.** I built the import graph of `TCSlib/` from each file's `import`
   lines. The copies cover every module that imports at least one of the five home files, directly
   or through other modules. That is 49 modules. Three home files are probed as well, because each
   also uses definitions homed elsewhere:
   - `ExpBFS/Radius`, with `StepRel` sealed;
   - `SavitchARM/Search`, with `WalkLe`, `StepRel` and `Rel` sealed;
   - `SavitchARM/Recursion`, with `WalkLe` and `StepRel` sealed.

   Total: 52 copies.
2. **Choosing what to seal.** Each copy seals only the definitions whose home file it imports.
   A definition homed in the module itself is never sealed in that module's copy.
3. **Building each copy.**
   - The copy is the module's source as committed. The exception is `SavitchARM/Reach`, which was
     first probed before its fix and then regenerated and probed again after it.
   - Every `set_option maxHeartbeats` value that is `0` or above 400000 is set to `400000`.
   - After the last `import` line, the generator inserts `set_option maxHeartbeats 400000` and one
     `attribute [local irreducible] <name>` line per sealed definition. `example-header.lean.txt`
     shows this block for `ISCountGenWalk`.
   - Copies are written to `/home/user/tcslib-scratch/wt-hk/rvprobe/rp1/`.

**Excluded home files.** Two home files are not probed: `Logspace/PathWalk` and `Codec/Bridge`.
Neither imports any other home file, directly or indirectly (checked against the same import
graph), so there is nothing to seal in them. This is two files, not three. The other three home
files are probed as described in step 1.

**State of the tree when probed.** The probes ran on the working tree after all re-points except
`SavitchARM/Reach`'s. That tree is identical to commit `f200144b` apart from `Reach`. `Reach` was
then fixed, regenerated and probed again: the "after fix" row below. `probes.out` holds each probe's
full output, under a header line `== <module> exit=N`.

## Results

53 runs: 52 modules, plus `Reach` a second time after its fix. In the final state all 52 modules
exit 0 with no errors. Only one probe ever failed: `Reach` before its fix, with one error at
`mem_iff_reach` (line 293 of the real file, line 296 of the copy). There, `hstep`, a `stepLang`
membership, was passed where `∀ j < t, StepRel N x s (c j) (c (j + 1))` is expected. The fix wraps
it as `fun j hj => stepRel_iff_mem.mpr (hstep j hj)`. Error counts are lines matching `: error`. The
non-error output is 22 `sorry` warnings: 21 in `ClassPSPACE.TQBF` and one in
`SpaceComplexity.Savitch` (`savitch`, sorried at that base; #208 later proved it). The merged-head
replay (`replay-lrp3`) has only the 21 (corrected after gate 107's minor 2).

| Module | Sealed definitions | Exit code | Errors |
|---|---|---|---|
| `TCSlib.Complexity.ClassPSPACE` | 1 | 0 | 0 |
| `TCSlib.Complexity.ClassPSPACE.TQBF` | 1 | 0 | 0 |
| `TCSlib.Complexity.ClassPSPACE.TQBFHard` | 1 | 0 | 0 |
| `TCSlib.Complexity.ClassPSPACE.TQBFHardBridge` | 1 | 0 | 0 |
| `TCSlib.Complexity.ClassPSPACE.TQBFHardMachine` | 1 | 0 | 0 |
| `TCSlib.Complexity.ClassPSPACE.TQBFHardParams` | 1 | 0 | 0 |
| `TCSlib.Complexity.ClassPSPACE.TQBFHardVerifier` | 1 | 0 | 0 |
| `TCSlib.Complexity.Randomized` | 4 | 0 | 0 |
| `TCSlib.Complexity.Randomized.BPLInP` | 3 | 0 | 0 |
| `TCSlib.Complexity.Randomized.BPLInPCount` | 3 | 0 | 0 |
| `TCSlib.Complexity.Randomized.Space` | 3 | 0 | 0 |
| `TCSlib.Complexity.Randomized.SpaceAmplifyPoly` | 3 | 0 | 0 |
| `TCSlib.Complexity.Randomized.SpaceAmplifyPolyCode` | 3 | 0 | 0 |
| `TCSlib.Complexity.Randomized.SpaceAmplifyPolyMachine` | 3 | 0 | 0 |
| `TCSlib.Complexity.Randomized.SpaceAmplifyPolyRun` | 3 | 0 | 0 |
| `TCSlib.Complexity.Randomized.UPath` | 2 | 0 | 0 |
| `TCSlib.Complexity.Randomized.UPathLoops` | 2 | 0 | 0 |
| `TCSlib.Complexity.Randomized.UPathMachine` | 2 | 0 | 0 |
| `TCSlib.Complexity.Randomized.UPathParse` | 2 | 0 | 0 |
| `TCSlib.Complexity.Randomized.UPathRL` | 4 | 0 | 0 |
| `TCSlib.Complexity.Randomized.UPathSearch` | 2 | 0 | 0 |
| `TCSlib.Complexity.Randomized.UPathWalk` | 2 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity` | 7 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.ExpBFS.Main` | 3 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.ExpBFS.Radius` | 1 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.ExpTime` | 3 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.Logspace.ISCountGenCorrect` | 7 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.Logspace.ISCountGenLoop` | 5 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.Logspace.ISCountGenMachine` | 5 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.Logspace.ISCountGenRadius` | 4 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.Logspace.ISCountGenStage` | 5 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.Logspace.ISCountGenWalk` | 5 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.Logspace.ISCountMath` | 1 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.Logspace.ISCountRegs` | 5 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.Logspace.ImmermanSzelepcsenyi` | 7 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.Logspace.Path` | 2 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.Logspace.PathHard` | 2 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.Logspace.PathHardDecide` | 2 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.Logspace.PathHardMachine` | 2 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.Logspace.PathHardRegs` | 2 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.Logspace.PathHardRun` | 2 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.Logspace.PathHardWalk` | 2 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.Logspace.PathWalkMachine` | 1 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.Logspace.PathWalkProof` | 1 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.Machines.NARMLogspace` | 3 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.Savitch` | 5 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.SavitchARM.Correct` | 5 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.SavitchARM.Reach (before fix)` | 2 | 1 | 1 |
| `TCSlib.Complexity.SpaceComplexity.SavitchARM.Reach (after fix)` | 2 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.SavitchARM.Recursion` | 2 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.SavitchARM.Search` | 3 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.SavitchARM.Setup` | 3 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.SavitchARM.Window` | 4 | 0 | 0 |

## Sanity probe (`zz_sanity.lean.txt`, output `zz_sanity.out`)

The sanity probe checks that sealing actually catches reads. It imports `Logspace.PathWalk` and
`SavitchARM.Search` and seals `WalkLe`, `StepRel` and `Rel`. It then states four `example`s: three
are planted definitional reads and one goes through an equation. **Result: exit 1 with exactly
three errors, one on each planted read; the equation example passes.**

| Line | Planted read | Result |
|---|---|---|
| 9 | `exact h` from `WalkLe E n 0 c t` to `c = t` | error: Type mismatch |
| 11 | `rcases h` on `WalkLe E n 1 c t` | error: `rcases` failed, "is not an inductive datatype" |
| 17 | `exact h` from `Rel orc x s u v` to `orc 3 (…) = true` | error: Type mismatch |
| 19–20 | `walkLe_zero_iff.mp h` (control) | no error |
