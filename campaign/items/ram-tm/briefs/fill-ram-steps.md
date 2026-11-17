# RAM fill (Codex): tier 0, the extended word RAM's run calculus (`Programs/WordRAM/Extended`, 18 admissions)

Read `COMMON.md` (bundled) first; its rules bind. **Fill name:** `fill-ram-steps`.
**Base:** the commit given in the dispatch prompt. It is the head of PR #370 (branch
`ram/readers`, into `complexity/ram-simulation`), which adds the readers this fill needs. This
replaces `COMMON.md`'s base rule for this fill only (Seyoon, 2026-11-17: dispatch before #370
merges). The maintainer lands your delivery on the RAM branch after #370 merges.

## What this is

`TCSlib/Programs/WordRAM/Extended.lean` extends the word RAM of [AFM26] by input, output, coins
and halving. It defines runs (`XSteps`), footprints (`StepsIn`, `XStepsIn`) and halting within
steps and cells (`HaltsWithin`). Its 18 results were stated on 2026-10-13 and gated with stage 2
on 2026-10-14, and they are frozen. Stage 2's simulation and its class corollaries rest on them,
so they come first. Seyoon added this tier on 2026-11-17, after gate 160 found that tier 3 needs
`HaltsWithin.mono` and `HaltsWithin.touches_le`. **This fill proves all 18.**

## Targets (in `WordRAM`, all in the owned file, in file order)

- `XSteps.trans`
- `xstep_map_base`
- `XSteps.of_steps`
- `XSteps.of_steps_proj`
- `XInstr.card_touches_le`
- `StepsIn.toSteps`
- `Steps.exists_stepsIn`
- `StepsIn.mono`
- `StepsIn.trans`
- `StepsIn.agreeOutside`
- `stepsIn_straight`
- `XStepsIn.toXSteps`
- `XSteps.exists_xStepsIn`
- `XStepsIn.of_stepsIn_proj`
- `HaltsWithin.mono`
- `HaltsWithin.touches_le`
- `HaltsWithin.unique`
- `HaltsWithin.coin_irrel`

Each has a proof sketch. Most are inductions on the run length, generalizing the start
configuration, as their sketches say. Several cite the vendored calculus of
`Programs/WordRAM/Steps.lean` (`WordRAM.Steps.trans`, `WordRAM.steps_straight`) by analogy.
Cite those lemmas where they apply, rather than redoing their inductions.

## Notes on the route

- **Same file, other file.** `XSteps`, `xstep`, `StepsIn`, `XStepsIn`, `XInstr.touches`,
  `baseTouches`, `XProgram.proj`, `initMem`, `XCfg.init` and `HaltsWithin` are defined in the
  owned file, so you may unfold them.
- **Vendored definitions** in `Programs/WordRAM/Basic.lean` and `Steps.lean` are read only
  through their published equations. PR #370, which is your base, adds the four you need
  to `Steps.lean`:
  - `WordRAM.step_def`: `step P c` as its `match` on the instruction at `c.pc`;
  - `WordRAM.effect_def`: `effect i m` as its `match`;
  - `WordRAM.Steps.zero_iff` and `WordRAM.Steps.succ_iff`: the two cases of `Steps`.

  Also use the existing `Steps.refl`, `Steps.trans`, `steps_straight`, `effects_nil` and
  `effects_cons`, the `step_accept`/`step_reject` verdict lemmas, and `Cfg`'s structure fields.
  Any other missing equation is an E-READER stop. Report it; do not unfold.
- **`xstep` is a `match` on `P.getD c.pc (.base .reject)`.** For `xstep_map_base` and
  `XSteps.of_steps_proj`, case on the instruction at `pc` once, in a private helper. Do not
  repeat the case analysis in each theorem.
- **Footprints:** `XInstr.card_touches_le` says each instruction touches at most three cells.
  `XSteps.exists_xStepsIn` and `HaltsWithin.touches_le` build the union footprint of `n` steps,
  of size at most `3 n`. `HaltsWithin` counts the `n < t` steps before the verdict, so the
  bound is `3 n ≤ 3 t`.
- **`HaltsWithin.unique`:** `xstep` is a function, so two runs from the same configuration agree
  up to the shorter length. One of them gives a verdict there, and the other cannot step past a
  verdict.
- **`HaltsWithin.coin_irrel`:** `xstep` reads `ρ` only at `coin`. Induction on the run, with
  `CoinFree` ruling out that case.

## Owned file (modify this and nothing else)

`TCSlib/Programs/WordRAM/Extended.lean`.
- No import changes. Statements stay byte-identical.
- Private helpers go under a section header, before their first use.
- When all 18 are proved, change the module docstring's "proofs pending" to say that they are
  proved, and drop the campaign labels from the proof sketches you rewrite (`COMMON.md`, rule 5).

## Downstream check

`RAMSimulation/Simulation` imports this file (through its own imports), and so do
`RAMSimulation/Classes`, `RAMSimulation/WordSize`'s consumers and the facade
`TCSlib/Complexity/RAMSimulation.lean`. Elaborate all of them, and any other module under
`TCSlib/Programs/` that imports this file.

## Order and frontier

Prove in file order. The `HaltsWithin` group at the end uses the run and footprint lemmas
before it. Tier 3 needs `HaltsWithin.mono` and `HaltsWithin.touches_le`, so if you stop early,
prefer a frontier that includes them. Checkpoint zips are welcome.
