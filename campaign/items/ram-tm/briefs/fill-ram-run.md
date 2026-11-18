# RAM fill (Codex), tier 2 job E: the simulation (`Simulation`, the 2 targets)

Read `COMMON.md` (bundled), its tier 2 addendum included; its rules bind. **Fill name:**
`fill-ram-run`. **Base:** the commit given in the dispatch prompt, on
`complexity/ram-simulation`.

## What this is

`TCSlib/Complexity/RAMSimulation/Simulation.lean` states stage 2: a program `P` of the extended
word RAM is simulated by one `FinTM Bool` (`WordRAM.exists_simulation`) and by one `FinNDTM Bool`
(`WordRAM.exists_ndSimulation`), within `simTime` steps and `simSpace` cells. The statements
were gated on 2026-10-14 and are frozen. **This job proves both**, from the interfaces of
PR #372:
- `WordRAM.Sim.exists_startup` (job C);
- `WordRAM.Sim.exists_phase` and `WordRAM.Sim.exists_verdictPhase` (job D).

They are sorried at your base and cited as stated. Once jobs A–D land, the two targets and the
nine class corollaries of `RAMSimulation/Classes` are unconditional.

## The argument

Gate 162's pack, "How the interfaces give the frozen bounds", gives it, and the auditor checked
it (G162-23). In outline:

1. **The machine.**
   - **Phases.** Choose `a` from `P`, larger than the bit length of every address written in `P`,
     so `ImmBound a ins` for every instruction. Index the phases by (position `p ≤ |P|`,
     parity). Position `|P|` is the "past the end" phase, which rejects.
   - **Dispatch.** A phase at `p` with exit `next` redirects to `p + 1`, and with `jump` to
     `jumpTarget ins`; targets past `|P|` go to `|P|`. Every redirect flips the parity, so a
     `bltz` to its own position never redirects a phase to itself (`Contract.inPhase` needs
     `q.1 ≠ p`). Verdict phases halt, through `Turing.phaseHostTM_run_le`.
   - **Embedding.** The start-up machine has `8 + k'` tapes. Place each eight-tape phase on its
     first eight tapes. Deterministic phases use `Turing.embedEmitTM` with `Fin.castAddEmb k'`.
     For nondeterministic ones, form the `NDTM` whose transition under `b` is that of
     `embedEmitTM σ (N.fixChoice b)`; its `fixChoice b` is then the embedded deterministic
     machine. Prove `Encodes` transport through the embedding once (`Cfg.select`,
     `embedEmitCfg_*`).
   - **The host.** Use `Turing.NDTM.phaseHostND` (`Build/NDHost`) over the start-up and the
     phases. `phaseHostND_fixChoice` makes its `fixChoice b` the deterministic `phaseHostTM` of
     the phases' `fixChoice b`.
2. **The master induction**, on the `XStepsIn` run of `HaltsWithin` (readers
   `WordRAM.XStepsIn.succ_iff`, `haltsWithin_iff`). Take a choice word `w` and the stream `ρ` of
   its bits at the coin phases' entries. After the start-up and `i` phases, the configuration
   encodes the `i`-th RAM configuration, over the cells `T_i = {-1} ∪` those touched so far, so
   `|T_i| ≤ f + 1`.
   - **Coin phases.** Take the entry's choice explicitly (G162-21).
   - **Everything else.** Transitions agree and the entry is never re-entered, so each slice runs
     deterministically: `Turing.NDTM.runWith_eq_fixChoice_runFrom` and
     `spaceUsedWith_eq_fixChoice_spaceUsed` (`Nondeterministic`, `NondeterministicSpace`). The
     NL compiler's `Complexity.LogProg.ndtm_runWith_eq_runFrom`
     (`SpaceComplexity/Machines/NARMCompile`) is a worked precedent of this shape.
3. **The bounds.**
   - **Time:**
     - the start-up takes at most `TW n + C₀·(n + W² + 1)` steps;
     - each phase takes at most `C₁·((f + 2)·(W + 1) + W² + n + 1)`, plus one dispatch step;
     - with `t ≥ 1` (`HaltsWithin` has `n < t`), the total is at most `simTime`
       (`WordRAM.simTime_eq`).
   - **Space:**
     - the start-up visits at most `SW n + C₀·(W + |bits n| + 1)` cells;
     - afterwards each of the eight tapes stays within its origin
       `± C₁·((f + 2)·(W + 1) + |bits n| + 1)`;
     - the extra tapes never move;
     - with `|bits n| ≤ logSpace n` (`Complexity.logSpace_eq`), the total is at most `simSpace`.
   - Use `Turing.MultiTapeTM.spaceUsedByTape_le_card_Icc`, and for branches
     `Complexity.LogProg.spaceUsedWith_le_of_ranges`. After the halt,
     `ComputesInTime.spaceUsed_le_of_halt` and `spaceUsedWith_append_of_halt` hold the bound.
4. **The targets.**
   - **`exists_simulation`:** `M = N.fixChoice false`. Its runs are those of the all-`false` word,
     whose stream reads like `ρ = []`: every `ρ.getD k false` is `false`. In verdict mode the
     output is `[v]` (`exists_verdictPhase`); in function mode it is `c.out`.
   - **`exists_ndSimulation`:**
     - every branch of length `T` is the run of some stream, so the uniform hypothesis bounds it
       and it halts;
     - an accepting stream gives an accepting branch, with its bits at the coin entries, padded;
     - an accepting branch gives a stream whose run accepts, by `WordRAM.HaltsWithin.unique`.

## Owned files

- `TCSlib/Complexity/RAMSimulation/Simulation.lean`: the two targets' bodies and sketches, and the
  module docstring. Repair its stale line references here: `phaseHostTM` is at `Seam.lean:886`,
  `exists_inputSeekTM` at `InputCall.lean:291`, `embedSilentTM` at `Embed.lean:253`. Better, name
  declarations instead of lines. Drop "proofs pending" when both are proved.
- **New files** under `TCSlib/Complexity/RAMSimulation/Sim/`, named `Run*.lean` (for example
  `RunHost.lean` for the host and embedding, and `RunInduction.lean` for the induction). Their
  declarations are public in `WordRAM.Sim`, per the tier 2 addendum. `Simulation.lean` imports
  them. Add each to the `RAMSimulation.lean` facade's imports and contents: you may edit the
  facade for that only.

## Admitted dependencies allowed

`WordRAM.Sim.exists_startup`, `WordRAM.Sim.exists_phase` and `WordRAM.Sim.exists_verdictPhase`,
which in turn reach jobs A–C's statements; those may appear in the walk too. Nothing else, and in
particular nothing from `Build/RecordTable`.

## Downstream check

`RAMSimulation/Classes` and the facades. With this job, `Classes`' nine corollaries reach only
tier 2's statements.
