<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMSim.lean :: Complexity.LogProg.sim_call -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Step Effect of an Oracle Call

**Claim.** When the instruction at $l$ calls decider $j$ in mode $\mu$ with arguments $R$, one step from the start-phase configuration with register values $v$ preserves the registers, input-head position, and output, and moves to the start-phase state selected by the oracle’s answer on the associated virtual input.

**Proof.** The run for one step is exactly the single-step transition (`rrun_one`). The compiled program’s call at $(l,\mathrm{start})$ is the call specified by the instruction: its decider and virtual-input data are $j$, $\mu$, and the argument list, while its two successor states are the start-phase versions of $l_1$ and $l_0'` (`armProg_call`). Each initial register tape represents the binary word of its assigned value, by the buffer-tape word identity (`tapeWord_bufferTape`). Consequently the virtual input assembled from the call segments is precisely the one in the claim. By the definition of a call step, the oracle’s Boolean answer chooses between the positive and negative successor states; this step leaves the register tapes, head positions, and output unchanged and resets the input head to position one. These are exactly the fields of the claimed final start-phase configuration.

**Key facts.** `Complexity.LogProg.rrun_one`, `Complexity.LogProg.armProg_call`, `Complexity.LogProg.tapeWord_bufferTape`.
