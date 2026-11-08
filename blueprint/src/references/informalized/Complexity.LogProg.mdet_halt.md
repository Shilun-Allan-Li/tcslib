<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/MARMCompile.lean :: Complexity.LogProg.mdet_halt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Halting simulation of a deterministic instruction

**Claim.** Under the stated precondition and register-length and memory-head bounds, if the ordinary execution from the given label and register values halts with unchanged registers and answer $b_0$, then the compiled machine reaches a halting configuration with output extended by $b_0$, and every configuration up to that time satisfies the register, decider-tape, and memory-head bounds.

**Proof.** 1. The deterministic part of the augmented program replaces memory instructions by a fixed return answer. At the label under consideration the instruction is deterministic, so changing that fallback answer does not change its ordinary one-step result (`astep_mdetPart`). Thus the execution that halts with answer $b_0$ can also be viewed using fallback answer $\neg b_0$. The precondition transfers to this choice by invariance of the precondition under changing the fallback answer (`pre_mdetPart`).

2. Apply the ordinary register-program simulation to this execution (`arm_run`). It supplies a compiled execution that halts with output extended by $b_0$, while retaining the register bounds along the run and the decider-work-tape bounds. The initial bound needed for the run follows from the assumed precondition and the hypotheses on the register bit lengths.

3. The compiled run can be represented using deterministic compilation with fallback answer $\neg b_0$. The deterministic machine's memory-enabled states would halt immediately with output bit $\neg b_0$ (`detM_step_mem`). Since the run just obtained instead halts with output bit $b_0$, such a state cannot occur before its terminal time (`avoid_of_halt`). Consequently, every earlier state avoids memory instructions, so the memory-augmented run with the given tape follows the deterministic run step by step (`mrunFrom_eq`).

4. At the terminal time, the deterministic configuration is the seam of the halted ordinary compiled configuration. The seam preserves its halting state (`seam_state_none`) and output, giving the claimed halt and output for the memory-augmented machine. At each time up to termination, convert the ordinary register and decider-tape bounds to bounds on the configuration with its memory tape appended (`mbox_memCfg`); the appended head bound is supplied by $|p|\le P$.

**Key facts.** `Complexity.LogProg.astep_mdetPart`, `Complexity.LogProg.pre_mdetPart`, `Complexity.LogProg.arm_run`, `Complexity.LogProg.detM_step_mem`, `Complexity.LogProg.avoid_of_halt`, `Complexity.LogProg.mrunFrom_eq`, `Complexity.LogProg.seam_state_none`, `Complexity.LogProg.mbox_memCfg`.

**Caveat.** The proof source invokes `compile_correct_from` to relate the ordinary compiled run to the deterministic machine's run, but the supplied upstream statement is abbreviated and the proof uses detailed register and decider-tape bounds from it. The final terminal-state argument also relies on the stated seam equality.
