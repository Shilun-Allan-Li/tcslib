<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMProof.lean :: Complexity.LogProg.AHalt.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Guarded Halting

**Claim.** If a run halts with answer $r$ and satisfies $G$ at every configuration before halting, and $G$ implies $G'$, then the run also satisfies $G'$ at every configuration before halting, with the same answer.

**Proof.** Take the halting time $T$ witnessing the hypothesis. The run at time $T$ is already halted with answer $r$, so the same $T$ witnesses halting with that answer. For each $t<T$, the configuration at time $t$ satisfies $G$ by hypothesis, and hence satisfies $G'$ by the assumed implication.
