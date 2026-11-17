<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMProof.lean :: Complexity.LogProg.AHalt.ret -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting After a Return Instruction

**Claim.** If the instruction at state $l$ returns $r$ and $G$ holds of the configuration with state $l$, registers $v$, and no recorded result, then the run from that configuration halts with answer $r$ and satisfies $G$ at every earlier configuration.

**Proof.** Use $T=1$. One application of the return instruction changes the state to the halting state and records the answer $r$. The only natural time $t<1$ is $t=0$, when the run is at the given initial configuration; $G$ holds there by assumption.
