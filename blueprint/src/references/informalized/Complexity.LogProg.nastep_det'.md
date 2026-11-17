<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMKit.lean :: Complexity.LogProg.nastep_det' -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Deterministic instruction steps agree

**Claim.** When the instruction of the nondeterministic program at $l$ is the deterministic instruction $i$, its one-step transition agrees with the step that assigns $i$ to every state.

**Proof.** Substitute the assumed instruction at $l$ into the definition of the nondeterministic step. Both sides then apply the same deterministic instruction $i$ at state $l$, with the same configuration, oracle, and input, so their resulting configurations agree.
