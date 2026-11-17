<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathWalkMachine.lean :: Complexity.LogProg.PReg.v_0 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input pointer register

**Claim.** For any register state whose first component is the input pointer $p$, the value of its register vector at index $0$ is $p$.

**Proof.** The register vector is the function listing the state components in order, beginning with $p$. Evaluating this list at index $0$ returns its first entry, so the value is $p$.
