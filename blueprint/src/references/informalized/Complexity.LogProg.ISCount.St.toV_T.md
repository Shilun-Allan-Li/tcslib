<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountRegs.lean :: Complexity.LogProg.ISCount.St.toV_T -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scratch Register Coordinate

**Claim.** For every state $\sigma$, the register vector's coordinate $6$ equals the scratch register $T$ of $\sigma$.

**Proof.** The register vector lists $T$ in coordinate $6$. Evaluating the vector at that coordinate therefore gives $\sigma.T$, directly from its definition.
