<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountRegs.lean :: Complexity.LogProg.ISCount.St.toV_K -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Code-Bound Register Coordinate

**Claim.** For every register state $\sigma$, the code-bound coordinate of its register vector equals $\sigma.K$.

**Proof.** The register vector is defined by listing the state fields in order, with $K$ in coordinate $5$. Evaluating that vector at the code-bound register, which is coordinate $5$, returns $\sigma.K$ by the definition.
