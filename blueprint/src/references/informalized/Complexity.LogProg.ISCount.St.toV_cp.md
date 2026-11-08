<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountRegs.lean :: Complexity.LogProg.ISCount.St.toV_cp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Known-Ball Size Coordinate

**Claim.** For every state $\sigma$, coordinate $9$ of the register vector equals the known-ball size $\mathrm{cp}$ of $\sigma$.

**Proof.** The register vector lists $\mathrm{cp}$ at coordinate $9$. Evaluating the vector at that coordinate gives $\sigma.\mathrm{cp}$ by definition.
