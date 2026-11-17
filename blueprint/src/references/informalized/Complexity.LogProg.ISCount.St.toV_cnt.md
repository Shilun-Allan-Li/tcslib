<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountRegs.lean :: Complexity.LogProg.ISCount.St.toV_cnt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inner Count Coordinate

**Claim.** For every state $\sigma$, coordinate $13$ of the register vector equals the inner count $\mathrm{cnt}$ of $\sigma$.

**Proof.** The register vector is defined with $\mathrm{cnt}$ in coordinate $13$. Its value at that coordinate is therefore $\sigma.\mathrm{cnt}$.
