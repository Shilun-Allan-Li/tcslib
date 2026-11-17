<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountRegs.lean :: Complexity.LogProg.ISCount.St.toV_c -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Next-Ball Count Coordinate

**Claim.** For every state $\sigma$, coordinate $11$ of the register vector equals the next-ball count $c$ of $\sigma$.

**Proof.** By definition, the register vector lists $c$ at coordinate $11$. Evaluating it there gives $\sigma.c$.
