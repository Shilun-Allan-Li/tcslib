<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Machine.lean :: Complexity.LogProg.ExpBFS.St.upd_Lg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logarithm Bound Update

**Claim.** Replacing coordinate $1$ of the register vector by $k$ gives the register vector of the state with logarithm bound $k$.

**Proof.** Compare the vectors at an arbitrary coordinate. At coordinate $1$, both contain $k$, since the vector update replaces that entry and the state update sets the logarithm bound to $k$. At every other coordinate, both retain the original register. The vectors therefore agree at every coordinate and are equal.
