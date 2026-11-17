<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Machine.lean :: Complexity.LogProg.ExpBFS.St.upd_K -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Code Bound Update

**Claim.** Replacing coordinate $6$ of the register vector by $k$ gives the register vector of the state with code bound $k$.

**Proof.** Compare the two register vectors at an arbitrary coordinate. At coordinate $6$, both have value $k$: the vector update inserts it there, and the state update sets the code bound to $k$. Every other coordinate keeps its original register value in both vectors. Hence the vectors agree coordinatewise and are equal.
