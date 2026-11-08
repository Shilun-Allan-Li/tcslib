<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Machine.lean :: Complexity.LogProg.ExpBFS.St.upd_N -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Length Update

**Claim.** Replacing coordinate $0$ of the register vector by $k$ gives the register vector of the state with input length counter $k$.

**Proof.** Compare the vectors at an arbitrary coordinate. At coordinate $0$, both have value $k$: the vector update inserts $k$, and the state update sets the input length counter to $k$. At all other coordinates, both retain the original register values. Thus the vectors agree coordinatewise and are equal.
