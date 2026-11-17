<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Machine.lean :: Complexity.LogProg.ExpBFS.St.upd_V -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Target Code Update

**Claim.** Replacing coordinate $9$ of the register vector by $k$ gives the register vector of the state with target code $k$.

**Proof.** Compare the two vectors at each coordinate. At coordinate $9$, both have value $k$, by the vector update and the state update of the target code. At all other coordinates, both preserve the original register values. Thus the vectors agree coordinatewise and are equal.
