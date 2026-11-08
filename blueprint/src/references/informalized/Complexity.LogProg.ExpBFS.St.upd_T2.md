<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Machine.lean :: Complexity.LogProg.ExpBFS.St.upd_T2 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Return Walk Counter Update

**Claim.** Replacing coordinate $11$ of the register vector by $k$ gives the register vector of the state with return walk counter $k$.

**Proof.** Compare the vectors coordinate by coordinate. At coordinate $11$, both have value $k$, as the vector update replaces that entry and the state update sets the return walk counter to $k$. At every other coordinate, the original register is unchanged in both. Hence the vectors are equal.
