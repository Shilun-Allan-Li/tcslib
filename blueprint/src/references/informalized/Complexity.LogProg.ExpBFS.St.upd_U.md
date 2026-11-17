<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Machine.lean :: Complexity.LogProg.ExpBFS.St.upd_U -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Source Code Update

**Claim.** Replacing coordinate $8$ of the register vector by $k$ gives the register vector of the state with source code $k$.

**Proof.** At coordinate $8$, both vectors have value $k$: the register-vector update inserts it, while the state update sets the source code to $k$. At each other coordinate, both vectors retain the original register. They consequently agree coordinatewise and are equal.
