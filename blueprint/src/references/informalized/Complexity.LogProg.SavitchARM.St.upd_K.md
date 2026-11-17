<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Machine.lean :: Complexity.LogProg.SavitchARM.St.upd_K -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the code bound register

**Claim.** Replacing coordinate $9$ of the register vector by $k$ gives the register vector of the state whose code bound register $K$ is $k$.

**Proof.** Compare the two register vectors at an arbitrary coordinate. The code bound field $K$ occupies coordinate $9$, where both vectors have value $k$. At every other coordinate, the update preserves the original entry, and setting $K$ to $k$ leaves all other state fields unchanged. Hence the vectors agree coordinatewise.
