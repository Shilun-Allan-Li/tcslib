<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Machine.lean :: Complexity.LogProg.SavitchARM.St.upd_SE -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the saved endpoints stack

**Claim.** Replacing coordinate $14$ of the register vector by $k$ gives the register vector of the state whose saved endpoints stack $SE$ is $k$.

**Proof.** Compare the vectors at an arbitrary coordinate. The saved endpoints stack $SE$ occupies coordinate $14$, where both vectors have value $k$. All other coordinates retain their original entries under both operations. Therefore the register vectors agree.
