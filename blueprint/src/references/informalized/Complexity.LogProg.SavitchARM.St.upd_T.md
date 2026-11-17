<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Machine.lean :: Complexity.LogProg.SavitchARM.St.upd_T -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the scratch register

**Claim.** Replacing coordinate $4$ of the register vector by $k$ gives the register vector of the state whose scratch register $T$ is $k$.

**Proof.** Compare the register vectors at an arbitrary coordinate. The scratch register $T$ is the entry at coordinate $4$, where both vectors have value $k$. At all other coordinates, both operations preserve the original state field. Hence the vectors agree.
