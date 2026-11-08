<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Machine.lean :: Complexity.LogProg.SavitchARM.St.upd_M -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the midpoint register

**Claim.** Replacing coordinate $12$ of the register vector by $k$ gives the register vector of the state whose midpoint register $M$ is $k$.

**Proof.** Compare the two register vectors at an arbitrary coordinate. The midpoint field $M$ is stored at coordinate $12$, so both vectors have value $k$ there. All other entries remain the original state fields on both sides, since the update affects only coordinate $12$ and changing $M$ affects no other field. The vectors are therefore equal.
