<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Machine.lean :: Complexity.LogProg.SavitchARM.St.upd_Q -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the pop routine scratch register

**Claim.** Replacing coordinate $17$ of the register vector by $k$ gives the register vector of the state whose pop routine scratch register $Q$ is $k$.

**Proof.** Compare the vectors coordinatewise. The scratch register $Q$ is at coordinate $17$, and both vectors contain $k$ there. Every other entry is unchanged by either operation, so the two register vectors are equal.
