<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Machine.lean :: Complexity.LogProg.SavitchARM.St.upd_SP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the phase bits stack

**Claim.** Replacing coordinate $15$ of the register vector by $k$ gives the register vector of the state whose phase bits stack $SP$ is $k$.

**Proof.** The phase bits stack $SP$ is stored at coordinate $15$, and both vectors have value $k$ at that coordinate. At every other coordinate, neither operation changes the original entry. Thus the register vectors are equal coordinatewise.
