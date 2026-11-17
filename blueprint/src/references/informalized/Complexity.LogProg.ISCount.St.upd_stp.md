<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountRegs.lean :: Complexity.LogProg.ISCount.St.upd_stp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the walk step count

**Claim.** Replacing coordinate 16 of the register vector of a state by $z$ gives the register vector of the state whose walk step count is $z$.

**Proof.** Check equality at each coordinate of the vectors. At coordinate $16$, the update supplies $z$, which is the walk step count in the modified state. At every other coordinate, neither the vector entry nor the corresponding state register changes. The vectors therefore agree at all coordinates.
