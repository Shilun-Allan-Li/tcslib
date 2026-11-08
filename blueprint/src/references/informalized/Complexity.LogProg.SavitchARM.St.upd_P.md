<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Machine.lean :: Complexity.LogProg.SavitchARM.St.upd_P -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the power accumulator

**Claim.** Replacing coordinate $3$ of the register vector by $k$ gives the register vector of the state whose power accumulator $P$ is $k$.

**Proof.** Compare the vectors at an arbitrary coordinate. The power accumulator $P$ is the entry at coordinate $3$, and both vectors have value $k$ there. At every other coordinate, the register update leaves the entry unchanged, as does changing only $P$ in the state. Thus the vectors agree at every coordinate.
