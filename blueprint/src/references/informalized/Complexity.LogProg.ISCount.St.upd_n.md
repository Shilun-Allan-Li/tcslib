<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountRegs.lean :: Complexity.LogProg.ISCount.St.upd_n -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the input length

**Claim.** Replacing coordinate 0 of the register vector of a state by $z$ gives the register vector of the state whose input-length register is $z$.

**Proof.** Two vectors are equal if they agree at every coordinate. At coordinate $0$, the update supplies $z$, which is the input-length entry of the modified state. At every other coordinate, the update leaves the vector unchanged, and the corresponding register of the state is unchanged. Hence the two vectors agree everywhere.
