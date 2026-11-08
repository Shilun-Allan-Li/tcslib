<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountRegs.lean :: Complexity.LogProg.ISCount.St.upd_v -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the outer-vertex coordinate

**Claim.** Replacing coordinate $10$ of a state's register vector by $z$ gives the register vector of the state obtained by setting its outer-vertex register to $z$.

**Proof.** At coordinate $10$, both the updated vector and the vector of the modified state have entry $z$. At every other coordinate, the update and the state modification leave the original register value intact. Thus the vectors agree coordinate by coordinate.
