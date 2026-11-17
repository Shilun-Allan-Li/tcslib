<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountRegs.lean :: Complexity.LogProg.ISCount.St.upd_u -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the inner-vertex coordinate

**Claim.** Replacing coordinate $12$ of a state's register vector by $z$ gives the register vector of the state obtained by setting its inner-vertex register to $z$.

**Proof.** Equality of the vectors follows by checking their entries. The entry at coordinate $12$ becomes $z$ under the update and is also $z$ in the modified state. All other entries are unchanged in both vectors, so the vectors agree everywhere.
