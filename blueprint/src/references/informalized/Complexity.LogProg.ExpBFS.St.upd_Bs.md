<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Machine.lean :: Complexity.LogProg.ExpBFS.St.upd_Bs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Memory-Base Coordinate Update

**Claim.** Changing coordinate $7$ of the register vector to $k$ gives the register vector of the state obtained by replacing $Bs$ with $k$.

**Proof.** We show equality of the two functions by checking their values at each of the 17 indices. At index $7$, the update replaces the old value $Bs$ by $k$, which is exactly the $Bs$ register of the modified state. At every other index, the update leaves the value unchanged, and the corresponding register of the modified state agrees with that of the original state. Hence the functions agree everywhere.
