<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Machine.lean :: Complexity.LogProg.TQBFARM.St.upd_C -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Halving Counter

**Claim.** For any machine state $s$ and natural number $k$, updating register $5$ of its register vector to $k$ gives the register vector of the state obtained by setting its halving counter $C$ to $k$.

**Proof.** Compare the two register vectors at an arbitrary index, checking each of the seven possible indices. At index $5$, the update replaces the old entry by $k$, and the modified state has $C=k$ in that position. At every other index, the update leaves the entry unchanged, and setting $C$ does not change the corresponding state field. The vectors therefore agree at every index.
