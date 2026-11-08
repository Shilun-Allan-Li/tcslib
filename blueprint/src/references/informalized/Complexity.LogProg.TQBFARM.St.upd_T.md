<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Machine.lean :: Complexity.LogProg.TQBFARM.St.upd_T -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Scratch Stack Copy

**Claim.** Updating register 3 of the register vector for a state $s$ to $k$ gives the register vector of the state obtained by setting $T=k$.

**Proof.** Compare the two vectors at an arbitrary coordinate. At coordinate $3$, both have value $k$. At every other coordinate, the register update leaves the value unchanged, as does changing only the field $T$ in the state. Hence the vectors agree coordinatewise.
