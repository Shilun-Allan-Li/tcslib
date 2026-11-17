<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Machine.lean :: Complexity.LogProg.TQBFARM.St.upd_V -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Current Literal Variable

**Claim.** Updating register 6 of the register vector for a state $s$ to $k$ gives the register vector of the state obtained by setting $V=k$.

**Proof.** Compare the vectors at an arbitrary coordinate. At coordinate $6$, each side has value $k$. At each of the other six coordinates, neither the register update nor the state update changes the listed value. Therefore the two vectors agree everywhere.
