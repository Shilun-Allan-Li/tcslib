<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Machine.lean :: Complexity.LogProg.TQBFARM.St.upd_Z -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Scratch Register

**Claim.** Changing coordinate 4 of the register vector for a state $st$ to $k$ gives the register vector of the state obtained by replacing $Z$ by $k$.

**Proof.** Compare the two vectors coordinatewise. At coordinate $4$, both sides contain $k$; at every other coordinate, the corresponding value is unchanged by either update. This proves equality of the vectors.
