<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPathMachine.lean :: Complexity.LogProg.UReg.u_9 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Saved Position Register Update

**Claim.** Replacing register 9 by $z$ gives the same register-value vector as updating coordinate 9 of the original vector to $z$.

**Proof.** At coordinate $9$, both vectors take the value $z$, corresponding to the new saved field position. At every other coordinate, the vector update keeps its old value, and changing register 9 leaves the other register fields unchanged. Equality at every coordinate proves equality of the vectors.
