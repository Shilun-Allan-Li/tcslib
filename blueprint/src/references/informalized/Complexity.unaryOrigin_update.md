<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean :: Complexity.unaryOrigin_update -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation of the Origin Marker

**Claim.** Updating the tape at a positive position to the unit marker leaves the origin marker exactly at position $0$.

**Proof.** Fix a position $z$ and split according to whether $z=u$. If $z=u$, the update gives the unit marker there. Since $u\ge 1$, this position is not $0$, so both sides of the claimed equivalence are false. If $z\ne u$, the update does not change the tape value at $z$, and the hypothesis says that this value is the origin marker exactly when $z=0$.
