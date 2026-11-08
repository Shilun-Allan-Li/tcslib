<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/RandomRestrictions.lean :: FABL.expect_sq_discreteDerivative_combine -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Squared Derivative under Coordinate Splitting

**Claim.** For the squared discrete derivative evaluated after combining the free coordinates with fixed complementary signs, its uniform mean over the full cube equals its uniform mean over assignments to the free coordinates.

**Proof.** Split a uniformly chosen full-cube point into its restrictions to $J$ and its complement. The coordinate-splitting bijection identifies the full-cube mean with the mean over pairs $(y,w)$ of free and fixed sign assignments; the free part of the original point is exactly its first component (freePart_eq_split). With $z$ fixed, the quantity being averaged depends on $y$ alone, so averaging it over the dummy variable $w$ leaves it unchanged. Thus the pair mean reduces to the mean over free assignments, as claimed.

**Key facts.** `FABL.freePart_eq_split`.
