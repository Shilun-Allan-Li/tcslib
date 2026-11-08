<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.booleanDual_parityFunction_univ_isPivotal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pivotality of Dual Parity

**Claim.** The Boolean dual of the parity function on all coordinates takes different values at any sign vector and at the vector obtained by flipping a chosen coordinate.

**Proof.** Write $z$ for the coordinatewise negation of $x$. Negating the vector obtained by flipping coordinate $i$ of $x$ gives the vector obtained by flipping coordinate $i$ of $z$; this follows by checking coordinate $i$ and every other coordinate. The parity flip identity (\(\texttt{parityFunction_univ_flipCoordinate}\)) says that flipping one coordinate negates full parity. In the dual, there is also an outer negation, so these two sign changes show that the dual parity at the flipped input is the negative of its value at $x$. A product of signs is either $1$ or $-1$, and neither equals its own negative; hence the two values differ.

**Key facts.** `FABL.parityFunction_univ_flipCoordinate`.
