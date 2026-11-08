<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.parityFunction_univ_isPivotal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Every Coordinate Is Pivotal for Full Parity

**Claim.** For every Boolean-cube input and coordinate, flipping that coordinate changes the value of full parity.

**Proof.** By the full-parity flip identity (parityFunction_univ_flipCoordinate), the value after the flip is the negative of the value before it. A sign is either $1$ or $-1$, and in either case it differs from its negative. Thus the two parity values are unequal, which is precisely pivotality.

**Key facts.** `FABL.parityFunction_univ_flipCoordinate`.
