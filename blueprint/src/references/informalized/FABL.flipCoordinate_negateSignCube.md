<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.flipCoordinate_negateSignCube -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Flipping commutes with global negation

**Claim.** For every sign vector $x$ and coordinate $i$, flipping coordinate $i$ in $-x$ gives the global negation of the vector obtained by flipping coordinate $i$ in $x$.

**Proof.** Check the two vectors coordinate by coordinate. At coordinate $j=i$, the flip replaces the current entry by its negative. The entry of $-x$ there is $-x_i$, so its flip is $x_i$; this is also the negative of the flipped entry of $x$, which is $-(-x_i)=x_i$. At any coordinate $j\ne i$, neither flip changes that coordinate, and both sides have value $-x_j$. Hence the vectors agree at every coordinate.
