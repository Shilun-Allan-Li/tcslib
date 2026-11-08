<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/UnateFunctions.lean :: FABL.reorientInput_flipCoordinate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reorientation and coordinate flips

**Claim.** Reorienting a sign vector after flipping coordinate $i$ gives the same result as flipping coordinate $i$ after reorientation.

**Proof.** It suffices to compare the two sign vectors at each coordinate $j$. If $j=i$, both constructions apply the same reorientation to the flipped sign at $i$; since the reorientation acts by multiplying signs, this is the flipped value of the reoriented sign. The possible signs of $\sigma_i$ and $x_i$ are $1$ and $-1$, and checking these cases gives the equality. If $j\ne i$, the flip changes no value at $j$, so both sides equal the reorientation of $x_j$ there. Thus the vectors agree at every coordinate.
