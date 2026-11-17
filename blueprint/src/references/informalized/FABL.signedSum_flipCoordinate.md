<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/KhintchineKahane.lean :: FABL.signedSum_flipCoordinate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weighted Sum Under a Coordinate Flip

**Claim.** Flipping coordinate $i$ changes the weighted sum by subtracting twice the original contribution from that coordinate.

**Proof.** Separate the $i$th term from each sum. At coordinate $i$, the flipped sign is the negative of the original sign, since each coordinate is either $1$ or $-1$. At every other coordinate, the update leaves the sign unchanged, so the remaining sums agree. Thus the flipped sum is $-x_iw_i$ plus the sum over the other coordinates, while the original is $x_iw_i$ plus that same sum. Subtracting gives the claimed identity.
