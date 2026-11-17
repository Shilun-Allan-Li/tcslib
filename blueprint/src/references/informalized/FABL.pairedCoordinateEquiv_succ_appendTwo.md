<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/CompleteQuadraticDecomposition.lean :: FABL.pairedCoordinateEquiv_succ_appendTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Appended Coordinate Pair

**Claim.** For $x\in\mathbb{F}_2^{r+2k}$ and $a,b\in\mathbb{F}_2$, applying the paired-coordinate automorphism for $k+1$ pairs to the vector obtained by appending $a,b$ to $x$ gives the image of $x$ under the automorphism for $k$ pairs, followed by $a+\sum_i x_i$ and $b+\sum_i x_i$.

**Proof.** Split the vector into its prefix of length $r+2k$ and its final two coordinates. In this decomposition, the automorphism for $k+1$ pairs first applies the tail shear, which leaves the prefix unchanged and adds the sum of its coordinates to each of the two tail coordinates. It then applies the automorphism for $k$ pairs to the prefix and reassembles the vector with the transformed tail. Thus the prefix becomes the image of $x$, while the tail becomes $(a+\sum_i x_i,b+\sum_i x_i)$, as claimed.
