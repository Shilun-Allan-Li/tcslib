<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/SmallBiasMarginals.lean :: FABL.coordinateFrequencyLift_ne_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lifted Frequency Is Nonzero

**Claim.** If a frequency vector on the coordinates in $J$ is nonzero, then its lifted frequency vector on all coordinates is nonzero.

**Proof.** Suppose the lifted vector were zero. The dot product of that vector with any full-cube vector would then be zero. In particular, evaluate it on the extension to all coordinates of an arbitrary vector $z$ indexed by $J$. The dot-product identity for the lifted frequency identifies this value with the dot product of $4\gamma$ and the restriction of that extension to $J$; the restriction is exactly $z$. Therefore $4\gamma$ has zero dot product with every $z$. Since the dot-product correspondence is injective, this forces $4\gamma=0$, contradicting the hypothesis.

**Key facts.** `FABL.f₂DotProduct_coordinateFrequencyLift`, `FABL.coordinateProjectionLinear_coordinateExtension`.
