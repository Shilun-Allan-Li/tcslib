<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/SmallBiasVariants.lean :: FABL.exists_basisExpandedGroupedCoefficient_ne_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A nonzero grouped coefficient

**Claim.** For $\ell>0$, every nonzero binary string of length $n\ell$ has a block whose coordinates, interpreted in the chosen basis of the degree-$\ell$ binary extension field, represent a nonzero field element.

**Proof.** Because $\gamma$ is nonzero, it has a coordinate $q$ with $\gamma(q)\ne0$; otherwise it would be zero at every coordinate and thus be the zero function. Use the inverse of the coordinate-pairing equivalence to write $q$ as the pair $(i,j)$, where $i$ selects a block and $j$ a position within that block. If the field element represented by block $i$ were zero, applying the basis coordinate map would show that every bit in that block is zero. In particular, the bit at position $j$ would be zero. The coordinate-pairing equivalence identifies that bit with $\gamma(q)$, contradicting its nonvanishing.
