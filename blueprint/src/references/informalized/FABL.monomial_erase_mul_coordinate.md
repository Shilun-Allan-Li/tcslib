<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.monomial_erase_mul_coordinate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monomial after deleting a coordinate

**Claim.** If $i\in S$, then the monomial on $S$ with $i$ deleted, multiplied by the sign at $i$, equals the monomial on $S$.

**Proof.** The product defining the monomial on $S$ can be split into the factor at $i$ and the product over all remaining coordinates, since $i\in S$. The latter product is the monomial on $S\setminus\{i\}$. Multiplying the two factors gives the monomial on $S};$ the real-valued factors commute, so the order of multiplication is immaterial.
