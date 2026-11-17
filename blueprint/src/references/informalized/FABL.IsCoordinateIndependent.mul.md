<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PolynomialThresholdInfluence.lean :: FABL.IsCoordinateIndependent.mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Products Preserve Coordinate Independence

**Claim.** If $q$ and $r$ are each unchanged by changing coordinate $i$, then their pointwise product is also unchanged by changing coordinate $i$.

**Proof.** Fix an input $x$ and a sign $b$. The product at the input with coordinate $i$ changed is $q(x^{i\gets b})r(x^{i\gets b})$. The two independence hypotheses identify these factors with $q(x)$ and $r(x)$, respectively. Their product is thus $q(x)r(x),$ as required.
