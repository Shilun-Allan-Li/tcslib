<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/KrawtchoukPolynomials.lean :: FABL.eval_chooseFactorPolynomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binomial coefficient polynomial evaluation

**Claim.** For natural numbers $z$ and $k$, the polynomial $(k!)^{-1}X(X-1)\cdots(X-k+1)$ evaluated at $z$ equals $\binom{z}{k}$.

**Proof.** Evaluate the product of the scalar polynomial and the descending Pochhammer polynomial. The descending Pochhammer evaluation formula identifies the latter with the numerator in the natural-number binomial coefficient formula; after rewriting division by $k!$ as multiplication by its inverse, the two expressions agree by commutative-ring arithmetic.
