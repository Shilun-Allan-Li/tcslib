<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.monomial_mul_heterogeneousBiasedMonomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product of Monomials

**Claim.** The product of the ordinary monomial on $T$ and the heterogeneous biased monomial on $S$ equals the coordinatewise product of their respective indicator-weighted factors.

**Proof.** Expand both monomials as products over $T$ and $S$. Extend each finite product to all coordinates by inserting the factor $1$ outside its indexing set. The product of these two full-coordinate products can then be combined coordinate by coordinate: at each $i$, its factors are the ordinary factor, present exactly when $i\in T$, and the standardized biased factor, present exactly when $i\in S$. This gives the stated product.
