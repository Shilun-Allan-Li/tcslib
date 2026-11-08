<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/LowDegree.lean :: LowDegreeTest.gowers_product_mul_degree_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Absorption of a low-degree factor

**Claim.** If $g$ has degree at most $d$, then the order-$(d+1)$ Gowers product of $f\cdot g$ agrees with that of $f$.

**Proof.** By multiplicativity of Gowers products (`gowers_product_mul`), the product of $f\cdot g$ at the specified base point and directions factors as the product for $f$ times the product for $g$. The degree hypothesis makes the latter factor equal to $1$. Multiplication by this unit leaves the Gowers product of $f$ unchanged.

**Key facts.** `LowDegreeTest.gowers_product_mul`.
