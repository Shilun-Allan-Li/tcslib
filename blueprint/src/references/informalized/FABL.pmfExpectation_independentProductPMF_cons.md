<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ReasonableProductPolynomials.lean :: FABL.pmfExpectation_independentProductPMF_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product Expectation by First Coordinate

**Claim.** For a product of finite coordinate spaces with independent coordinate laws, the expectation of a function is obtained by first averaging over coordinate $0$ and then averaging over the remaining coordinates.

**Proof.** Regard a point in the full product as a pair $(z,x)$, where $z$ is its coordinate $0$ and $x$ records the remaining coordinates. The equivalence between these descriptions simply reindexes the finite sum defining expectation. Expanding the product mass function at $(z,x)$ gives the mass of $z$ under $p_0$ times the product of the masses of the remaining coordinates, by the defining formula for the independent product distribution (\texttt{FABL.independentProductPMF\_apply}). Reorder the finite sum to sum over $z$ inside and over $x$ outside. For each fixed $x$, the factor contributed by the remaining coordinates is constant in $z$, so it factors out of the inner sum. The inner sum is precisely the expectation under $p_0$ of $z\mapsto f(\operatorname{cons}(z,x))$; the outer sum is the expectation under the product law of the remaining coordinates. This is the stated iterated expectation.

**Key facts.** `FABL.independentProductPMF_apply`.
