<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/FoolingF₂Polynomials/ViolaAuxiliary.lean :: FABL.expectation_pair_correlation_eq_expect_convolution_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pair correlation as a squared convolution average

**Claim.** For a probability density $\phi$ of uniform mean one and any function $F$, averaging $F(x+y)F(x+y')$ over independent $\phi$-distributed shifts $y,y'$, and then uniformly over $x$, equals the uniform average of the square of the convolution of $\phi$ with $F$.

**Proof.** Expand both density-weighted expectations as finite uniform expectations. By linearity, move the constant factors inside the averages and regroup the result as successive averages over $y$, $y'$, and $x$. Commuting these finite averages puts the $x$-average outermost. For each fixed $x$, factor the product into $(\phi(y)F(x+y))(\phi(y')F(x+y'))$; the two independent finite averages then multiply. Each factor is the density-weighted expectation of $F(x+y)$. By the addition form of the convolution evaluation formula (`density_convolution_apply`), this is the convolution of $\phi$ and $F$ at $x$. Thus the product is the square of that convolution, and averaging over $x$ proves the identity.

**Key facts.** `FABL.density_convolution_apply`.
