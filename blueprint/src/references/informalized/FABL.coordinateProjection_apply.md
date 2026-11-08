<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.coordinateProjection_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate projection formula

**Claim.** Projecting onto all coordinates except one evaluates the function by averaging over the value assigned to that omitted coordinate, while keeping all other coordinates fixed.

**Proof.** Fix an input $x$. In the product average defining the projection, merging coordinates from $x$ and a resampled input leaves every coordinate other than $i$ equal to its value in $x$, and sets coordinate $i$ to the resampled value $y_i$. Thus the integrand depends only on $y_i$. The expectation of a product of coordinate functions under the independent product distribution factors as the product of their expectations (\texttt{FABL.pmfExpectation\_independentProductPMF\_prod}). Here all factors except the $i$th are constant one, whose expectations are one (\texttt{FABL.pmfExpectation\_const\_one}); the remaining factor is the expectation under $\pi$ of $f$ with coordinate $i$ replaced. This is the asserted formula.

**Key facts.** `FABL.pmfExpectation_independentProductPMF_prod`, `FABL.pmfExpectation_const_one`.
