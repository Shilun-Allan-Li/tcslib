<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/NoiseOperatorExercises.lean :: FABL.pmfExpectation_independentProductPMF_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product Expectation by Last Coordinate

**Claim.** For a finite product with a common coordinate space, the expectation under the independent product law is the expectation over the last coordinate of the conditional expectation over the first $n$ coordinates.

**Proof.** Reindex each tuple of length $n+1$ as a pair $(x,a)$ consisting of its first $n$ coordinates and its last coordinate; this is the finite product decomposition encoded by $\mathrm{finSnocEquiv}$ (\texttt{FABL.finSnocEquiv\_apply}). Expand the independent product mass at the tuple obtained by appending $a$ to $x$. By the product-mass formula (\texttt{FABL.independentProductPMF\_apply}), it is the product of the mass of $a$ under the last-coordinate law and the product of the masses of the first $n$ coordinates. Reorder the finite sum so that it first sums over $x$ for each fixed $a$. In that inner sum, the last-coordinate mass is constant and factors out; the remaining sum is the expectation of $x\mapsto f(\operatorname{snoc}(x,a))$ under the product law on the first $n$ coordinates. Summing these inner expectations against the last-coordinate masses gives the claimed iterated expectation.

**Key facts.** `FABL.finSnocEquiv_apply`, `FABL.independentProductPMF_apply`.
