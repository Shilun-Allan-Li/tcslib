<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductFourierBases.lean :: FABL.pmfInner_add_left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Additivity in the First Argument

**Claim.** For functions $f,g,h$ on a finite set with probability distribution $\pi$, the expectation of $(f+g)h$ equals the sum of the expectations of $fh$ and $gh$.

**Proof.** By the definition of the probability inner product, the left side is the expectation of $(f+g)h$ (`pmfInner_eq_expect`). Pointwise, distributivity gives $(f(x)+g(x))h(x)=f(x)h(x)+g(x)h(x)$. Expectation is additive on sums of functions (`pmfExpectation_add`), so the resulting expectation is the sum of the expectations of $fh$ and $gh$, which are the two inner products on the right.

**Key facts.** `FABL.pmfInner_eq_expect`, `FABL.pmfExpectation_add`.
