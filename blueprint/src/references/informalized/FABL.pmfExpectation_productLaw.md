<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ProductHypercontractivity.lean :: FABL.pmfExpectation_productLaw -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation Under a Product Law

**Claim.** For finite spaces $A$ and $B$, the expectation of $f$ under the law that first samples from $\mu$ and then independently samples from $\nu$ is the expectation over $a\sim\mu$ of the expectation over $b\sim\nu$ of $f(a,b)$.

**Proof.** The product law is defined by first binding a sample $a$ from $\mu$, then mapping a sample $b$ from $\nu$ to the pair $(a,b)$. The expectation-under-binding formula (`pmfExpectation_bind`) therefore expresses the left side as the expectation over $a$ of the expectation under that mapped law. The expectation-under-mapping formula (`pmfExpectation_map`) identifies the inner expectation with the expectation over $b\sim\nu$ of $f(a,b)$, as required.

**Key facts.** `FABL.pmfExpectation_bind`, `FABL.pmfExpectation_map`.
