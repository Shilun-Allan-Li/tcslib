<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ProductHypercontractivity.lean :: FABL.pmfExpectation_productProbabilityPMF_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation on a Product Space

**Claim.** The expectation under the product law on $\Omega^{n+1}$ equals the expectation over the last sample $a\sim\pi$ of the expectation over the first $n$ independent samples of $f(x_1,\ldots,x_n,a)$.

**Proof.** Reindex the finite sum over tuples in $\Omega^{n+1}$ by the bijection between such tuples and pairs $(x,a)$, where $x\in\Omega^n$ and $a\in\Omega$; under this bijection the tuple is the sequence obtained by appending $a$ to $x$ (`finSnocEquiv_apply`). The product probability of that tuple is the product of the coordinate probabilities (`productProbabilityPMF_apply`), which separates into the product for $x$ times the probability of $a$. Interchanging the finite sums puts the sum over $a$ outside. For each $a$, factor its probability out of the sum over $x$; the remaining sum is the expectation over the first $n$ samples of $f$ with $a$ appended. This is the stated iterated expectation.

**Key facts.** `FABL.finSnocEquiv_apply`, `FABL.productProbabilityPMF_apply`.
