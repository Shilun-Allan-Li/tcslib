<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ProductHypercontractivity.lean :: FABL.iteratedCouplingInner_eq_productProbabilityPMF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Iterated coupling as a product expectation

**Claim.** For a finite set $\Omega$, the iterated coupling expectation of $f$ and $g$ at length $n$ equals the expectation of $f(x)g(y)$ under the law of $n$ independent coordinate pairs, each distributed according to $\kappa$.

**Proof.** Proceed by induction on $n$. At length zero, the product law is concentrated on the unique empty tuple (`productProbabilityPMF_zero`), and expectation under a point mass evaluates the payoff at that point (`pmfExpectation_pure`). Both coordinate projections of the empty tuple are the empty tuple, so the result is the product of the two function values there. For the successor step, expose the final coordinate pair. The iterated coupling first averages over that pair and then applies the length-$n$ iterated coupling to the two functions with that pair appended (`iteratedCouplingInner_succ`). The product-law expectation has the same decomposition into an outer expectation over the final coordinate and an inner expectation over the first $n$ coordinates (`pmfExpectation_productProbabilityPMF_succ`). Apply the induction hypothesis to each fixed final pair; the first- and second-coordinate projections of an appended tuple are the corresponding projected tuples with the respective entries appended (`pairVectorFst_snoc`, `pairVectorSnd_snoc`). Thus the inner payoffs agree pointwise, and so do the full expectations.

**Key facts.** `FABL.iteratedCouplingInner_zero`, `FABL.productProbabilityPMF_zero`, `FABL.pmfExpectation_pure`, `FABL.iteratedCouplingInner_succ`, `FABL.pmfExpectation_productProbabilityPMF_succ`, `FABL.pairVectorFst_snoc`, `FABL.pairVectorSnd_snoc`.
