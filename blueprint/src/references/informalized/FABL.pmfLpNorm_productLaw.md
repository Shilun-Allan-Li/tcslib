<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ProductHypercontractivity.lean :: FABL.pmfLpNorm_productLaw -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability Norm under Product Distributions

**Claim.** For finite sets A and B, probability distributions πA and πB, p > 0, and f: A × B → ℝ, the probability norm under the product distribution equals the iterated probability norm, first over B and then over A.

**Proof.** Expand both norms using their definition as real powers of expectations. The product expectation formula (FABL.pmfExpectation_productLaw) rewrites the expectation under the product distribution as an expectation over a, whose integrand is the expectation over b of |f(a,b)|^p. For each fixed a, the norm power identity (FABL.pmfLpNorm_rpow) says that this inner expectation equals the p-th power of the norm over B. Substituting this into the outer expectation yields exactly the expectation whose p-th root is the outer norm on the right-hand side. Since p is positive, the real-power composition in these definitions gives the stated equality.

**Key facts.** `FABL.pmfExpectation_productLaw`, `FABL.pmfLpNorm_rpow`.
