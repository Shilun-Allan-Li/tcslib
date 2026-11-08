<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPAlgorithms.lean :: FABL.uniformRandomizedAssignment_sampleLaw -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Law of a Uniform Randomized Assignment

**Claim.** For finite sets $V$ and nonempty $D$, independently assigning each variable a uniform value in $D$ gives the uniform distribution on all assignments $V\to D$.

**Proof.** The sample law is the independent product of the marginal laws. When every marginal is uniform on $D$, the independent product law is uniform on the function space $V\to D$ (`independentProductPMF_uniform`), proving the result.

**Key facts.** `FABL.independentProductPMF_uniform`.
