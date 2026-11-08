<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.card_lowDegreeF₂Coefficients -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counting binary coefficients

**Claim.** The set of all functions from the subsets of an $n$-element set of size at most $\ell$ to the two-element field has cardinality $2^m$, where $m$ is the number of such subsets.

**Proof.** A function from a finite set of $m$ elements to a two-element set is specified by one of two choices at each input. Thus there are $2^m$ such functions. Here the domain has cardinality $m$ by definition, and the two-element field has cardinality $2$; the finite-function cardinality formula gives the result.
