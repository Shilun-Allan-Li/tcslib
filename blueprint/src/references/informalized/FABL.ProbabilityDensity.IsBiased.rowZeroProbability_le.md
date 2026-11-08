<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/MatrixProductVerification.lean :: FABL.ProbabilityDensity.IsBiased.rowZeroProbability_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Row Zero Probability Bound

**Claim.** For a nonzero vector \(\gamma\), the density-weighted probability that its dot product with the input is zero is at most \((1+\varepsilon)/2\) when the density is \(\varepsilon\)-biased.

**Proof.** The probability in question equals one half of one plus the density expectation of the Walsh character associated with \(\gamma\) (\texttt{FABL.matrixProductRowZeroProbability\_eq}). By the equivalence between bias and bounds on character expectations, the absolute value of this expectation is at most \(\varepsilon\) for every nonzero \(\gamma\) (\texttt{FABL.ProbabilityDensity.isBiased\_iff\_expectation}). In particular, the expectation itself is at most \(\varepsilon\); substituting this upper bound into the probability identity proves the result.

**Key facts.** `FABL.matrixProductRowZeroProbability_eq`, `FABL.ProbabilityDensity.isBiased_iff_expectation`.
