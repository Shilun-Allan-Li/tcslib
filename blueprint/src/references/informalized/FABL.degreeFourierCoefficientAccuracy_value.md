<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/LowDegree.lean :: FABL.degreeFourierCoefficientAccuracy_value -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact Coefficient Accuracy

**Claim.** For every natural number $k$, the coefficient accuracy parameter is $2^{-(k+1)}$.

**Proof.** By definition, the parameter is one quarter of the granularity, and the granularity is $2(1/2)^k$. Thus it equals $\frac12(1/2)^k=(1/2)^{k+1}=2^{-(k+1)}$, using the exponent addition law and the definition of reciprocal powers.
