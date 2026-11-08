<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/FourierEstimation.lean :: FABL.uniformSample_toMeasure_eq_pi -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Product Measure

**Claim.** For a finite nonempty measurable space whose singletons are measurable, the measure of a uniform random function from the $m$ coordinates to $\Omega$ is the product of the uniform measures on $\Omega$ over those coordinates.

**Proof.** It is enough to compare the two measures on each singleton, since the space of functions is finite and its singletons are measurable. Fix a function of the $m$ coordinates. Under the uniform law on all such functions, its probability is the reciprocal of the number of functions, namely $|\Omega|^{-m}$. Under the product measure, each coordinate is assigned its specified value with probability $|\Omega|^{-1}$, so the singleton has measure $\prod_{i=1}^m |\Omega|^{-1}=|\Omega|^{-m}$. Thus the singleton masses, and hence the measures, agree.
