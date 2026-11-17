<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/FourierEstimation.lean :: FABL.uniformSampleInputs_toMeasure_eq_pi -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product Measure for Uniform Sample Inputs

**Claim.** The measure associated with a uniform random element of $(\{−1,1\}^n)^m$ is the product of the measures associated with uniform random elements of $\{−1,1\}^n$.

**Proof.** Apply the general product-measure identity for a uniform random element of a finite function space: its associated measure is the product, over the index set, of the uniform measures on the value space (`uniformSample_toMeasure_eq_pi`). Taking the value space to be $\{−1,1\}^n$ and the index set to be the $m$ coordinates gives the claimed identity.

**Key facts.** `FABL.uniformSample_toMeasure_eq_pi`.
