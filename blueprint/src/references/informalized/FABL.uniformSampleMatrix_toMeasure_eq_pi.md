<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/FiniteFamily.lean :: FABL.uniformSampleMatrix_toMeasure_eq_pi -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Matrix Product Measure

**Claim.** For a finite family of coordinate sets, the measure of a uniform random matrix whose rows are independent uniform samples is the product of the uniform sample measures, one for each row.

**Proof.** Two finite measures on this finite function space agree if they assign the same measure to every singleton. Fix a matrix of samples. Its probability under the uniform law on all matrices is the reciprocal of the number of such matrices. Since a matrix is a function from the row indices to the sample space, the cardinality of the whole space is the sample-space cardinality raised to the number of rows. The product measure assigns the same matrix the product of the reciprocal sample-space cardinalities, one for each row. These probabilities coincide, proving equality of the measures.
