<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/QueryLearning.lean :: FABL.runWithCost_queriedFiniteFamilyFourierEstimatorProgramWithSamples -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Queried estimator with uniform samples

**Claim.** The queried finite-family Fourier estimator with samples has the same run law as drawing a uniform sequence of cube inputs, arranging it as a family-indexed sample matrix, and returning the finite-family estimator with its specified cost.

**Proof.** First use the fixed-input run theorem: for every input sequence, the program returns the queried estimator output and charges the stated cost. Its law is therefore the uniform law on sequences mapped to that output-cost pair. The finite-family indexing equivalence carries a uniform sequence of length $|\mathcal F|m$ to a uniform family-by-sample matrix (map of a uniform law through this equivalence). Mapping both laws by the output-and-cost function and composing the maps yields the claimed uniform-matrix description. The two output descriptions agree because the equivalence simply reshapes the sequence into its family-indexed rows; the costs agree by associativity of natural-number addition.

**Key facts.** `FABL.runWithCost_queriedFiniteFamilyFourierEstimatorFromInputs`, `FABL.LearningCost.toTriple_injective`.
