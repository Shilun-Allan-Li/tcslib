<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DeterministicGoldreichLevin.lean :: FABL.DeterministicQueryProgram.runWithCost_deterministicGoldreichLevinCoefficientProgram -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coefficient Program Output and Cost

**Claim.** The deterministic Goldreich–Levin coefficient program returns the sparse Fourier hypothesis whose coefficients are the empirical averages over the program’s small-bias sample, and its cost is the prescribed combination of generator construction, membership queries, and coefficient-estimation work.

**Proof.** Unfold the coefficient program and run its three components in order. The initial local-work charge contributes the generator construction work. The query batch asks the target at each point obtained by converting the corresponding small-bias sample to the sign cube, so the answers are exactly the target values used in the stated hypothesis. The final local-work charge contributes the family size times the per-coefficient estimation work, and the pure return produces the hypothesis defined from those answers. By the recursive cost definition, the batch contributes its sample count in membership queries and the same amount of local work; combining these charges gives the prescribed cost.
