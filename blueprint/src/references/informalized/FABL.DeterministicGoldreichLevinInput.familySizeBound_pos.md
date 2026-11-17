<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DeterministicGoldreichLevin.lean :: FABL.DeterministicGoldreichLevinInput.familySizeBound_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positivity of the Family Size Bound

**Claim.** The family size bound for a deterministic Goldreich–Levin input is positive.

**Proof.** The family size bound is the value of the positive family-size function at the input's Fourier bound and learning parameter. Positivity of that function (`fourierOneNormFamilySizeBound_pos`) immediately gives the claim.

**Key facts.** `FABL.fourierOneNormFamilySizeBound_pos`.
