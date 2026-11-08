<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/Controller.lean :: FABL.isAccurateGoldreichLevinStage_of_isAccurateRestrictedFourierWeightEstimate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Accuracy of a Goldreich–Levin Stage

**Claim.** If an estimate approximates every restricted Fourier weight to within $\tau^2/4$, then it has the same accuracy for every candidate in the specified Goldreich–Levin stage, evaluated at the stage prefix and the candidate's free-coordinate part.

**Proof.** Take any candidate $S$ in the stage. The assumed accuracy holds for every coordinate set and every subset of that coordinate set. Instantiate it with the stage prefix $J$ and with the free-coordinate part of $S$, which is a subset of $J$. The resulting inequality is exactly the required stage accuracy for $S$.
