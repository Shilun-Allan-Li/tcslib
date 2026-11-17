<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.lowDegreeJuntaAccuracy_lt_detectionThreshold -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Accuracy Below the Detection Threshold

**Claim.** For every natural number $k$, the coefficient accuracy $1/(3\cdot 2^k)$ is strictly less than the detection threshold $1/(2\cdot 2^k)$.

**Proof.** Unfolding the two quantities reduces the claim to $1/(3\cdot 2^k)<1/(2\cdot 2^k)$. Both denominators are positive, so cross-multiplication preserves the inequality and reduces it to $2\cdot 2^k<3\cdot 2^k$. Since $2^k>0$, this is immediate.
