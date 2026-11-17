<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.juntaRestrictionFailureSet_subset_empiricalBad -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Failure Implies Empirical Error

**Claim.** If the sample contains fewer than M inputs matching the fixed assignment on P, then the empirical matching fraction differs from its uniform-cube probability by at least the stated accuracy, assuming |P| ≤ k.

**Proof.** Write R for the prescribed sample count, a for the matching accuracy $2^{-(k+1)}$, and $p=2^{-|P|}$ for the probability that a uniform cube input matches the assignment. Failure to extract M matching examples means the match count is less than M, by `takeMatchingJuntaExamples_eq_none_iff`. The empirical matching mean is exactly that count divided by R, by `finiteUniformEmpiricalMean_juntaMatchObservation`. Since $R\ge 2^{k+1}M$, this mean is strictly less than $M/R\le a$. Meanwhile, $|P|\le k$ gives $p\ge 2^{-k}=2a$, using `expect_juntaMatchObservation` for the matching probability. Thus the empirical mean lies below p by at least a, so its absolute deviation from p is at least a. The prescribed sample count is positive; this follows from `fourierEstimatorSampleCount_pos` and the fact that it is added to the other sample-count term.

**Key facts.** `FABL.takeMatchingJuntaExamples_eq_none_iff`, `FABL.finiteUniformEmpiricalMean_juntaMatchObservation`, `FABL.expect_juntaMatchObservation`, `FABL.fourierEstimatorSampleCount_pos`.
