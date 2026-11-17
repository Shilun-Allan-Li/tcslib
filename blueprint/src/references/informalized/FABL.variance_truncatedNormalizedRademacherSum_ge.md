<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLCounterexample.lean :: FABL.variance_truncatedNormalizedRademacherSum_ge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variance of a Truncated Rademacher Sum

**Claim.** For every positive integer $n$, the variance of the truncated normalized Rademacher sum is at least $1/24$.

**Proof.** Let $Z$ be the normalized Rademacher sum, $T$ its truncation to $[-1,1]$, and let the underlying law be uniform on the sign cube. The second moment of $Z$ is $1$ (`normalizedRademacherSum_secondMoment`), while its fourth moment is at most $3$ (`normalizedRademacherSum_fourthMoment_le_three`). Apply the Paley–Zygmund inequality (`pmfPaleyZygmund`) to the nonnegative random variable $Y=Z^2$ with threshold parameter $1/2$. These moment bounds give probability at least $1/12$ that $Z^2>1/2$. Whenever this event occurs, truncation still satisfies $T^2\ge 1/2$ (`truncateUnit_sq_ge_half_of_sq_gt_half`), so the event where $T^2\ge1/2$ has probability at least $1/12$ (`pmfEventProbability_mono`). For a nonnegative random variable, its expectation is at least a threshold times the probability of exceeding that threshold (`mul_pmfEventProbability_le_expectation`); hence $\mathbb E[T^2]\ge(1/2)(1/12)=1/24$. Finally, $T$ has mean zero (`mean_truncatedNormalizedRademacherSum`), so its variance equals this second moment. Converting the uniform expectation to the stated variance expression yields the claim.

**Key facts.** `FABL.pmfExpectation_uniformPMF_eq_expect`, `FABL.normalizedRademacherSum_secondMoment`, `FABL.normalizedRademacherSum_fourthMoment_le_three`, `FABL.pmfPaleyZygmund`, `FABL.pmfEventProbability_nonneg`, `FABL.truncateUnit_sq_ge_half_of_sq_gt_half`, `FABL.pmfEventProbability_mono`, `FABL.mul_pmfEventProbability_le_expectation`, `FABL.mean_truncatedNormalizedRademacherSum`.
