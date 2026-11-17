<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/RandomSmallBias.lean :: FABL.measure_randomSmallBiasSample_not_isBiased_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Random Sample Small Bias

**Claim.** For $n\ge0$ and $0<\varepsilon<1$, the probability that the sample fails to have all nontrivial Walsh empirical means bounded in absolute value by $\varepsilon$ is at most $2^{-n}$.

**Proof.** If $n=0$, every sample is small biased, so the failure event is empty. Otherwise, failure means that some nonzero frequency has empirical mean with absolute value greater than $\varepsilon$. Thus the failure event is contained in the union, over all frequencies, of their bad events. Monotonicity and the finite union bound bound its probability by the sum of the individual probabilities. The frequency tail bound (\texttt{measure\_randomSmallBiasFrequencyBadSet\_le}) bounds each summand by $2\exp(-4n)$. There are $2^n$ frequencies, so the sum is at most $2^n\cdot2\exp(-4n)$. For $n\ge1$, the numerical estimate (\texttt{two\_pow\_mul\_two\_exp\_neg\_four\_mul\_le\_rpow\_neg}) bounds this by $2^{-n}$.

**Key facts.** `FABL.isSmallBiasedSample_zero`, `FABL.measure_randomSmallBiasFrequencyBadSet_le`, `FABL.two_pow_mul_two_exp_neg_four_mul_le_rpow_neg`.
