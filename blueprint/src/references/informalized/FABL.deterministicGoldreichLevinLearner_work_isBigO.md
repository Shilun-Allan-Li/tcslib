<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DeterministicGoldreichLevin.lean :: FABL.deterministicGoldreichLevinLearner_work_isBigO -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial work growth

**Claim.** The charged work of the deterministic Goldreich–Levin learner is $O(T^{100})$ as the task scale $T$ tends to infinity.

**Proof.** Fix a task. The polynomial work bound for the learner gives an upper bound on its charged work by the input’s polynomial runtime bound (deterministicGoldreichLevinLearner_work_polynomial_le). By the runtime scale factor bounds, the runtime scale is at least $1$, so it is nonnegative. The work and the hundredth power of the scale are therefore both nonnegative, and their absolute values equal themselves. Rewriting the polynomial runtime bound using the definition of task scale gives the pointwise estimate $\mathrm{work}\le 2^{170}T^{100}$. Since this holds for every task, it supplies a uniform bound on the filter of tasks whose scales tend to infinity, which is precisely the asserted Big-O estimate.

**Key facts.** `FABL.deterministicGoldreichLevinLearner_work_polynomial_le`, `FABL.DeterministicGoldreichLevinInput.runtimeScale_factor_bounds`.
