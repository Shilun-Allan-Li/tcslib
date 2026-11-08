<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/KushilevitzMansour.lean :: FABL.kushilevitzMansourProgram_failureProbability_le_one_tenth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Failure probability of the learner

**Claim.** Under the stated Fourier concentration and cardinality hypotheses, the probability that the Kushilevitz–Mansour output hypothesis has relative Hamming distance greater than $\varepsilon$ from the target is at most $1/10$.

**Proof.** Set $\tau=\varepsilon/(4M)$, the threshold used by the two-stage program. Apply the failure bound for a bind (`FABL.LearningProgram.eventProbability_bind_le_add`) with the first-stage bad event being that the Goldreich–Levin state is not correct and with the final bad event being that the output has relative Hamming error greater than $\varepsilon$. The first-stage failure probability is at most $1/20$ by the Goldreich–Levin query-program bound (`FABL.goldreichLevinQueryProgram_incorrectProbability_le_one_twentieth`).

For any state outside that bad event, correctness supplies a complete active family, a cardinality bound, and the soundness and cap properties needed by the second stage. Completeness transfers the assumed concentration on the initial family to concentration on the active family, with error threshold $\varepsilon/2$ (`FABL.isFourierSpectrumConcentratedOn_of_goldreichLevin_complete`). Such a family is nonempty (`FABL.finiteFamily_nonempty_of_spectrum_concentrated`), so the second stage takes its estimator branch. The finite-family estimator's failure probability is at most its confidence parameter, here $1/20$ (`FABL.queriedFiniteFamilyFourierEstimatorProgramWithConfidence_failureProbability_le`). Thus the bind inequality bounds total failure by $1/20+1/20=1/10$.

**Key facts.** `FABL.LearningProgram.eventProbability_bind_le_add`, `FABL.goldreichLevinQueryProgram_incorrectProbability_le_one_twentieth`, `FABL.isFourierSpectrumConcentratedOn_of_goldreichLevin_complete`, `FABL.finiteFamily_nonempty_of_spectrum_concentrated`, `FABL.queriedFiniteFamilyFourierEstimatorProgramWithConfidence_failureProbability_le`.
