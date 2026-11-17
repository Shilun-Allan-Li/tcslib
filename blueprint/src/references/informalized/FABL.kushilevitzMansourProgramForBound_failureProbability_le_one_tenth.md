<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/KushilevitzMansour.lean :: FABL.kushilevitzMansourProgramForBound_failureProbability_le_one_tenth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Learner Failure Probability

**Claim.** Under the stated spectral concentration and family-size hypotheses, the bounded Kushilevitz–Mansour learner has failure probability at most $1/10$.

**Proof.** First, spectral concentration together with the family-size bound implies that $M$ is positive (the positive-family-bound lemma, `positive_familyBound_of_spectrum_concentrated`). Thus the bounded program takes its positive-$M$ branch and is exactly the Kushilevitz–Mansour program with this bound. The failure-probability estimate for that program (`kushilevitzMansourProgram_failureProbability_le_one_tenth`) applies under the same concentration and family-size hypotheses and gives the required upper bound.

**Key facts.** `FABL.positive_familyBound_of_spectrum_concentrated`, `FABL.kushilevitzMansourProgram_failureProbability_le_one_tenth`.
