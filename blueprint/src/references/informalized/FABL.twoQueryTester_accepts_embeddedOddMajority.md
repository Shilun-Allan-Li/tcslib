<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/TestingAmplification.lean :: FABL.twoQueryTester_accepts_embeddedOddMajority -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance of embedded odd majority

**Claim.** A two-query nonadaptive tester that accepts every coordinate dictator with probability $1$ also accepts, with probability $1$, the majority function on the first $d$ coordinates whenever $d$ is odd and $d\le n$.

**Proof.** Acceptance probability $1$ is equivalent to acceptance at every seed in the support of the tester's seed distribution (`FABL.acceptanceProbability_eq_one_iff_support_amplification`). Fix such a seed. The transcript produced by the embedded odd majority at this seed agrees with the transcript produced by some coordinate dictator, by the two-query transcript lemma (`FABL.twoQuery_embeddedMajority_transcript_eq_dictator`). The dictator is accepted at this seed, since its acceptance probability is $1$ and the seed is in the support. Because the two transcripts agree, the tester's acceptance decision agrees as well, so it accepts the embedded majority at the chosen seed. This holds for every seed in the support; the same characterization of acceptance probability $1$ now gives the conclusion.

**Key facts.** `FABL.acceptanceProbability_eq_one_iff_support_amplification`, `FABL.twoQuery_embeddedMajority_transcript_eq_dictator`.
