<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/DictatorTesting.lean :: FABL.naeFunctionTester_acceptanceProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance and Condorcet Probability

**Claim.** For the tester that samples a ranking profile uniformly and accepts when the three societal pairwise outcomes are not all equal, its acceptance probability equals the probability that the societal outcome has a Condorcet winner.

**Proof.** By definition, the tester's acceptance probability is the expectation under its seed distribution of the indicator that its acceptance predicate holds. Its seed is a ranking profile, and its distribution is uniform; the uniform-PMF expectation identity rewrites this as the ordinary uniform expectation over profiles (`FABL.pmfExpectation_uniformPMF_eq_expect`). Fix any profile. The transcript entries are the three pairwise vote vectors evaluated by the Boolean social choice function, by the transcript evaluation rule (`FABL.NonadaptiveFunctionTester.transcript_apply`). Thus the tester accepts exactly when the three resulting societal outcomes are not all equal. The Condorcet-winner indicator agrees with the indicator of this not-all-equal condition (`FABL.condorcetWinnerIndicator_eq_nae3`). The two indicators therefore agree profile by profile, and so their expectations, hence the two probabilities, are equal.

**Key facts.** `FABL.pmfExpectation_uniformPMF_eq_expect`, `FABL.condorcetWinnerIndicator_eq_nae3`, `FABL.NonadaptiveFunctionTester.transcript_apply`.
