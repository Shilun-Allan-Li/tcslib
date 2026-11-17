<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadTests.lean :: FABL.SignTester.acceptanceProbability_mem_Icc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tester Acceptance Bounds

**Claim.** For a sign tester with finite seed space and a function taking values in $[-1,1]$, its acceptance probability lies in $[0,1]$.

**Proof.** For each seed, the selected check has randomized value in $[0,1]$ (`SignQueryCheck.randomizedValue_mem_Icc`). The tester's acceptance probability is the expectation of these values over its seed law. An expectation under a probability mass function preserves the interval $[0,1]$ (`pmfExpectation_mem_Icc_zero_one`), so the acceptance probability lies in that interval.

**Key facts.** `FABL.SignQueryCheck.randomizedValue_mem_Icc`, `FABL.pmfExpectation_mem_Icc_zero_one`.
