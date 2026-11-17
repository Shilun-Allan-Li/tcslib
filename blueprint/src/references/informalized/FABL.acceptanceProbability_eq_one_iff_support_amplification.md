<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/TestingAmplification.lean :: FABL.acceptanceProbability_eq_one_iff_support_amplification -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance with Probability One on Support

**Claim.** For a nonadaptive function tester with a finite seed space, a probability distribution on that space, and a deterministic acceptance rule, the acceptance probability on $f$ is one exactly when every seed in the distribution's support causes acceptance.

**Proof.** If the acceptance probability is one, assume for contradiction that a support seed is rejected. A support seed has strictly positive probability weight. Each summand in the acceptance expectation is at most its weight, and the rejected seed's summand is strictly smaller. The total expectation is therefore strictly less than the sum of all weights, which equals one by (\(\texttt{FABL.pmfExpectation\_const\_one}\)). This contradicts the assumed probability of one.

In the other direction, assume all support seeds are accepted. On support, the acceptance indicator is one. Off support, the seed has probability zero, so its term contributes zero. Therefore the expectation of the acceptance indicator is the expectation of the constant-one function, namely one (\(\texttt{FABL.pmfExpectation\_const\_one}\)).

**Key facts.** `FABL.pmfExpectation_const_one`.
