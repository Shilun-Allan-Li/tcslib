<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPConstructions.lean :: FABL.acceptanceProbability_eq_one_iff_accepts_on_support -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance with Probability One and Support

**Claim.** For a nonadaptive function tester with seed distribution $\nu$, the acceptance probability on $f$ is $1$ if and only if the tester accepts $f$ for every seed in the support of $\nu$.

**Proof.** Suppose first that the acceptance probability is one. If some seed in the support were rejected, its probability weight would be positive. In the finite sum defining acceptance probability, each seed contributes at most its probability weight, and this rejected seed contributes strictly less. Hence the total would be strictly below the sum of all probability weights, which is one—a contradiction.

Conversely, suppose every seed in the support is accepted. For seeds in the support, the acceptance indicator equals one. For seeds outside the support, the distribution assigns probability zero, so their contributions to the expectation vanish regardless of the acceptance indicator. Thus the acceptance probability equals the expectation of the constant-one function, which is one (\(\texttt{FABL.pmfExpectation\_const\_one}\)).

**Key facts.** `FABL.pmfExpectation_const_one`.
