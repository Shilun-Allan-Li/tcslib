<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/LowDegree.lean :: LowDegreeTest.degree_test_completeness -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completeness of the degree test

**Claim.** If every $(d+1)$-fold Gowers product of the $\pm1$ lift of $f$ equals $1$, then the degree test accepts with probability exactly $1$.

**Proof.** The acceptance probability is $(1+\|(-1)^f\|_{U^{d+1}}^{2^{d+1}})/2$ by the acceptance-probability formula (`degree_test_accept_prob_eq`). The norm-equals-one characterization (`gowers_norm_eq_one_iff`) says that the degree hypothesis makes the norm power equal to $1$. Substitution gives $(1+1)/2=1$.

**Key facts.** `LowDegreeTest.degree_test_accept_prob_eq`, `LowDegreeTest.gowers_norm_eq_one_iff`.
