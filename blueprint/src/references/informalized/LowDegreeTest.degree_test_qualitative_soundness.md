<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/LowDegree.lean :: LowDegreeTest.degree_test_qualitative_soundness -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Qualitative soundness of the degree test

**Claim.** If the $\pm1$ lift of $f$ has a nontrivial $(d+1)$-fold derivative, then the degree test accepts with probability strictly less than $1$.

**Proof.** First, the Gowers norm power is at most $1$: each product in its defining average is either $1$ or $-1$ (`gowers_product_pm1`), so each summand is at most $1$, and averaging preserves this bound. The degree hypothesis fails, so the norm-equals-one characterization (`gowers_norm_eq_one_iff`) shows that this norm power is not $1$. Together these give a strict upper bound of $1$. Finally, the acceptance-probability formula (`degree_test_accept_prob_eq`) expresses the acceptance probability as half of one plus this norm power, which is therefore strictly less than $1$.

**Key facts.** `LowDegreeTest.gowers_product_pm1`, `LowDegreeTest.gowers_norm_eq_one_iff`, `LowDegreeTest.degree_test_accept_prob_eq`.
