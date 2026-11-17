<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/CircuitInfluence.lean :: FABL.expect_maxRestrictedDecisionTreeDepth_le_clog_add_two_of_failure_le_quarter -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected Maximum Restricted Depth

**Claim.** Under the stated quarter-power tail bound for each function’s restricted decision tree depth, the expected maximum depth across the family is at most $\lceil\log_2(m+1)\rceil+2$.

**Proof.** Set $q=\lceil\log_2(m+1)\rceil$ and write $D$ for the maximum restricted depth at a given restriction. For every nonnegative integer $D$, the elementary estimate $D\le q+2^D/2^q$ holds (`natCast_le_add_pow_div_pow`). Also, the power of two of a finite maximum is at most one plus the sum of the individual powers: $2^D\le 1+\sum_i 2^{d_i}$ (`two_pow_sup_le_one_add_sum`), where $d_i$ is the restricted depth of the $i$th function.

Average these inequalities over random restrictions. Monotonicity of the expectation (`expectRandomRestriction_mono`), its additivity and constant rule (`expectRandomRestriction_add`, `expectRandomRestriction_const`), and interchange of a finite sum with expectation (`sum_expectRandomRestriction`) give $\mathbb E[2^D]\le 1+\sum_i\mathbb E[2^{d_i}]$. The single-function moment bound from the assumed tail estimates gives each summand at most $2$ (`expect_two_pow_restrictedDecisionTreeDepth_le_two_of_failure_le_quarter`), so $\mathbb E[2^D]\le1+2m$.

Finally, the definition of $q$ ensures $m+1\le2^q$ (`Nat.le_pow_clog`). Averaging $D\le q+2^D/2^q$ and using the preceding moment estimate yields $\mathbb E[D]\le q+(1+2m)/2^q$. Since $1+2m\le2(m+1)\le2^{q+1}$, this is at most $q+2$, as claimed.

**Key facts.** `FABL.natCast_le_add_pow_div_pow`, `FABL.two_pow_sup_le_one_add_sum`, `FABL.expectRandomRestriction_mono`, `FABL.expectRandomRestriction_add`, `FABL.expectRandomRestriction_const`, `FABL.sum_expectRandomRestriction`, `FABL.expect_two_pow_restrictedDecisionTreeDepth_le_two_of_failure_le_quarter`.
