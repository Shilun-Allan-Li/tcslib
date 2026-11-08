<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/LowDegree.lean :: LowDegreeTest.RM_test_completeness -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completeness of the Reed–Muller test

**Claim.** If $f$ belongs to $\mathrm{RM}(d,n)$, then the $(d+1)$-fold derivative test accepts $f$ with probability exactly $1$.

**Proof.** Membership in $\mathrm{RM}(d,n)$ means precisely that $f$ satisfies the Boolean degree-at-most-$d$ condition. The completeness theorem for that condition states that the test's acceptance probability is $1$ (`LowDegreeTest.degree_test_completeness`), giving the claim.

**Key facts.** `LowDegreeTest.degree_test_completeness`.
