<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianSharpLevelOneCounterexample.lean :: FABL.normalizedRademacherSum_neg_counterexample -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Oddness of the Normalized Sign Sum

**Claim.** For every natural number $n$ and every sign vector $x$, negating all coordinates negates the normalized sum.

**Proof.** Expand the normalized sum as a linear form. For each sign $s$, its value is either $1$ or $-1$; in either case, the value of $-s$ is the negative of the value of $s$. Thus each term in the linear form changes sign when the input vector is negated. Summing these identities gives the negative of the original sum.
