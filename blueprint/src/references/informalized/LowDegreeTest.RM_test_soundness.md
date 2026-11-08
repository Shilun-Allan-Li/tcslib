<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/LowDegree.lean :: LowDegreeTest.RM_test_soundness -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Soundness of the low-degree test

**Claim.** For $d\ge1$, if $f$ is $\varepsilon$-far from every Boolean function of degree at most $d$, then the $(d+1)$-fold derivative test accepts $f$ with probability at most $1-\varepsilon$.

**Proof.** The quantitative soundness theorem states exactly that under the degree lower bound and the stated distance hypothesis, the acceptance probability is at most $1-\varepsilon$ (`LowDegreeTest.degree_test_quantitative_soundness`). Applying it yields the result.

**Key facts.** `LowDegreeTest.degree_test_quantitative_soundness`.
