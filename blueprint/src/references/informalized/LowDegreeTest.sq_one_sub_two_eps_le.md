<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/LowDegree.lean :: LowDegreeTest.sq_one_sub_two_eps_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Squaring contracts on the unit interval

**Claim.** If $0\le\varepsilon\le\tfrac12$, then $(1-2\varepsilon)^2\le1-2\varepsilon$.

**Proof.** The hypotheses imply $0\le1-2\varepsilon\le1$. For any $t$ in this interval, $t^2\le t$, since $t-t^2=t(1-t)$ is nonnegative. Taking $t=1-2\varepsilon$ proves the inequality.
