<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/LowDegree.lean :: LowDegreeTest.gowers_norm_le_of_far_d1 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gowers norm bound from distance to low degree

**Claim.** If $f$ is $\varepsilon$-far from degree at most $d$, with $d\ge1$, then the fourth power of the $U^2$ norm of its sign lift is at most $1-2\varepsilon$.

**Proof.** The bound for functions far from degree at most $d$ first gives $\|F\|_{U^2}^4\le (1-2\varepsilon)^2$ (`gowers_U2_le_of_far`). The same far-from-degree hypothesis, together with $d\ge1$, implies $\varepsilon\le 1/2$ (`eps_le_half_of_far`). Since also $0\le\varepsilon$, the quantity $1-2\varepsilon$ lies in $[0,1]$, and hence its square is at most itself: $(1-2\varepsilon)^2\le1-2\varepsilon$ (`sq_one_sub_two_eps_le`). Combining the inequalities proves the claim.

**Key facts.** `LowDegreeTest.gowers_U2_le_of_far`, `LowDegreeTest.eps_le_half_of_far`, `LowDegreeTest.sq_one_sub_two_eps_le`.
