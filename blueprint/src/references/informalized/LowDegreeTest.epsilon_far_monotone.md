<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/LowDegree.lean :: LowDegreeTest.epsilon_far_monotone -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of degree farness

**Claim.** If $d'\le d$ and $f$ is $\varepsilon$-far from degree at most $d$, then it is also $\varepsilon$-far from degree at most $d'$.

**Proof.** The bounds $0\le\varepsilon\le1$ carry over unchanged. For any function of degree at most $d'$, repeatedly apply the fact that a degree bound remains valid when increased by one (`degree_le_succ`); since $d'\le d$, this gives degree at most $d$. The original farness hypothesis then says its distance from $f$ is at least $\varepsilon$.

**Key facts.** `LowDegreeTest.degree_le_succ`.
