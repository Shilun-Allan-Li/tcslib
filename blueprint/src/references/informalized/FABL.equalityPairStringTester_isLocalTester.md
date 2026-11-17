<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/TestingExercises.lean :: FABL.equalityPairStringTester_isLocalTester -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Local testing of equal pairs

**Claim.** For positive $n$, the tester that samples a pair uniformly, queries both values, and accepts exactly when they agree is a local tester for strings equal within each pair, with rate $1$.

**Proof.** The rate is positive. If $w$ has equal values in every pair, then every sampled pair is accepted, so its rejection probability is zero. For the soundness condition, let $\varepsilon\in(0,1]$ and suppose every string satisfying the pair-equality property is at relative Hamming distance greater than $\varepsilon$ from $w$. Repair $w$ by copying the first value of each pair to both positions. The repaired string satisfies the property (`equalityPairRepair_mem`), so its distance from $w$ is greater than $\varepsilon$. Each pair with unequal original values contributes exactly one changed position among its two positions; consequently twice this relative distance equals the fraction of pairs whose values differ (`two_mul_relativeHammingDist_equalityPairRepair`). The rejection probability is precisely that fraction (`equalityPairStringTester_rejectionProbability`). It is therefore greater than $2\varepsilon$, and hence greater than the required rate-$1$ threshold $\varepsilon$.

**Key facts.** `FABL.equalityPairRepair_mem`, `FABL.two_mul_relativeHammingDist_equalityPairRepair`, `FABL.equalityPairStringTester_rejectionProbability`.
