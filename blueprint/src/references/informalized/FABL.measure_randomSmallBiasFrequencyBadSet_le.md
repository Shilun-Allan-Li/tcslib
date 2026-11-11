<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/RandomSmallBias.lean :: FABL.measure_randomSmallBiasFrequencyBadSet_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Walsh Frequency Tail Bound

**Claim.** For positive $n$ and $\varepsilon>0$, the probability that a nonzero frequency has empirical Walsh mean of absolute value at least $\varepsilon$ is at most $2\exp(-4n)$.

**Proof.** Split into the cases $\gamma=0$ and $\gamma\ne0$. If $\gamma=0$, the bad event is empty by its defining nonzero-frequency condition, so its probability is zero. For $\gamma\ne0$, the sample count is positive. Each Walsh-character observation is either $-1$ or $1$, and its uniform expectation is zero because a nonzero frequency has mean zero (\texttt{expect\_vectorWalshCharacter}). The finite-sample Hoeffding bound (\texttt{measure\_finiteUniformEmpiricalMean\_sub\_expect\_ge\_le}) therefore bounds the bad-event probability by $2\exp(-m\varepsilon^2/2)$, where $m$ is the sample count. By the ceiling definition, $8n/\varepsilon^2\le m$, hence $m\varepsilon^2\ge8n$ and $-m\varepsilon^2/2\le-4n$. Monotonicity of the exponential gives the stated bound.

**Key facts.** `FABL.vectorWalshCharacter_eq_neg_one_or_one`, `FABL.randomSmallBiasSampleCount_pos`, `FABL.expect_vectorWalshCharacter`, `FABL.measure_finiteUniformEmpiricalMean_sub_expect_ge_le`.
