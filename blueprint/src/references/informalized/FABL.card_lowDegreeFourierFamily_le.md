<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/LowDegree.lean :: FABL.card_lowDegreeFourierFamily_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound for Low-Degree Subsets

**Claim.** The number of subsets of an $n$-element set having size at most $k$ is at most $(k+1)(n+1)^k$.

**Proof.** By the counting formula (`FABL.card_lowDegreeFourierFamily_eq_sum_choose`), the cardinality is the sum of $\binom{n}{j}$ over $0\le j\le k$. Each summand is at most $(n+1)^j$, and hence at most $(n+1)^k$, since $j\le k$ and $n+1\ge1$. There are $k+1$ terms, so their sum is at most $(k+1)(n+1)^k$.

**Key facts.** `FABL.card_lowDegreeFourierFamily_eq_sum_choose`.
