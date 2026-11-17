<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GotsmanLinialExtremizer.lean :: FABL.tendsto_sum_shiftedBinomialProbability_div_oddMajorityInfluence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Shifted Binomial Sum Limit

**Claim.** For natural numbers $c$ and $k$ with $k\le c+1$, the sum of the first $k$ shifted binomial probabilities, each divided by the central binomial probability $a_m$, tends to $k$ as $m\to\infty$.

**Proof.** For each $j$ in the range $0\le j<k$, the hypothesis $k\le c+1$ implies $j\le c$. The termwise limit theorem for shifted binomial probabilities says that the corresponding ratio tends to $1$ (the limit of each summand is $1$) (\texttt{tendsto\_shiftedBinomialProbability\_div\_oddMajorityInfluence}). Since the sum has finitely many terms, its limit is the sum of their limits. There are exactly $k$ terms, so the limit is $k$.

**Key facts.** `FABL.tendsto_shiftedBinomialProbability_div_oddMajorityInfluence`.
