<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/KWiseIndependentLowerBound.lean :: FABL.exists_odd_kWiseFrequencyFamily -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# An Odd-Wise Frequency Family

**Claim.** For positive $n$ and odd $k$, there is a family of subsets of $[n]$ with every pairwise union of size at most $k$ and with the stated binomial-sum cardinality.

**Proof.** Choose any coordinate $i\in[n]$, possible since $n>0$, and take the family `oddKWiseFrequencyFamily n (k/2) i`. Its defining pairwise-union estimate (`card_union_le_two_mul_add_one_of_mem_oddKWiseFrequencyFamily`) bounds each union size by $2(k/2)+1$. Since $k$ is odd, this quantity equals $k$. The family cardinality formula (`card_oddKWiseFrequencyFamily`) gives the sum through index $k/2$ plus $\binom{n-1}{k/2}$. For odd $k$, $k/2=(k-1)/2$, so this is exactly the asserted cardinality.

**Key facts.** `FABL.card_union_le_two_mul_add_one_of_mem_oddKWiseFrequencyFamily`, `FABL.card_oddKWiseFrequencyFamily`.
