<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/KWiseIndependentLowerBound.lean :: FABL.exists_even_kWiseFrequencyFamily -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# An Even-Wise Frequency Family

**Claim.** For nonnegative integers $n,k$ with $k$ even, there is a family of subsets of an $n$-element set such that every union of two family members has size at most $k$, and the family has size $\sum_{j=0}^{k/2}\binom{n}{j}$.

**Proof.** Take the low-degree Fourier family with degree bound $k/2$. Each member has size at most $k/2$, so the union of any two members has size at most the sum of their sizes, hence at most $2(k/2)=k$; the cited union bound for this family gives precisely the same estimate (`FABL.card_union_le_two_mul_of_mem_lowDegreeFourierFamily`). Its cardinality is the sum of the binomial coefficients through degree $k/2$ (`FABL.card_lowDegreeFourierFamily_eq_sum_choose`). These are exactly the required properties.

**Key facts.** `FABL.card_union_le_two_mul_of_mem_lowDegreeFourierFamily`, `FABL.card_lowDegreeFourierFamily_eq_sum_choose`.
