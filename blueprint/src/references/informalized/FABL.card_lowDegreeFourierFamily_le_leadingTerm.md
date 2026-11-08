<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ThresholdFunctionCounting.lean :: FABL.card_lowDegreeFourierFamily_le_leadingTerm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Leading-Term Bound for Low-Degree Subsets

**Claim.** When $n>0$, the number of subsets of an $n$-element set having size at most $k$ is at most $n^k+k n^{k-1}$.

**Proof.** Use the counting formula (`FABL.card_lowDegreeFourierFamily_eq_sum_choose`) to express the count as the sum of $\binom{n}{j}$ for $0\le j\le k$. If $k=0$, the family contains only the empty set, and the claimed bound is $1$. Otherwise write the degree cutoff as $k+1$. Split off the final term $\binom{n}{k+1}$. It is at most $n^{k+1}$. For each earlier index $j\le k$, the bound $\binom{n}{j}\le n^j$, together with $n>0$, gives $\binom{n}{j}\le n^k$. Thus the earlier terms sum to at most $(k+1)n^k$. Adding the bounds gives $n^{k+1}+(k+1)n^k$, which is the stated expression after writing the original cutoff as $k+1$.

**Key facts.** `FABL.card_lowDegreeFourierFamily_eq_sum_choose`.
