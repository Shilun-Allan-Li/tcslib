<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/KWiseIndependentLowerBound.lean :: FABL.choose_floor_half_le_card_of_isKWiseIndependentMultiset -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size Bound for Wise Independent Multisets

**Claim.** If a multiset of sign vectors indexed by a finite nonempty set is $k$-wise independent, then $\binom{n}{\lfloor k/2\rfloor}$ is at most the size of the indexing set.

**Proof.** Let $\mathcal F$ be the family of subsets of $\{1,\ldots,n\}$ of size at most $\lfloor k/2\rfloor$. For any $S,T\in\mathcal F$, the union-size bound gives $|S\cup T|\le 2\lfloor k/2\rfloor\le k$ (\texttt{FABL.card_union_le_two_mul_of_mem_lowDegreeFourierFamily}, together with the defining membership criterion \texttt{FABL.mem_lowDegreeFourierFamily}). The frequency-family bound for a $k$-wise independent multiset then yields $|\mathcal F|\le |\Omega|$ (\texttt{FABL.card_frequencyFamily_le_card_of_isKWiseIndependentMultiset}). Every subset of size exactly $\lfloor k/2\rfloor$ belongs to $\mathcal F$, so the number of such subsets, $\binom{n}{\lfloor k/2\rfloor}$, is at most $|\mathcal F|$. Combining the inequalities proves the result.

**Key facts.** `FABL.card_union_le_two_mul_of_mem_lowDegreeFourierFamily`, `FABL.mem_lowDegreeFourierFamily`, `FABL.card_frequencyFamily_le_card_of_isKWiseIndependentMultiset`.
