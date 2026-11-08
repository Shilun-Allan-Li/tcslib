<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/KWiseIndependentLowerBound.lean :: FABL.card_oddKWiseFrequencyFamily -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cardinality of the Odd Frequency Family

**Claim.** The family consisting of all subsets of the $n$ coordinates of size at most $m$, together with the specified sets formed by adjoining $i$ to an $m$-element subset of the other coordinates, has cardinality $\sum_{j=0}^{m}\binom{n}{j}+\binom{n-1}{m}$.

**Proof.** The two component families are disjoint: every set in the extension contains $i$ and has size $m+1$, while every set in the low-degree family has size at most $m$. The low-degree family has cardinality $\sum_{j=0}^{m}\binom{n}{j}$ (`FABL.card_lowDegreeFourierFamily_eq_sum_choose`), and the extension has cardinality $\binom{n-1}{m}$ (`FABL.card_oddKWiseFrequencyExtension`). Adding the cardinalities of these disjoint families gives the claimed formula.

**Key facts.** `FABL.disjoint_lowDegreeFourierFamily_oddKWiseFrequencyExtension`, `FABL.card_lowDegreeFourierFamily_eq_sum_choose`, `FABL.card_oddKWiseFrequencyExtension`.
