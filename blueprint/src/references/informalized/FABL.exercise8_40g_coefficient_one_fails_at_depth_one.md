<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.exercise8_40g_coefficient_one_fails_at_depth_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth-one cost exceeds the growth rate

**Claim.** The worst-case expected query cost of the recursive randomized decision tree at depth one is not at most $\lambda$, where $\lambda=(1+\sqrt{33})/4$.

**Proof.** At depth one, the worst-case expected query cost is $2$ (\texttt{FABL.recursiveNandRandomizedTree\_worstCaseCost\_one}). The growth rate satisfies $\lambda<2$ (\texttt{FABL.nandGrowthRate\_lt\_two}), so $2>\lambda$. Thus the worst-case cost cannot be at most $\lambda$.

**Key facts.** `FABL.recursiveNandRandomizedTree_worstCaseCost_one`, `FABL.nandGrowthRate_lt_two`.
