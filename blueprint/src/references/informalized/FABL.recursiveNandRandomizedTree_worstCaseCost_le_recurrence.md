<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.recursiveNandRandomizedTree_worstCaseCost_le_recurrence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Worst-Case Cost Recurrence Bound

**Claim.** For every $d$, the worst-case expected query cost of the level-$d$ randomized tree is at most $\max(F_d,T_d)$, where $F_0=T_0=1$, $F_{d+1}=2T_d$, and $T_{d+1}=F_d+T_d/2$.

**Proof.** The worst-case cost is at most the maximum of the two output-conditioned costs (\(\texttt{FABL.recursiveNandRandomizedTree_worstCaseCost_le_maxOutputCost}\)). Each of those conditioned costs is bounded by its corresponding recurrence cost (\(\texttt{FABL.recursiveNandOutputCosts_le_recurrence}\)). Taking maxima preserves these inequalities, so the worst-case cost is at most $\max(F_d,T_d)$.

**Key facts.** `FABL.recursiveNandRandomizedTree_worstCaseCost_le_maxOutputCost`, `FABL.recursiveNandOutputCosts_le_recurrence`.
