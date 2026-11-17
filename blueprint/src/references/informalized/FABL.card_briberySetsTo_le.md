<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.card_briberySetsTo_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size of the Bribery Set After Finitely Many Steps

**Claim.** After $t$ steps of the specified bribery procedure, the set of chosen coordinates has cardinality at most $t$.

**Proof.** Proceed by induction on $t$. At time zero the set is empty, so the bound holds. For the induction step, the next set is either unchanged or is formed by inserting one coordinate into the previous set, according to whether the current mean is below the target. In the insertion case its cardinality is at most the previous cardinality plus one, hence at most $t+1$ by induction. In the unchanged case its cardinality is at most $t$, and therefore at most $t+1$. The recursive description of the procedure is expressed by the successor formula (`FABL.briberySetsTo_succ`).

**Key facts.** `FABL.briberySetsTo_succ`.
