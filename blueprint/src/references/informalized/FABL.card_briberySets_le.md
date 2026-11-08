<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.card_briberySets_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper Bound on the Bribery Set Size

**Claim.** For $n>0$, the bribery set formed after $t$ steps with target $99/100$ has cardinality at most $t$.

**Proof.** Induct on the number of steps. Initially the bribery set is empty. At the next step, the successor formula (`FABL.briberySets_succ`) says the set is either unchanged or obtained by inserting one coordinate into the preceding set. In the insertion case its size is at most the old size plus one, so it is at most $t+1$ by the induction hypothesis. In the unchanged case the old bound $t$ already implies the desired bound $t+1$.

**Key facts.** `FABL.briberySets_succ`.
