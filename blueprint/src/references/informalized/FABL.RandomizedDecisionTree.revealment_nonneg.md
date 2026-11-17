<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeSymmetrization.lean :: FABL.RandomizedDecisionTree.revealment_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative revealment

**Claim.** The revealment of $T$ under the independent product input distribution is nonnegative.

**Proof.** If the coordinate set is empty, revealment is defined to be $0$. Otherwise choose any coordinate. Its query probability is nonnegative ($\texttt{FABL.RandomizedDecisionTree.queryProbability\_nonneg}$), and it is at most the supremum defining revealment. Hence revealment is nonnegative.

**Key facts.** `FABL.RandomizedDecisionTree.queryProbability_nonneg`.
