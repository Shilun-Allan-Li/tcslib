<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeSymmetrization.lean :: FABL.RandomizedDecisionTree.functionRevealment_zero_dimension -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero Function Revealment in Dimension Zero

**Claim.** In dimension zero, the infimum of the revealments of randomized decision trees computing any given function is zero.

**Proof.** The probability mass function has nonempty support, so the input alphabet is nonempty. A complete deterministic tree computing the function therefore exists (`completeTree_computes`), and viewing it as randomized gives a candidate whose revealment is zero in dimension zero (`revealment_zero_dimension`). Since function revealment is an infimum over candidates, it is at most this tree’s revealment, hence at most zero (`functionRevealment_le_revealment`). Conversely, function revealment is nonnegative (`functionRevealment_nonneg`). The two inequalities give equality with zero.

**Key facts.** `FABL.FiniteDecisionTree.completeTree_computes`, `FABL.RandomizedDecisionTree.functionRevealment_le_revealment`, `FABL.RandomizedDecisionTree.revealment_zero_dimension`, `FABL.RandomizedDecisionTree.functionRevealment_nonneg`.
