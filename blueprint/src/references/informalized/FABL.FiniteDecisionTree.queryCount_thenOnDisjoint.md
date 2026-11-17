<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.FiniteDecisionTree.queryCount_thenOnDisjoint -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Query Count for Sequential Disjoint Trees

**Claim.** When a tree using $A$ is followed by a tree selected by its output and using disjoint coordinates $B$, the combined query count on $x$ is the first tree's count plus the selected second tree's count, both on $x$.

**Proof.** The query-trace identity for sequential composition states that the combined trace is the trace of $T$ followed by the trace of $K(T(x))$, each evaluated on the same input (`queryTrace_thenOnDisjoint`). The length of a concatenated pair of lists is the sum of their lengths. Using that query count is trace length gives the asserted sum.

**Key facts.** `FABL.FiniteDecisionTree.queryTrace_thenOnDisjoint`.
