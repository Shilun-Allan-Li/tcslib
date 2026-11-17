<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.FiniteDecisionTree.queryTrace_thenOnDisjoint -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Trace of Sequential Composition

**Claim.** When a tree querying $A$ is followed by a tree selected according to its output and querying $B$, for disjoint $A$ and $B$, the composed tree’s trace is the first tree’s trace followed by the selected second tree’s trace.

**Proof.** Proceed by induction on the first tree. If it is a leaf with value $a$, the composed tree is the second tree indexed by $a$, weakened to the union of available sets. Weakening leaves the trace unchanged (`queryTrace_weaken`), and the first tree’s trace is empty, so the claimed concatenation follows. At a query node, the composed tree makes that same first query and continues with the composition of the selected child and the same second-tree family. Casting its available set does not change the trace (`queryTrace_castAvailable`). The induction hypothesis identifies the remainder as the selected child’s trace followed by the trace of the second tree at that child’s output. Since the original tree and its selected child have the same output on the input, this is exactly the claimed concatenation after prefixing the query.

**Key facts.** `FABL.FiniteDecisionTree.queryTrace_weaken`, `FABL.FiniteDecisionTree.queryTrace_castAvailable`.
