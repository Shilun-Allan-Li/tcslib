<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.FiniteDecisionTree.queryTrace_weaken -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Trace Unchanged by Enlarging Availability

**Claim.** If $A\subseteq B$, viewing a tree whose queries are available in $A$ as a tree with queries available in $B$ leaves its query trace unchanged on every input.

**Proof.** Proceed by induction on the tree, allowing the larger set $B$ to vary in the induction. A leaf has empty trace before and after weakening. At a query node, weakening preserves the root coordinate and weakens the selected child from the set obtained by erasing that coordinate from $A$ to the corresponding erased set from $B$. The inclusion between these erased sets follows from $A\subseteq B$. By the induction hypothesis the selected child’s trace is unchanged; prefixing the common root query proves the claim.
