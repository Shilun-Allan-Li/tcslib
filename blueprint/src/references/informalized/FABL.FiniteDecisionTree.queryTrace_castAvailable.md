<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.FiniteDecisionTree.queryTrace_castAvailable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Trace Under Availability Identification

**Claim.** If the available coordinate sets $A$ and $B$ are equal, identifying a tree over $A$ as a tree over $B$ leaves its query trace unchanged on every input.

**Proof.** The equality of available sets lets us substitute $B=A$. Under this identification, the cast of the tree is just the same tree, so its query trace is unchanged.
