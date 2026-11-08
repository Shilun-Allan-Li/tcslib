<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitReindex.lean :: BoolCircuit.TreeCircuit.reidx_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation Under Reindexing

**Claim.** Evaluating a reindexed circuit under an assignment $g$ gives the same result as evaluating the original circuit under the assignment $g\circ f$.

**Proof.** Proceed by structural induction. For a literal, its reindexed input index is the image under $f$ of the original index, while its sign is unchanged. Hence its evaluation under $g$ is exactly the original literal's evaluation under $g\circ f$. For a gate, reindexing maps the children and leaves the gate type unchanged. In either the AND or OR case, evaluation folds the corresponding operation over the child list. Mapping a list commutes with this fold, and the induction hypothesis identifies the evaluation of each mapped child with that of the original child under $g\circ f$. Applying this to the head and then the tail of the list proves equality of the folds; the empty-list case has the same identity value on both sides.

**Key facts.** `BoolCircuit.TreeCircuit.ind`.
