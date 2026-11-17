<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPDerandomization.lean :: FABL.maxLinearScopeSplitEquiv_fst_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First coordinate of the scope decomposition

**Claim.** For an assignment on the variables, the first component of its scope decomposition, evaluated at a position in the constraint scope, equals the assignment at the variable in that position.

**Proof.** The decomposition first restricts the assignment to variables in the range of the scope embedding, then reindexes that restriction by the scope’s position set. Evaluating this first component at $i$ therefore evaluates the original assignment at the variable represented by the image of $i$ under the scope embedding. The inverse of the embedding’s range equivalence sends that image back to $i$; thus the value is exactly the assignment at the scope variable in position $i$.
