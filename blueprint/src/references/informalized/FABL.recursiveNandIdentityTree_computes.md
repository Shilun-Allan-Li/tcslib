<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.recursiveNandIdentityTree_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Identity Tree Computes the Initial Function

**Claim.** On a single sign input, the decision tree that queries its sole coordinate and returns the observed sign computes the depth-zero recursive NAND function.

**Proof.** For any input, evaluation of the tree queries coordinate $0$ and returns the sign found there. By definition, the depth-zero recursive NAND function returns precisely that coordinate. Thus the two functions agree on every input.
