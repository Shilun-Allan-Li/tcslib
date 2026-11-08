<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeSymmetrization.lean :: FABL.exists_booleanFunctionSymmetry_apply_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transitivity of the symmetry group

**Claim.** If the function has a symmetry carrying any specified coordinate to any other, then for every pair of coordinates there is an element of its symmetry group carrying the first coordinate to the second.

**Proof.** Apply the transitivity hypothesis to the given coordinates $i,j$. It provides a coordinate permutation $\pi$ with $\pi(i)=j$ that leaves the function invariant under input permutation. The invariance condition says precisely that $\pi$ belongs to the function's symmetry group, so this same permutation gives the required group element.
