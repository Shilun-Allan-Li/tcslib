<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/OrthogonalDecomposition.lean :: FABL.permuteProductFunction_symm_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inverse action on product functions

**Claim.** For a permutation $\sigma$ of the coordinates, permuting a product function's inputs by $\sigma^{-1}$ and then by $\sigma$ leaves the function unchanged.

**Proof.** Evaluate both functions at an arbitrary input $x$. The two successive coordinate permutations compose to the identity, so each coordinate of the resulting input is the corresponding coordinate of $x$. The function therefore has the same value at every input, and the two functions are equal.
