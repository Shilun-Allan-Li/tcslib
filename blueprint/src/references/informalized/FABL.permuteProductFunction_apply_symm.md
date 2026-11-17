<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/OrthogonalDecomposition.lean :: FABL.permuteProductFunction_apply_symm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inverse action on product functions

**Claim.** For a permutation $\sigma$ of the coordinates, permuting a product function's inputs by $\sigma$ and then by $\sigma^{-1}$ leaves the function unchanged.

**Proof.** Evaluate both functions at an arbitrary input $x$. Their values agree because the two successive coordinate permutations send each coordinate back to its original position: for every coordinate $i$, the resulting input has value $x(i)$. Hence the functions agree at every input and are equal.
