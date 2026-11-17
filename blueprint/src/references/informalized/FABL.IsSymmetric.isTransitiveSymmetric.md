<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/SocialChoiceFunctions/Examples.lean :: FABL.IsSymmetric.isTransitiveSymmetric -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symmetry Implies Transitive Symmetry

**Claim.** If a function on the sign cube is invariant under every coordinate permutation, then for any two coordinates there is a permutation sending the first to the second under which the function remains invariant.

**Proof.** Given coordinates $i$ and $i'$, take the transposition that swaps them. This permutation sends $i$ to $i'$. Since the function is invariant under every coordinate permutation by hypothesis, it is invariant under this transposition in particular. This also covers the case $i=i'$, when the transposition is the identity.
