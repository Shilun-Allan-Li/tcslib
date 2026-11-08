<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/SocialChoiceFunctions/Examples.lean :: FABL.andFunction_transitiveSymmetric -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transitive symmetry of AND

**Claim.** For every $n$, the AND function is invariant under coordinate permutations, and any coordinate can be sent to any other by such a permutation; hence it is transitively symmetric.

**Proof.** The function is symmetric (`FABL.andFunction_symmetric`): permuting the coordinates does not change whether every coordinate is $-1$, so it does not change the output. The general fact that a symmetric function on the Boolean cube is transitively symmetric (`FABL.IsSymmetric.isTransitiveSymmetric`) then supplies, for each pair of coordinates, a permutation sending the first to the second while preserving the function.

**Key facts.** `FABL.andFunction_symmetric`, `FABL.IsSymmetric.isTransitiveSymmetric`.
