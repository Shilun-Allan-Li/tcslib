<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/LinearThresholdInfluence.lean :: FABL.affineLinearRemainder_permute_swap_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate Swap Identity for an Affine Remainder

**Claim.** For distinct coordinates $i,j$, swapping those coordinates in the input to the affine remainder that omits $i$ gives the remainder omitting both $i,j$, plus $a_jx_i$.

**Proof.** Expand the remainder over all coordinates except $i$. Since $j\ne i$, its term occurs in that sum; separate it off. For every remaining coordinate $k$, we have $k\ne i$ and $k\ne j$, so the swap leaves its input value $x_k$ unchanged. At the separated coordinate $j$, the swap makes the input value $x_i$. The remaining sum is thus the remainder omitting both coordinates, and the separated term is $a_jx_i$, proving the identity.
