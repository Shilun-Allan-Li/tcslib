<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.completeQuadraticLinearPrefixBit_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Increment of the Prefix Sum

**Claim.** For $k<n$, the prefix sum through bound $k+1$ equals the prefix sum through bound $k$ plus the encoded coordinate $w_k$.

**Proof.** In the sum defining the prefix with bound $k+1$, each coordinate with index less than $k$ contributes its existing term from the prefix with bound $k$. The coordinate with index exactly $k$ contributes the encoded bit $w_k$, and every coordinate with index greater than $k$ contributes zero. Therefore the sum separates into the earlier prefix terms and the single new term. The sum of the terms supported only at the coordinate $k$ is exactly that encoded bit, giving the stated identity.
