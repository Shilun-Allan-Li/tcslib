<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.completeQuadraticLinearPrefixProof_eq_of_checks -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linear Prefix Values from Checks

**Claim.** If all the stated consistency checks hold, then for every $k\le n$ the encoded table value at linear prefix $k$ equals the sum in $\mathbb F_2$ of the encoded input coordinates with indices less than $k$.

**Proof.** Proceed by induction along the finite sequence of prefix indices. At index zero, the endpoint check says the table value is false, whose image in $\mathbb F_2$ is zero; the sum over coordinates with index less than zero is also zero. For the successor step, let the current index be $i<n$ and assume the assertion at $i$. The linear transition check identifies the encoded table value at $i+1$ with the value at $i$ plus the encoded input bit $w_i$. By the induction hypothesis, the first summand is the sum over indices below $i$. The prefix-sum increment identity (`completeQuadraticLinearPrefixBit_succ`) says that adding the encoded coordinate at $i$ gives exactly the sum over indices below $i+1$. This proves the claim at the successor and completes the induction.

**Key facts.** `FABL.completeQuadraticLinearPrefixBit_succ`.
