<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/ModPow.lean :: Complexity.BinArith.size_lt_of_two_mul_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strict Decrease of Binary Size

**Claim.** If $P>0$ and $2P'\le P$, then the binary size of $P'$ is strictly less than the binary size of $P$.

**Proof.** Let $k$ be the binary size of $P$. Since $P>0$, $k>0$, and the defining size bound gives $P<2^k$. Hence $2P'\le P<2^k=2\cdot2^{k-1}$, so $P'<2^{k-1}$. The characterization of binary size by powers of two then gives $\operatorname{size}(P')\le k-1<k=\operatorname{size}(P)$.
