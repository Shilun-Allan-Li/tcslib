<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.innerProductPrefixBit_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successive inner product prefixes

**Claim.** When $k<m$, the prefix sum through the first $k+1$ coordinate pairs equals the prefix sum through the first $k$ pairs plus the product in $\mathbb{F}_2$ of the two bits in pair $k$.

**Proof.** The prefix of length $k+1$ is the prefix of length $k$ together with its last summand, indexed by $k$. Since $k<m$, the condition selecting a valid pair holds for this last index, so that summand is exactly the product in pair $k$. This gives the stated recurrence.
