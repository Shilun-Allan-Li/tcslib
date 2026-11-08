<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.innerProductLinearPCPPDescription_proofLength_le_twice_inputLength -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Proof length bound

**Claim.** For every positive natural number $m$, the proof length of the inner product PCPP description on inputs of length $2m$ is at most $4m$.

**Proof.** The description has proof length $m+(m+1)$. Since $m$ is positive, $1\le m$, so $m+(m+1)\le m+2m=3m\le 4m$. This is the claimed bound.
