<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticCircuitReduction.lean :: FABL.quadraticCircuitSemanticPCPPReduction_proofLength_le_explicit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quadratic reduction proof length bound

**Claim.** For a Boolean circuit with positive input length, the proof length of its quadratic semantic PCPP reduction is at most $2^{12(n+g+2)^2}$, where $g$ is the number of gates.

**Proof.** Let $N=1+n+g$ and $B=2^{3(N+1)^2}$. The quadratic circuit proof length bound gives a bound of $3\cdot 2^{(n+g+1)^2}$ (\texttt{circuitQuadraticPCPPProofLength_le_three_mul_two_pow_square}). Since $n+g+1\le N+1$ and $(N+1)^2\le 3(N+1)^2$, this is at most $3B$. The four-query verifier's seed space has size at most $6B$ (\texttt{circuitQuadraticFourQueryPCPPSystem_descriptionSize_le}). The three-query conversion defines the new proof length as the old proof length plus $64$ times this seed-space size (\texttt{quadraticCircuitSemanticPCPPReduction_proofLength}). Thus it is at most $3B+64(6B)\le512B=2^{3(N+1)^2+9}$. Finally, $N+1=n+g+2$, and $1\le(n+g+2)^2$, so $3(n+g+2)^2+9\le12(n+g+2)^2$. Monotonicity of powers of $2$ gives the stated bound.

**Key facts.** `FABL.BooleanCircuit.circuitQuadraticPCPPProofLength_le_three_mul_two_pow_square`, `FABL.BooleanCircuit.circuitQuadraticFourQueryPCPPSystem_descriptionSize_le`, `FABL.quadraticCircuitSemanticPCPPReduction_proofLength`.
