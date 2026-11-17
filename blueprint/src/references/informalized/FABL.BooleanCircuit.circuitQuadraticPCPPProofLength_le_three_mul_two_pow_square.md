<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticCircuitReduction.lean :: FABL.BooleanCircuit.circuitQuadraticPCPPProofLength_le_three_mul_two_pow_square -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quadratic PCPP Proof Length Bound

**Claim.** For every Boolean circuit with $n$ input bits and $g$ gates, its quadratic PCPP proof length is at most $3\cdot 2^{(n+g+1)^2}$.

**Proof.** Write $m=1+n+g$ for the number of quadratic variables. This is positive, so $m\le m^2$; also $m\le 2^{m^2}$. Thus each of the three contributions $m$, $2^m$, and $2^{m^2}$ to the proof length is at most $2^{m^2}$. Their sum is at most $3\cdot 2^{m^2}$. Since $m=n+g+1$, this is the asserted bound.
