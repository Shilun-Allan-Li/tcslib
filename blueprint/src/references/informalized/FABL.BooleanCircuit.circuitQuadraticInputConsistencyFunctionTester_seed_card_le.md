<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticCircuitReduction.lean :: FABL.BooleanCircuit.circuitQuadraticInputConsistencyFunctionTester_seed_card_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Consistency Seed Bound

**Claim.** For positive input length, the input consistency tester’s seed space has size at most $2^{3(m+1)^2}$, where $m=1+n+g$ is the circuit’s quadratic variable count and $g$ is its number of gates.

**Proof.** The seed space is the product of the $n$ input coordinates and the $m$-dimensional cube over $\mathbb F_2$. Its cardinality is therefore $n2^m$. Since $n\le m$ and $m\le 2^m$, this is at most $2^m2^m=2^{2m}$. The exponent $2m$ is at most $3(m+1)^2$, so the claimed bound follows by monotonicity of powers of $2$.
