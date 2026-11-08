<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticCircuitReduction.lean :: FABL.BooleanCircuit.circuitQuadraticFourQueryPCPPSystem_descriptionSize_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Verifier Description Size Bound

**Claim.** The description size of the circuit's four-query PCPP system is at most $6\cdot 2^{3(m+1)^2}$, where $m$ is the circuit's associated quadratic variable count.

**Proof.** The verifier's description size is the cardinality of its seed space. The combined tester has seeds consisting of a choice of one of two components together with a seed for that component, so its seed count is the sum of the two component seed counts. The homogeneous quadratic PCPP description bound gives at most $5\cdot 2^{3(m+1)^2}$ seeds for the inner tester (`homogeneousQuadraticPCPPSystem_descriptionSize_le`). The input-consistency tester has at most $2^{3(m+1)^2}$ seeds (`circuitQuadraticInputConsistencyFunctionTester_seed_card_le`). Adding these bounds gives the claimed factor of $6$.

**Key facts.** `FABL.homogeneousQuadraticPCPPSystem_descriptionSize_le`, `FABL.BooleanCircuit.circuitQuadraticInputConsistencyFunctionTester_seed_card_le`.
