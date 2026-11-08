<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticCircuitReduction.lean :: FABL.BooleanCircuit.circuitQuadraticFourQueryPCPPSystem_isPCPP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The Circuit Verifier Is a PCPP

**Claim.** The combined four-query verifier is a PCPP for the property of inputs accepted by the circuit, with rejection rate $\rho_C$.

**Proof.** The general PCPP criterion (`FABL.isPCPP_of_exists_close_of_acceptanceProbability_ge`) reduces the result to three conditions. First, the rate is positive, as follows from its definition. Second, for every accepted input, the encoded circuit quadratic proof makes the verifier accept with probability $1$ (`circuitQuadraticFourQueryPCPPSystem_complete`). Third, whenever a proof makes the verifier accept with probability at least $1-\rho_C\varepsilon$, the input is $\varepsilon$-close to an accepted input (`circuitQuadraticFourQueryPCPPSystem_close_of_acceptanceProbability_ge`). These are precisely the required positivity, completeness, and soundness conditions.

**Key facts.** `FABL.isPCPP_of_exists_close_of_acceptanceProbability_ge`, `FABL.BooleanCircuit.circuitQuadraticFourQueryPCPPSystem_complete`, `FABL.BooleanCircuit.circuitQuadraticFourQueryPCPPSystem_close_of_acceptanceProbability_ge`.
