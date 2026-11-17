<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticCircuitReduction.lean :: FABL.BooleanCircuit.circuitQuadraticFourQueryPCPPSystem_complete -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completeness of the Combined Verifier

**Claim.** If the circuit accepts the input $w$, then the combined four-query verifier accepts $w$ with probability $1$ when given its encoded circuit quadratic proof.

**Proof.** The combined verifier's acceptance probability is the average of the inner-function tester's and input-consistency tester's acceptance probabilities (`circuitQuadraticFourQueryPCPPSystem_acceptanceProbability`). On the encoded proof, the first probability is $1$ by inner-tester completeness, using that the circuit accepts $w$ (`circuitQuadraticInnerFunctionTester_complete`). The second is $1$ by input-consistency tester completeness (`circuitQuadraticInputConsistencyFunctionTester_complete`). Their average is therefore $1$.

**Key facts.** `FABL.BooleanCircuit.circuitQuadraticFourQueryPCPPSystem_acceptanceProbability`, `FABL.BooleanCircuit.circuitQuadraticInnerFunctionTester_complete`, `FABL.BooleanCircuit.circuitQuadraticInputConsistencyFunctionTester_complete`.
