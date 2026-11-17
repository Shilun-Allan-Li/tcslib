<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticCircuitReduction.lean :: FABL.BooleanCircuit.circuitQuadraticInnerFunctionTester_complete -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completeness of the Inner Tester

**Claim.** If the Boolean circuit accepts the input, then the inner-function tester accepts the input together with the canonically encoded circuit proof with probability one.

**Proof.** The circuit witness assigns the constant variable the value $1$, the input variables the bits of $w$, and each gate variable its evaluated value. Since the circuit accepts, this witness satisfies the circuit’s homogeneous quadratic system (`circuitQuadraticWitness_satisfies`). Encode this witness as the extension portion of the joined proof, and use the canonical homogeneous-quadratic PCPP encoding for its inner-proof portion. The extension and inner-proof extraction identities (`circuitQuadraticExtensionProof_join` and `circuitQuadraticInnerProof_join`) show that the inner tester sees precisely these two assignments. Its acceptance probability is therefore the acceptance probability of the homogeneous-quadratic system tester on the satisfying witness and its canonical encoding; completeness of that tester gives probability one (`homogeneousQuadraticPCPPSystem_complete`).

**Key facts.** `FABL.BooleanCircuit.circuitQuadraticInnerFunctionTester_acceptanceProbability`, `FABL.BooleanCircuit.circuitQuadraticExtensionProof_join`, `FABL.BooleanCircuit.circuitQuadraticInnerProof_join`, `FABL.BooleanCircuit.circuitQuadraticWitness_satisfies`, `FABL.homogeneousQuadraticPCPPSystem_complete`.
