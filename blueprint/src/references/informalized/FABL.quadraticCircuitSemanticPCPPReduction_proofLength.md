<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticCircuitReduction.lean :: FABL.quadraticCircuitSemanticPCPPReduction_proofLength -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quadratic Reduction Proof Length

**Claim.** For $n\ge1$, the three-query semantic PCPP reduction associated with a Boolean circuit $C$ has proof length equal to the circuit's quadratic PCPP proof length plus $64$ times the number of seeds in its four-query PCPP system.

**Proof.** The proof is the cited identity for the circuit's three-query PCPP description: its proof length is the quadratic PCPP proof length plus $64$ times the description size of the four-query system (`FABL.BooleanCircuit.circuitQuadraticThreeQueryPCPPDescription_proofLength`). The semantic reduction is defined using this three-query description, so its proof-length field is exactly the description's proof length. Substituting the identity gives the claimed formula.

**Key facts.** `FABL.BooleanCircuit.circuitQuadraticThreeQueryPCPPDescription_proofLength`.
