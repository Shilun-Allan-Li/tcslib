<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticCircuitReduction.lean :: FABL.BooleanCircuit.circuitQuadraticThreeQueryPCPPDescription_proofLength -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Three-query proof length

**Claim.** For a Boolean circuit $C$ with $n>0$ input bits, the proof length of its three-query PCPP description is the quadratic PCPP proof length for $C$ plus $64$ times the description size of its associated four-query PCPP system.

**Proof.** Unfold the circuit’s three-query PCPP description. The general proof-length formula for a three-query description says that its length is the original proof length plus the query count times $2$ to the query count times the system’s description size ($\texttt{threeQueryPCPPDescription\_proofLength}$). Here the underlying system is the four-query system, so the added term is $4\cdot 2^4=64$ times its description size. The original proof length is the quadratic PCPP proof length by the definition of the circuit’s description, yielding the claimed formula.

**Key facts.** `FABL.threeQueryPCPPDescription_proofLength`.
