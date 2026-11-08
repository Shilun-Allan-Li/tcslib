<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticCircuitReduction.lean :: FABL.BooleanCircuit.circuitQuadraticThreeQueryPCPPDescription_rejectionRate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Three-query rejection rate

**Claim.** For the circuit’s three-query PCPP description, the rejection rate is $1/12800000$.

**Proof.** Rewrite the circuit’s three-query description using the general rejection-rate formula: passing from a description with $q$ queries divides its rejection rate by $q2^q$ ($\texttt{threeQueryPCPPDescription\_rejectionRate}$). The circuit construction uses the four-query description, whose rejection rate is specified by the quadratic PCPP rejection-rate definition. Substituting that rate and $q=4$, then simplifying the rational numbers, gives $1/12800000$.

**Key facts.** `FABL.threeQueryPCPPDescription_rejectionRate`.
