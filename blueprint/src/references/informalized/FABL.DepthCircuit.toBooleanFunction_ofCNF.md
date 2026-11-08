<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Circuits.lean :: FABL.DepthCircuit.toBooleanFunction_ofCNF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit representation of a CNF function

**Claim.** For every CNF formula on the sign cube, the Boolean function computed by the circuit formed from that formula equals the function represented by the formula.

**Proof.** The circuit formed from a CNF formula computes the same value as the formula at every point of the sign cube, by the pointwise evaluation identity (`FABL.DepthCircuit.eval_ofCNF`). Therefore the two Boolean functions are equal.

**Key facts.** `FABL.DepthCircuit.eval_ofCNF`.
