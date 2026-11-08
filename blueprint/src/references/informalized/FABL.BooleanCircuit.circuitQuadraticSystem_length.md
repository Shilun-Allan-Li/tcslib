<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticCircuitReduction.lean :: FABL.BooleanCircuit.circuitQuadraticSystem_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quadratic system length

**Claim.** For a Boolean circuit with $g$ gates, its associated homogeneous quadratic system has exactly $g+2$ equations.

**Proof.** Unfold the construction of the quadratic system. It consists of one equation for each of the circuit’s $g$ gates, together with two additional equations. Counting these entries gives length $g+2$.
