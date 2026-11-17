<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticCircuitReduction.lean :: FABL.BooleanCircuit.circuitQuadraticWitness_input -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input witness coordinate

**Claim.** At the coordinate assigned to input position $i$, the circuit witness associated with $w$ equals the field element corresponding to $w(i)$.

**Proof.** The input coordinate selects the nonconstant summand at the outer indexing split and the input summand at the inner split. By the witness definition, its value is therefore the Boolean-to-field correspondence applied to $w(i)$.
