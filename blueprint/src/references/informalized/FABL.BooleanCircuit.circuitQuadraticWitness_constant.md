<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticCircuitReduction.lean :: FABL.BooleanCircuit.circuitQuadraticWitness_constant -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Constant witness coordinate

**Claim.** For every Boolean input $w$, the quadratic witness of $C$ at $w$ has value $1$ in the field with two elements at its constant coordinate.

**Proof.** The constant coordinate is the one selected by the first summand in the indexing decomposition. In the witness definition, every index in that summand is assigned the field element $1$. Evaluating at the constant coordinate therefore gives $1$.
