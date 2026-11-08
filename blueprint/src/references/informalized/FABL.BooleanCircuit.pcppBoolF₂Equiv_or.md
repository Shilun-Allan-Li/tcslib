<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticCircuitReduction.lean :: FABL.BooleanCircuit.pcppBoolF₂Equiv_or -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Field encoding of disjunction

**Claim.** For Boolean values $a$ and $b$, the field encoding of their disjunction equals the sum of their encodings plus their product in $[?]$.

**Proof.** There are four possibilities for $(a,b)$. If both are false, both sides are zero. If exactly one is true, both sides are one. If both are true, the left side is one and the right side is $1+1+1=1$ in the field of two elements. Thus the identity holds in every case.
