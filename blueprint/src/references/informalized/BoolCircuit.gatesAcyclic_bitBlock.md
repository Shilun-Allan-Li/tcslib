<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Adder.lean :: BoolCircuit.gatesAcyclic_bitBlock -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acyclicity of a bit block

**Claim.** If $a,b,c,cin,acc<L$, then the specified bit-block gate list is acyclic from index bound $L$.

**Proof.** Expanding the definitions gives the gate list in its prescribed order: two XOR gate groups for the full adder, its final OR gate, a further XOR group, and the final NOT and AND gates. In each group, the inputs $a,b,c,cin,acc$ are below $L$, while any other inputs are indices introduced by earlier gates in this list. Checking these finitely many inputs against the bound $L+i$ at each position $i$ proves acyclicity; the required inequalities follow from the five hypotheses and elementary arithmetic on the displayed offsets.
