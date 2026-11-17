<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StraightLineDualRail.lean :: BoolCircuit.DAGCircuit.toStraightLine_length_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length bound for the straight-line program

**Claim.** The constructed straight-line program has length at most $2|C.\mathrm{gates}|+1$.

**Proof.** The dual-rail invariant bounds the number of statements generated while processing the gates by twice the number of gates. The construction appends one final statement to read out the circuit output. Thus the total length is at most $2|C.\mathrm{gates}|+1$.

**Key facts.** `BoolCircuit.StraightLine.dualRail_inv`.
