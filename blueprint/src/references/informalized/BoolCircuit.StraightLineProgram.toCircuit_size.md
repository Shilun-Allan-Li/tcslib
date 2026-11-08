<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StraightLine.lean :: BoolCircuit.StraightLineProgram.toCircuit_size -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size of the Translated Circuit

**Claim.** The translated circuit has size $2n+\max(|P|,1)$, where $|P|$ is the number of statements in the straight-line program.

**Proof.** The circuit size is the number of input vertices plus the number of gates. The translation appends the gates for the straight-line statements to the gates for negated inputs, with an additional constant gate when the statement list is empty. The straight-line gate list has length $n+|P|$ (`BoolCircuit.StraightLine.length_slpGates`). Adding the input vertices and accounting for the two cases—empty or nonempty statement list—gives $2n+1$ when $|P|=0$ and $2n+|P|$ otherwise. This is $2n+\max(|P|,1)$.

**Key facts.** `BoolCircuit.StraightLine.length_slpGates`.
