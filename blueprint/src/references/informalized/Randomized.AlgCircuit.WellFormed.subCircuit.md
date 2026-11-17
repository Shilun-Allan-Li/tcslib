<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/AlgCircuit.lean :: Randomized.AlgCircuit.WellFormed.subCircuit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Well-formedness under circuit subtraction

**Claim.** Concatenating two nonempty well-formed circuits, shifting the second circuit’s references by the size of the first, and appending a subtraction gate that refers to the two output nodes produces a well-formed circuit.

**Proof.** The resulting gate list is nonempty because it contains the final subtraction gate. To check references, split according to whether a gate lies in the first circuit, in the shifted copy of the second, or is the final subtraction gate. A gate in the first circuit retains its original position and satisfies the reference condition by well-formedness of the first circuit. A gate from the second circuit originally at position $k$ occurs at position $|C|+k$; its references are increased by $|C|$, so each remains strictly earlier than the new position by well-formedness of the second circuit. Finally, the last subtraction gate refers to indices $|C|-1$ and $|C|+|C'|-1$, the output positions of the two nonempty circuits. Both indices are strictly less than the position of that final gate.
