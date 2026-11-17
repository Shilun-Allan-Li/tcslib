<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Adder.lean :: BoolCircuit.runWith_xorGates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the XOR gate sequence

**Claim.** Starting from a list of Boolean values of length $L$, running the four gates appends, in order, the OR and AND of the values at $x,y$, the negation of their AND, and their XOR.

**Proof.** Unfold the four-gate sequence and apply the rule for running a list one gate at a time: each new gate is evaluated on the values accumulated so far. Since $x,y<L$, appending values does not change the entries read at indices $x$ and $y$. Thus the first gate appends their OR, and the second appends their AND. In the third gate, the sole argument is $L+1$, which is out of range at that point, so its value is false and the NOT gate appends true; this is the negation of the previously appended AND. The fourth gate reads index $L$, containing the OR, and index $L+2$, containing that negation. Their conjunction is the XOR of the original values at $x,y$, as is checked by the four possible Boolean input pairs. Hence the final list has exactly the stated appended values.

**Key facts.** `BoolCircuit.runWith_cons`, `BoolCircuit.runWith_nil`.
