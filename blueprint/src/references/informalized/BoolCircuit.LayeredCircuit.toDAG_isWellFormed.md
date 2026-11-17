<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LayeredDAG.lean :: BoolCircuit.LayeredCircuit.toDAG_isWellFormed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Well-Formedness of the Converted Circuit

**Claim.** The DAG obtained from a finite layered circuit using only standard gate operations has pairwise distinct arguments at each gate, and every NOT gate has exactly one argument.

**Proof.** The converted DAG’s gate list is the list of gates constructed up to the layered circuit’s depth. Apply the gate-list well-formedness result (\texttt{BoolCircuit.LayeredCircuit.gatesUpTo_wellFormed}) at that depth to each gate in the list. It gives precisely that the gate’s arguments have no repetitions and that, if its kind is NOT, its argument list has length one. These are the two conditions in the definition of DAG well-formedness.

**Key facts.** `BoolCircuit.LayeredCircuit.gatesUpTo_wellFormed`.
