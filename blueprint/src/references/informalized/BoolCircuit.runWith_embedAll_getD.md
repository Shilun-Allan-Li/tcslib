<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyGadget.lean :: BoolCircuit.runWith_embedAll_getD -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of embedded circuits in sequence

**Claim.** After embedding and executing a list of circuits, the designated position for any circuit in the list contains that circuit’s output on the input read from the specified source indices.

**Proof.** Induct on the list of circuits, allowing the initial value list and the selected position to vary. For a nonempty list with first circuit $D$, split execution into the gates embedded from $D$ followed by those for the tail (`runWith_append`). Executing the first block extends the list by exactly $|D.	ext{gates}|+1$ entries. If the selected position is zero, its designated index is the output position for $D$, so the embedded-circuit evaluation result (`runWith_embedGates_getD`) gives the claim. If the position is a successor, use the extended list as the initial list for the induction hypothesis on the tail. The source indices remain in range because the first block only lengthens the list. The definition of the embedding offset shifts the tail’s designated position by exactly the length of this first block. Finally, the input supplied to a tail circuit agrees coordinatewise with the original source-based input: each source index is in range in the extended list, so executing the first block has not changed its value (`runWith_getD_of_lt`).

**Key facts.** `BoolCircuit.runWith_append`, `BoolCircuit.runWith_embedGates_getD`, `BoolCircuit.runWith_getD_of_lt`.
