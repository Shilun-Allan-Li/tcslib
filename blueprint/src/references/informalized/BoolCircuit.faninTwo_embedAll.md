<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyGadget.lean :: BoolCircuit.faninTwo_embedAll -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fan-in after embedding circuits

**Claim.** If every circuit in a finite list of circuits with $m$ inputs is well formed and has fan-in at most two, then every gate in the circuit list obtained by embedding them has the same properties.

**Proof.** Induct on the list of circuits, with the embedding offset $L$ arbitrary. For the empty list there are no gates to check. For a list beginning with circuit $D$, its embedded gates form the first part of an append, followed by the embeddings of the remaining circuits at the updated offset. A gate in the first part is well formed and has at most two inputs by the embedding theorem for one circuit (`faninTwo_embedGates`), using the hypothesis that $D$ has fan-in at most two. A gate in the remaining part satisfies the claim by induction, since every remaining circuit still has the assumed property and the induction applies at the updated offset. These two cases cover the entire embedded list.

**Key facts.** `BoolCircuit.faninTwo_embedGates`.
