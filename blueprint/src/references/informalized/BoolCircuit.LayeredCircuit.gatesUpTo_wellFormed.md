<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LayeredDAG.lean :: BoolCircuit.LayeredCircuit.gatesUpTo_wellFormed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Well-Formed Gates in Every Prefix

**Claim.** For every natural number $M$, each gate in the list through layer $M$ has pairwise distinct argument vertices, and any gate of kind NOT has exactly one argument.

**Proof.** Proceed by induction on $M$. At $M=0$ the gate list is empty, so the claim is vacuous. For the step from $M$ to $M+1$, membership in the appended list splits into membership in the earlier prefix or in the new layer's list. In the first case, the induction hypothesis gives well-formedness. In the second case, the gate comes from some node in the successor of layer $M$; the fact that every layer gate is well formed (`layerGate_wellFormed`) gives the result. If the depth condition fails, the new list is empty, so this second case cannot occur.

**Key facts.** `BoolCircuit.LayeredCircuit.layerGate_wellFormed`.
