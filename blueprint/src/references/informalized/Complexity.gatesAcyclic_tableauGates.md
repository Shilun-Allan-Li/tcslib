<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyTableau.lean :: Complexity.gatesAcyclic_tableauGates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acyclicity of tableau gates

**Claim.** In the gate list for the tableau of $M$ on an input of length $n$ through time $t$, every argument of gate $i$ has index strictly less than $n+i$.

**Proof.** Proceed by induction on the time bound. At time zero, the gate list consists of the two constant gates, each with no arguments, so the required condition holds. For the successor step, write the new list as the previous tableau gates followed by the gates embedding all the transition gadgets. The length formula for tableau gates (`Complexity.length_tableauGates`) identifies the number of available vertices after the previous block with the new block's base. The sources for the gadgets have the required arity (`Complexity.length_tableauSources`) and all lie below that base (`Complexity.tableauSources_lt`). Thus the embedded block is acyclic relative to that base, by the acyclicity result for embedding all gadgets (`BoolCircuit.gatesAcyclic_embedAll`). Combining this with the induction hypothesis via the concatenation principle for acyclic gate lists (`BoolCircuit.GatesAcyclic.append`) proves acyclicity of the full list.

**Key facts.** `Complexity.length_tableauGates`, `Complexity.length_tableauSources`, `Complexity.tableauSources_lt`, `BoolCircuit.gatesAcyclic_embedAll`, `BoolCircuit.GatesAcyclic.append`.
