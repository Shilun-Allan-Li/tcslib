<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauCircuit.lean :: BoolCircuit.gatesAcyclic_tabProgGates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acyclicity of tabulated program gates

**Claim.** For every instruction index and finite instruction list, the concatenated tabulated gate lists are acyclic relative to the base offset at that index.

**Proof.** Induct on the instruction list, allowing the starting index to vary. For the empty list there are no gates, so acyclicity is vacuous (GatesAcyclic.nil). For a list beginning with instruction $\mathrm{ins}$ at index $i$, its gate list is acyclic relative to the base at $i$ (gatesAcyclic_tabInstrGates). The instruction gadget has length equal to the fixed tabulation width (length_tabInstrGates), and the base at $i$ plus that width is exactly the base at $i+1$, by the definition of the base offset. The induction hypothesis therefore gives acyclicity of the remaining program relative to the offset following the first gadget. The append principle (GatesAcyclic.append) combines the first gadget and the remaining gates, proving the claim.

**Key facts.** `BoolCircuit.GatesAcyclic.nil`, `BoolCircuit.gatesAcyclic_tabInstrGates`, `BoolCircuit.length_tabInstrGates`, `BoolCircuit.GatesAcyclic.append`.
