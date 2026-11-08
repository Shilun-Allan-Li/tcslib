<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauCircuit.lean :: BoolCircuit.tabCircuit_isFaninTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fan-In Bound for the Tabulated Circuit

**Claim.** Every gate of the tabulated circuit has distinct arguments, every NOT gate has exactly one argument, and every gate has at most two arguments.

**Proof.** First establish these three properties for each component gate. Constant gates have no arguments, and copy gates have one; neither can violate the NOT condition. Shifting a gate adds the same offset to each argument, preserving distinctness and argument count, and leaves its kind unchanged.

For a fixed instruction kind, the embedded gadget gates satisfy the properties by the fan-in preservation result for embedding circuits (BoolCircuit.faninTwo_embedAll), since each gadget is itself fan-in two (BoolCircuit.gadget_isFaninTwo). The additional padding constants and output-copy gates satisfy them by the component checks above. Therefore every gate in the fixed part of an instruction satisfies the properties; shifted fixed-part gates do as well. The source-copy gates also satisfy them.

Induct on the instruction list to show that all gates in the tabulated program satisfy the properties: for a cons list, split membership between the current instruction's gates and the recursively tabulated tail, and apply the preceding component facts and induction hypothesis. Finally, split any gate in the whole circuit between the preliminary gates and the tabulated program gates. Every preliminary gate is a constant gate by the characterization of preliminary-gate membership (BoolCircuit.mem_tabPre). Thus all gates have the three properties, which are precisely the asserted well-formedness and fan-in bounds.

**Key facts.** `BoolCircuit.faninTwo_embedAll`, `BoolCircuit.gadget_isFaninTwo`, `BoolCircuit.mem_tabPre`.
