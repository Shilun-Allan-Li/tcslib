<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauCircuit.lean :: BoolCircuit.gatesAcyclic_tabInstrGates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acyclicity of an instruction gadget

**Claim.** The gate list constructed for an instruction is acyclic relative to its tabulated base offset.

**Proof.** Write $B$ for the instruction’s base offset. First consider the $m$ copy gates built from the padded sources. Each reads the single vertex assigned to its source; every such vertex is below $B$ by the source bound (tabSrc_lt). Thus these gates are acyclic relative to $B$. Next, the fixed gate list is acyclic relative to $m$: its embedded gadget gates are acyclic by the embedding theorem (gatesAcyclic_embedAll), since the source list has length $m$ and its entries are below $m$. Appending the intervening constant gates preserves acyclicity because they have no arguments. The final copy gates in this fixed list read vertices indexed by embedding offsets. Each offset is below the total embedded width (embedOffset_lt), and that width is at most the tabulated maximum (kindWidth_le_tabG); hence these copies also satisfy the required earlier-vertex bound. The append principle for acyclic lists (GatesAcyclic.append) combines these portions, accounting for the length of each preceding portion when shifting the next portion’s bound. Finally append the shifted fixed list to the initial source-copy gates. Shifting adds $B$ to each argument, while the fixed list’s acyclicity bound is measured from $m$; the source-copy list has length $m$ (length_padSrc), so the two bounds align. This proves acyclicity of the complete instruction gadget.

**Key facts.** `BoolCircuit.tabSrc_lt`, `BoolCircuit.gatesAcyclic_embedAll`, `BoolCircuit.embedOffset_lt`, `BoolCircuit.kindWidth_le_tabG`, `BoolCircuit.length_embedAll`, `BoolCircuit.length_padSrc`, `BoolCircuit.GatesAcyclic.append`.
