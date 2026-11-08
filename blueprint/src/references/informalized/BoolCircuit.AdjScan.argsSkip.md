<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformScan.lean :: BoolCircuit.AdjScan.argsSkip -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Skipping an Encoded Argument List

**Claim.** For every encoded list suffix and bounded starting register state, the scan can reach the gate-scan state with its pointer advanced by the encoded list length, maintaining the register bound throughout.

**Proof.** Induct on the argument list. If it is empty, its encoding is the one-bit terminator. The suffix equation bounds the pointer by the length of $E$ (`le_of_drop`), and the oracle reads the terminator as false (`getD_of_drop`, `astep_rd`). The machine takes the exit branch and reaches the gate-scan state; the registers remain bounded, and the run is assembled by one-step reach lemmas (`AReach.step`) followed by reflexivity (`AReach.refl`). For a list $k::as$, the encoding consists of its leading true bit, the unary code for $k$, and the encoding of $as$. The length formula for encoded lists bounds the pointer and intermediate registers. The leading read branches into the element scan; the machine advances the pointer and clears the accumulator. The unary scan consumes the code for $k$ while respecting the register bound (`uloop`), then the machine returns to the argument-list scan with the pointer just past that code. The suffix after the code is exactly the encoding of $as$ followed by the original remainder (`drop_succ_of_drop`, `drop_add_of_drop`). Apply the induction hypothesis there, and concatenate the initial transitions, unary scan, and remaining reach using transitivity of reach (`AReach.trans`). The resulting pointer is advanced by the full encoded-list length, and the induction construction preserves the bound on all registers.

**Key facts.** `BoolCircuit.AdjScan.le_of_drop`, `BoolCircuit.AdjScan.length_encodeList_cons`, `BoolCircuit.AdjScan.drop_succ_of_drop`, `BoolCircuit.AdjScan.drop_add_of_drop`, `BoolCircuit.AdjScan.getD_of_drop`, `BoolCircuit.AdjScan.astep_rd`, `BoolCircuit.AdjScan.uloop`, `BoolCircuit.AdjScan.gd_rg`, `Complexity.LogProg.AReach.step`, `Complexity.LogProg.AReach.refl`, `Complexity.LogProg.AReach.trans`.
