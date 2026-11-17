<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformScan.lean :: BoolCircuit.AdjScan.hitGate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scan Hit on a Gate

**Claim.** When the scan is in its gate-hit state and the encoded suffix begins with a gate marker and the encoding of $g$, it halts with bounded registers and returns true for a size task, the requested-kind comparison for a type task, or the requested-vertex membership test for an edge task.

**Proof.** The nonempty-prefix length bound (`le_of_drop`), together with $|E|\le B$, bounds the position of the marker and the two kind bits. Every gate kind has an encoding of exactly two bits. Thus the suffix decomposes into the marker, two bits $b_1,b_2$, and the encoded arguments; dropping those first three bits leaves the argument encoding (`drop_add_of_drop`). The first two kind bits are read correctly from the oracle: the dropped-list entry fact (`getD_of_drop`) identifies them with the corresponding bits of $E$.

For a size task, the hit state immediately returns true. For a type task, the scan advances to its kind-reading state, reads $b_1$ and $b_2$, and returns whether the requested kind equals the decoded kind. The encoding-decoding identity (`decodeKind_encode`) identifies that decoded kind with $g.kind$, giving exactly the stated comparison. The intermediate configurations obey the register bound by `gd_rg`.

For an edge task, the scan advances through the fixed preliminary states to the argument-reading state, with registers still bounded by `gd_rg`. The remaining suffix is the encoding of the argument list followed by the remainder, so the argument-examination result (`argsEx`) halts with answer true precisely when $iv$ occurs among $g$'s arguments. This is the required edge answer.

**Key facts.** `BoolCircuit.AdjScan.le_of_drop`, `BoolCircuit.AdjScan.length_gate_encode`, `BoolCircuit.AdjScan.getD_of_drop`, `BoolCircuit.AdjScan.drop_add_of_drop`, `BoolCircuit.AdjScan.gd_rg`, `Complexity.LogProg.AHalt.ret`, `Complexity.LogProg.AHalt.step`, `BoolCircuit.AdjScan.decodeKind_encode`, `BoolCircuit.AdjScan.argsEx`.
