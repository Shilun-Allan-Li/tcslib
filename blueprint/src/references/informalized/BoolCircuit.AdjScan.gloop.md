<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformScan.lean :: BoolCircuit.AdjScan.gloop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gate-List Scan and Halt

**Claim.** Under the stated oracle, target, and length hypotheses, a scan starting at the gate-reading state over an encoded list of gates halts within the register bound. It returns the task-specific answer for the gate at offset $tv-c$ when that offset is within the list, and returns false when it is not.

**Proof.** Proceed by induction on the gate list. If the list is empty, its encoding is the single terminator bit. The dropped-suffix length bound (`le_of_drop`) bounds the current position, and the first bit of the suffix is therefore read as true (`getD_of_drop`). The scan takes its rejection branch and halts false; the register bounds follow from `gd_rg`.

For a nonempty list, write it as $g::gs$. The encoding starts with a marker followed by the encoding of $g$ and then the encoding of $gs$. The scan reads the marker and compares the current counter $c$ with the target index $tv$ (`astep_rd` and `astep_hit`). If $c=tv$, this gate is the target, and the gate-hit result (`hitGate`) supplies the correct task-specific answer and bounded halt. If $c\ne tv$, the scan skips the current gate using `gateSkip`, reaching the next gate-reading state with counter $c+1$ and a bounded third register. The suffix after that gate is exactly the encoded remainder (`drop_add_of_drop`), so the induction hypothesis applies to $gs$. The index identity $tv-c=(tv-(c+1))+1$ aligns the selected position in the tail with the original offset. Chaining the skip reachability with the induction-hypothesis halt (`AReach.halt`) proves the result, including the false answer when the target lies beyond the list.

**Key facts.** `BoolCircuit.AdjScan.le_of_drop`, `BoolCircuit.AdjScan.getD_of_drop`, `BoolCircuit.AdjScan.gd_rg`, `Complexity.LogProg.AHalt.ret`, `BoolCircuit.AdjScan.astep_rd`, `BoolCircuit.AdjScan.astep_hit`, `BoolCircuit.AdjScan.hitGate`, `BoolCircuit.AdjScan.gateSkip`, `BoolCircuit.AdjScan.drop_add_of_drop`, `Complexity.LogProg.AHalt.step`, `Complexity.LogProg.AReach.halt`.
