<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterSteps.lean :: Complexity.UTab.goes_layer -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution of one tableau layer

**Claim.** Starting from the specified layer label and register values, the counter program reaches the copy-loop label for the initial layer and the layer label otherwise, with the stated updated registers and appended instruction bits, within the bound $B$.

**Proof.** The layer label tests the step counter, which is positive because $T\ge 1$ and its initial value is $tD$ with the corresponding layer setup; the positive branch therefore takes one step to the layer’s first cell (`goes_jz_pos`). The execution then traverses the work-tape cells (`goes_tapes`), the input positions (`goes_inputs`), and the snapshot (`goes_snap`), in that order. These three facts give the output bits for their respective consecutive index intervals, and update the instruction index and preceding-instruction counter as the traversal advances. The work-tape and input traversals also establish the required register values at the start of the snapshot traversal. The stride identity $D=k(2T+1)+(|z|+n+2)+1$ shows that these intervals partition the full range from $tD$ to $(t+1)D-1$; splitting that range into the three pieces identifies the combined output with the prescribed concatenation. Composing the four executions concatenates their outputs and adds their step bounds. The register updates simplify to the stated next layer-start record, with the initial-layer branch retaining the special zero value of $q$. Finally, the resulting sum of bounds is at most $B$, by $t\le T$ and elementary arithmetic.

**Key facts.** `Complexity.CounterProg.goes_jz_pos`, `Complexity.UTab.goes_tapes`, `Complexity.UTab.goes_inputs`, `Complexity.UTab.goes_snap`, `Complexity.CounterProg.Goes.trans`, `Complexity.UTab.range'_add`, `Complexity.CounterProg.Goes.congr`.
