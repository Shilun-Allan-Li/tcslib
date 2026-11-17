<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean :: BoolCircuit.runWith_getD_last -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of the Last Gate

**Claim.** After evaluating a finite gate list $G$ and then a gate $g$ from $v$, the value at index $|v|+|G|$ is the output of $g$ on the list produced by evaluating $G$.

**Proof.** Evaluating a concatenation means first evaluating its initial segment and then its remaining segment (`runWith_append`). Applying this to $G$ followed by $[g]$, and using the formula for evaluating a single gate (`runWith_singleton`), expresses the result as the list from evaluating $G$ followed by the value $f(g,w)$, where $w$ is that intermediate list. The length formula (`length_runWith`) gives $|w|=|v|+|G|$. Thus the specified index is exactly the position of the appended value, so reading it returns $f(g,w)$; the default value is not needed.

**Key facts.** `BoolCircuit.runWith_append`, `BoolCircuit.runWith_singleton`, `BoolCircuit.length_runWith`.
