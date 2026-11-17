<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformScan.lean :: BoolCircuit.AdjScan.le_of_drop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length Bound for a Nonempty List Prefix

**Claim.** If dropping the first $p$ entries of $E$ gives $s$ followed by $rest$, and $s$ is nonempty, then $p+|s|\le |E|$.

**Proof.** Because $s$ is nonempty, its length is positive. Taking lengths in the dropped-list equality gives $|E|-p=|s|+|rest|$ when $p\le |E|$, hence $|s|\le |E|-p$ and the desired inequality. To account for the other possibility, if $p>|E|$, dropping $p$ entries gives the empty list, contradicting the equality with the nonempty prefix $s$. Thus $p\le |E|$, and the length calculation proves the bound.
