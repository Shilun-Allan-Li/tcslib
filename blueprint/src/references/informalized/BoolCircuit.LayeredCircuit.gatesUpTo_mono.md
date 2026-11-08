<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LayeredDAG.lean :: BoolCircuit.LayeredCircuit.gatesUpTo_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Gate Lists

**Claim.** Whenever $m\le M$, the gate list through layer $M$ is the list through layer $m$ followed by some list of additional gates.

**Proof.** Induct on the endpoint $M$. At $M=0$, the assumption $m\le0$ forces $m=0$, and the empty list is the required extension. For the successor endpoint $M+1$, if $M<m$, then $m=M+1$ and the two lists are identical, so the extension is empty. Otherwise $m\le M$. By induction the list through $M$ is the list through $m$ followed by some extension. The list through $M+1$ appends the gates of layer $M$ to the list through $M$; associativity of list concatenation combines these two appended parts into the required extension.
