<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Encoding.lean :: BoolCircuit.encodeChildren_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoding a Nonempty Child List

**Claim.** The encoding of a child list beginning with $d$ is a leading bit $1$, followed by the encoding of $d$ and then the encoding of the remaining child list.

**Proof.** By definition, encoding the child list concatenates, for each child, a leading $1$ followed by that child's circuit encoding, and then appends a final $0$. Splitting off the first child gives $[1]$ followed by the encoding of $d$, then the corresponding concatenation for the remaining children and the same final $0$. Associativity of list concatenation groups this as the leading $1$ followed by the encoding of $d$ concatenated with the encoding of the remaining child list.
