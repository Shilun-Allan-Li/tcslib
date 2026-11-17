<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/HardFunctions.lean :: BoolCircuit.length_encodeCircuit_succ_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit Encoding Length Bound

**Claim.** For every Boolean circuit $C$ on $n$ variables, the length of its encoding plus one is at most $(n+4)$ times its size.

**Proof.** Use structural induction on the circuit. For a literal of index $k<n$, the literal-length formula gives encoding length $k+3$; since $k\le n-1$, this length plus one is at most $n+3$, which is bounded by $(n+4)$ times the size of a literal, namely $n+4$.

For a node with children $cs$, first prove a bound for the encoding of its children: its length is at most $(n+4)$ times the sum of the child sizes, plus one. Induct on the child list. The empty list encodes as a single terminator bit, giving the bound. In the cons case, the encoding adds a separator bit and the encoding of the first child; the child’s induction hypothesis bounds its encoding length plus one, while the list induction hypothesis bounds the rest. The two contributions combine to the stated bound for the whole child list.

Now the node encoding consists of two initial bits followed by this child encoding. Its size is one plus the sum of the child sizes. Substituting the child-list bound and simplifying yields that the node encoding length plus one is at most $(n+4)$ times the node size.

**Key facts.** `BoolCircuit.TreeCircuit.ind`, `BoolCircuit.encodeChildren_cons`, `BoolCircuit.encodeChildren_nil`, `BoolCircuit.encodeCircuit_node`, `BoolCircuit.length_encodeCircuit_lit`.
