<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/SequentialCircuit.lean :: BoolCircuit.SeqCircuit.unroll_values -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Values in the Unrolled Circuit

**Claim.** For every time $k\le T$ and every vertex $a$ in the sequential circuit's combinational block, the unrolled circuit's value at the position assigned to $a$ at time $k$ equals the value of $a$ when the combinational circuit is evaluated on the inputs and the state at time $k$.

**Proof.** Proceed by induction on $k$, using the register values at time $k$ as the intermediate invariant. The block evaluation fact (`BoolCircuit.SeqCircuit.unroll_block`) says that if the unrolled circuit has the correct values at the register positions for time $k$, then it has the claimed values at every vertex of the combinational block at that time. It remains to establish that register invariant. At time zero, the register gate is the empty-argument gate whose kind is chosen from the initial register value. The empty conjunction evaluates to true and the empty disjunction to false, so this gate returns exactly the initial value. For the successor step, the register gate has one argument, placed at the preceding time and at the vertex specified by the next-state function. Its conjunction therefore returns that argument's value. The induction hypothesis identifies this value with the corresponding combinational-circuit value at the preceding time, which is the definition of the next state. Thus the register invariant holds at each time, and the block evaluation fact gives the desired equality.

**Key facts.** `BoolCircuit.SeqCircuit.unroll_block`, `BoolCircuit.SeqCircuit.unroll_reg`.
