<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/SequentialCircuit.lean :: BoolCircuit.SeqCircuit.getElem_unroll_gates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gate at a Position in the Unrolled Circuit

**Claim.** For any position $p$ below the number of gates in the unrolled circuit, the gate there is the gate prescribed by the unrolling rule at position $p$.

**Proof.** The unrolled circuit's gate list is defined by mapping the unrolling rule over the list of positions from $0$ up to its length. At any valid position $p$, indexing this mapped list returns the image of the entry at $p$; the entry is $p$ itself. Thus the gate at that position is precisely the unrolling rule applied to $p$.
