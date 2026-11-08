<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/SequentialCircuit.lean :: BoolCircuit.SeqCircuit.length_unroll_gates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Number of Gates in the Unrolled Circuit

**Claim.** If the sequential circuit has size $s$, then unrolling it for $T$ steps produces exactly $(T+1)s$ gates.

**Proof.** The gate list of the unrolled circuit is the image of the list of positions with length $(T+1)M.size$. Mapping a function over a list preserves its length, so the unrolled gate list has length $(T+1)M.size=(T+1)s$.
