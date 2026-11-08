<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Adder.lean :: BoolCircuit.bitsVal_eq_logProg_bitsVal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement of Boolean-list values

**Claim.** For every finite Boolean list, interpreting its entries as base-two digits gives the same value as the recursive definition that assigns the first bit weight $1$ and doubles the value of the remaining list.

**Proof.** Proceed by induction on the list. The empty list has value $0$ under both definitions. For a nonempty list $b::l$, the base-two digit recurrence expresses its value as $b$'s digit plus twice the value of the tail. By the induction hypothesis, the tail's base-two value is its recursively defined value. Substituting that equality gives exactly the recursive definition for $b::l$.
