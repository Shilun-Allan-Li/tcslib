<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatReductionValid.lean :: BoolCircuit.DAGCircuit.eval_dual -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation Under Dualization

**Claim.** If every NOT gate of $C$ has exactly one argument, then on every input assignment $x$, the dual circuit evaluated at the bitwise complement of $x$ outputs the complement of $C$ evaluated at $x$.

**Proof.** Fix $x$. First compare the full lists of vertex values. The initial input list for the dual circuit on the complemented assignment is the entrywise complement of the original input list. At each gate, dualization preserves the rule that the new gate's value is the complement of the original gate's value; the condition that every NOT gate has one argument is needed for this gatewise duality. Inducting through the gates in topological order therefore shows that the dual circuit's entire value list is the entrywise complement of the original value list (`BoolCircuit.runWith_dual`). The output vertex is unchanged by dualization, and it is a valid vertex of the original value list. Selecting that same position in the complementary lists gives complementary output bits, as required.

**Key facts.** `BoolCircuit.runWith_dual`.
