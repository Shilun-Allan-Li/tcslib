<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyProgram.lean :: BoolCircuit.progCircuit_size_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Program circuit size bound

**Claim.** The size of the program circuit is at most $n+2$ plus the program length times the largest gadget width among instruction kinds.

**Proof.** First use the exact circuit-size formula (BoolCircuit.progCircuit_size), then expand the base offset at the full program length. It remains to bound the sum of the widths attached to the instructions. Induct on the program list. The empty list has sum and length zero. For a list beginning with instruction $ins$, the induction hypothesis bounds the tail's sum by its length times the maximum width. Since the width of $ins$'s kind is at most the supremum over all kinds (by the finite-set supremum property), adding this first width gives at most one further copy of that maximum. This proves the sum bound, and substitution gives the result.

**Key facts.** `BoolCircuit.progCircuit_size`.
