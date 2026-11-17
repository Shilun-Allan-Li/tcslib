<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.b2_unary_read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Read Under Unary Reinterpretation

**Claim.** The input symbol read from the unary reinterpretation of a configuration is the original read with every present bit replaced by true; a blank remains blank.

**Proof.** The input-head position is unchanged by reinterpretation, and the unary input has the same length as $x$. If the head is at either boundary, both configurations read blank. Otherwise both read the cell at the same interior position; the unary word has true in every cell, so its read is true, exactly the result of replacing any present original bit by true.
