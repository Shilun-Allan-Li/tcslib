<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Loops.lean :: Complexity.BinArith.length_mulU -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of unary multiplication output

**Claim.** For any finite bit strings $a,b$, the unary multiplication procedure applied to their pair encoding produces a string of length $|a||b|$.

**Proof.** The loop-on-a-pair identity (`Complexity.BinArith.forLoop_pairEncode`) reduces the loop on the encoded inputs to an iteration of the multiplication step, with the first input's length as the iteration count. The iterated-step formula (`Complexity.BinArith.iterate_mulUStep`) shows that each iteration appends one copy of the fixed string $b$ to the accumulator. Thus the final accumulator is a concatenation of $|a|$ copies of $b$, whose length is the sum of $|a|$ copies of $|b|$, namely $|a||b|$. The final total second projections recover that accumulator, giving the claimed output length.

**Key facts.** `Complexity.BinArith.forLoop_pairEncode`, `Complexity.BinArith.iterate_mulUStep`.
