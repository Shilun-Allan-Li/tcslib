<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Basic.lean :: Complexity.BinArith.transduce_pairs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transduction of Paired Bits

**Claim.** Processing the consecutively listed bits of a finite list of bit pairs from state $(\bot,s)$ produces the same output as serially processing those pairs from state $s$.

**Proof.** Induct on the list of pairs, generalizing the starting state $s$. With no pairs, both procedures output the empty word. For a first pair $(x,y)$ followed by a list of pairs, the transducer first reads $x$: it stores $x$ and emits nothing. On reading $y$, it emits the output prescribed by the current state and $(x,y)$, then updates that state using the transition rule. The remaining input is exactly the consecutively listed bits of the tail pairs, so the induction hypothesis identifies its output with the serial output from the updated state. Prefixing the first pair's output gives the required equality.
