<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.comp_pair_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Aligned Pair Parsing Run

**Claim.** Given the register alignment and bit-reading hypotheses, the program parses the word using the aligned pair parser: if parsing fails it reaches “answer false” after consuming some prefix, and if parsing succeeds it reaches the appropriate copy state just past the encoded first component.

**Proof.** Apply the aligned-pair parsing loop to the program's scan, first-component test, second-component test, and bit-reading states. Its stride is $1$ for an outer scan and $2$ for an inner scan, which is positive; the register used as the scan limit is distinct from the pointer register. The given alignment equation supplies the loop's limit, while the bit-oracle identity identifies each queried bit of the encoded input with the corresponding bit of the word (`Complexity.comp_bit`).

At each iteration the loop consumes one parser unit, advancing the pointer by the stride. When the pair parser fails, it stops at a prefix length $t\le |w|$ and reaches “answer false,” with exactly that pointer increment and all other registers unchanged. When parsing succeeds with first component $u$, the parser identifies the encoded pair boundary after $2|u|+2$ bits; the loop reaches the designated copy stage with the corresponding pointer increment. Safety and register bounds are inherited from the loop's bound hypothesis (`Complexity.LogProg.alignedPair_loop`).

**Key facts.** `Complexity.LogProg.alignedPair_loop`, `Complexity.comp_bit`.
