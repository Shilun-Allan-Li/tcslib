<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPReduce.lean :: Randomized.PIT.shStep_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Empty Circuit Shift Fixed Point

**Claim.** For every unary prefix $M$ and output string $out$, one shift step leaves unchanged the pairing of $M$ with the encoding of the empty gate list and $out$.

**Proof.** The empty gate list is encoded by the single terminating bit $0$. After decoding the nested pairing, the circuit component is therefore this one-bit terminator. It satisfies the stopping condition: it is nonempty, but dropping its first bit leaves the empty string and its first bit is $0$. Hence the definition of a shift step selects its unchanged-input branch, proving the equality.
