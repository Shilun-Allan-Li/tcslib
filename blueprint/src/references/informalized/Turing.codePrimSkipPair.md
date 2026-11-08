<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.codePrimSkipPair -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Primitive Recursiveness of the Two-Bit Skipper

**Claim.** For any predicate on pairs of Boolean values, the reader that consumes the first two bits if they satisfy the predicate and returns the remaining suffix, and otherwise fails, is primitive recursive.

**Proof.** Represent the input as a list case split: failure occurs if it has fewer than two entries. For a list with first two bits $a,b$ and remaining suffix $zs$, test whether the predicate holds on $(a,b)$; return the suffix as a successful option exactly when it does. The predicate on the two Boolean entries is primitive recursive because its domain is finite, and the test, option construction, and conditional are primitive recursive. Applying the list case operation twice combines these cases into the stated reader.
