<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.codePrimSkipFin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Primitive Recursiveness of the Bounded-Index Skipper

**Claim.** The partial reader that parses an initial unary numeral and returns the remaining suffix exactly when the numeral is less than $n$ is jointly primitive recursive in $n$ and the input string.

**Proof.** First parse the unary numeral and suffix using the primitive recursive unary reader (Turing.codePrimUnary). Bind its result to a conditional test of whether the parsed numeral is less than the bound $n$. If the test holds, return the suffix wrapped as a successful option; otherwise return failure. The comparison, option construction, and conditional are primitive recursive, and option bind combines these steps into the required reader.

**Key facts.** `Turing.codePrimUnary`.
