<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.codePrimPrefix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Primitive Recursiveness of the Co-Length Prefix

**Claim.** The operation taking a finite Boolean string $xs$ and a natural number $n$ to the prefix of length $\max(\operatorname{length}(xs)-n,0)$ is primitive recursive.

**Proof.** Reverse the input string, remove its first $n$ entries using the primitive recursive suffix-removal operation (Turing.codePrimDrop), and reverse the result. Reversing a list is primitive recursive, so this composite operation is primitive recursive. For a list $xs$, reversing after removing $n$ entries from its reversal gives precisely the prefix of $xs$ whose length is $\operatorname{length}(xs)-n$ when that difference is nonnegative, and gives the empty list otherwise. This follows from the list identity relating reversal of a dropped suffix to taking the corresponding prefix.

**Key facts.** `Turing.codePrimDrop`.
