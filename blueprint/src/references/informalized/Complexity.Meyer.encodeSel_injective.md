<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachine.lean :: Complexity.Meyer.encodeSel_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of Selector Encoding

**Claim.** The encoding that assigns to each selector its indicator function at its index under the fixed enumeration is injective.

**Proof.** Suppose two selectors have the same encoded Boolean function. Evaluate both functions at the index assigned to the first selector. Its encoding is true there, so the second selector’s encoding must also be true there. Since each encoding is true precisely at its own enumerated index, the two selectors have the same index. The enumeration is a bijection, hence injective, so the selectors are equal.
