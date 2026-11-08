<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimeBlockTests.lean :: Complexity.zipWith_xor_self -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Self-XOR of a Bit String

**Claim.** For every finite bit string $l$, its bitwise XOR with itself is the all-zero bit string of length $|l|$.

**Proof.** Induct on the list. For the empty list, both sides are empty. For a list with first bit $b$ and remaining list $l$, applying XOR entrywise gives the first bit $b\mathbin{\mathrm{xor}}b$, which is false, followed by the entrywise XOR of $l$ with itself. The induction hypothesis makes the latter the zero string of length $|l|$, so the result is the zero string of length $|l|+1$.
