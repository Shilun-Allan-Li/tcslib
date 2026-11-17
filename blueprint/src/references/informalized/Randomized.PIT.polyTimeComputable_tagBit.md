<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPRun.lean :: Randomized.PIT.polyTimeComputable_tagBit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Tag Bit

**Claim.** For every natural number $i$, the function sending a bit string $w$ to the one-bit word consisting of its bit at position $i$, with missing bits read as false, is polynomial-time computable.

**Proof.** Dropping the first $i$ bits is polynomial-time computable. Applying the polynomial-time head-with-default-false function to the resulting suffix returns exactly the bit at position $i$, or false if the suffix is empty. Closure under composition proves the claim.

**Key facts.** `Complexity.BinArith.polyTimeComputable_drop`, `Complexity.polyTimeComputable_headD`, `Complexity.PolyTimeComputable.comp`.
