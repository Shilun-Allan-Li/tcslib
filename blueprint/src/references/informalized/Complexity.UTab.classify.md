<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterMain.lean :: Complexity.UTab.classify -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary string classification

**Claim.** Every finite Boolean string is either entirely ones, or consists of a string of ones followed by a zero and an arbitrary finite Boolean string.

**Proof.** Proceed by induction on the string. The empty string is a repetition of zero ones. For a nonempty string, inspect its first bit. If it is zero, the string has the required second form with zero initial ones and the rest as its arbitrary suffix. If it is one, apply the induction hypothesis to the tail. When the tail is all ones, adjoining the first one gives a string of one more repeated one; when the tail has a first zero after a run of ones, adjoining the initial one lengthens that run by one and preserves the remaining suffix.
