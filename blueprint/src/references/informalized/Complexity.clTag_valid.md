<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clTag_valid -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Validity of the Deterministic Boundary Tag

**Claim.** The tag that is false at input-head position zero and true at every positive position is false at the left boundary and true at the right boundary, so it satisfies the boundary-tag conditions.

**Proof.** The tag is defined to be true exactly when the position is nonzero. If the position is zero, this definition makes the tag false. If the position is the right boundary, its value is $n+1$, which is positive, so the tag is true. These are the two required boundary implications; no restriction is imposed on its value at interior positions.
