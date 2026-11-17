<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Logic.lean :: Light.Limits.addr_of_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Address Bound from a Word Limit

**Claim.** If the space bound is at most the word bound and $x$ is below the space bound, then the integer address represented by $x$ is valid and has absolute value at most the word bound.

**Proof.** The cast of a natural number to the integers is nonnegative. Casting $x<S$ shows that its integer value is strictly below the space bound, so it is a valid address. The address absolute-bound result (`Limits.Addr.abs_le`) then gives $|x|\le w$ from the assumed comparison of space and word bounds.

**Key facts.** `Light.Limits.Addr.abs_le`.
