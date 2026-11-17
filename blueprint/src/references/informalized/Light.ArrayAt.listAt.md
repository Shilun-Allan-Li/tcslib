<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/ArrayAt.lean :: Light.ArrayAt.listAt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Array Specification Implies List Specification

**Claim.** An array specification implies the corresponding list specification, retaining its length, recorded values, and upper-limit condition.

**Proof.** The array specification already contains the length condition, the segment condition identifying each in-range list entry with the corresponding value of $\mu$, and the upper-limit condition. The list specification asks for exactly these same three properties, so they transfer directly.
