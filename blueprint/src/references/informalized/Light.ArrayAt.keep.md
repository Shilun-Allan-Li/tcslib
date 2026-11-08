<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/ArrayAt.lean :: Light.ArrayAt.keep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation Under Agreement on the Interval

**Claim.** If an array specification for $\mu$ holds on the given interval and $\mu'$ agrees with $\mu$ there, then the same list and parameters satisfy the array specification for $\mu'$.

**Proof.** An array specification contains the list length, segment identity, entrywise bound, and upper-limit condition. The bound and the two numerical conditions do not depend on the function, so they remain valid. For the segment identity, first pass from the array specification to its list specification (`Light.ArrayAt.listAt`), then use preservation of that list specification under agreement on the interval (`Light.ListAt.keep`). Its segment identity supplies the required values of $\mu'$ at each position; retaining the original length, bound, and upper-limit condition completes the array specification.

**Key facts.** `Light.ArrayAt.listAt`, `Light.ListAt.keep`.
