<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/ArrayAt.lean :: Light.ArrayAt.drop_take -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Specification of a Subarray

**Claim.** If an array specification holds for $l$ and $k+n\le N$, then the list formed by dropping the first $k$ entries of $l$ and taking the next $n$ entries is an array specification beginning at $a+k$, of length $n$, with the same bound and upper limit.

**Proof.** First forget the entrywise bound in the array specification to obtain the corresponding list specification (`Light.ArrayAt.listAt`). The list specification's drop-and-take result states that, under $k+n\le N$, dropping $k$ entries and taking $n$ produces a list of length $n$ that records the values of $\mu$ starting at $a+k$ and satisfies the required upper-limit condition (`Light.ListAt.drop_take`). It remains to check the entrywise bound: any entry of the taken list comes from the dropped list, and hence from the original list. The original bound therefore applies to it. Together these properties give the asserted array specification.

**Key facts.** `Light.ArrayAt.listAt`, `Light.ListAt.drop_take`.
