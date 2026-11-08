<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/ArrayAt.lean :: Light.ListAt.read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading a Recorded List Entry

**Claim.** If a list records the values of μ at consecutive indices starting at a and has length N, then for every i < N, μ(a+i) equals the default-zero lookup of the list at i.

**Proof.** Since the list has length N, the inequality i < N gives i < l.length. The segment-recording property therefore identifies μ(a+i) with the list entry at i. The default-zero lookup agrees with that entry at every index within the list, yielding the stated equality (the segment lookup fact `Light.Seg.getD`).

**Key facts.** `Light.Seg.getD`.
