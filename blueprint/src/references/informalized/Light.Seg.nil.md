<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Seg.lean :: Light.Seg.nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The Empty List Is a Segment

**Claim.** For every function $\mu$ and starting index $a$, the empty list is a segment of the values of $\mu$ starting at $a$.

**Proof.** The segment condition asks for an equality at every index less than the list's length. The empty list has length zero, so there is no such index; the condition therefore holds vacuously.
