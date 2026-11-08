<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/ArrayAt.lean :: Light.IndexAt.read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading an Indexed Segment

**Claim.** For each $i<N$, the value of $\mu(a+i)$ equals the natural-number list entry at index $i$, with zero as the default, viewed as an integer.

**Proof.** The list length is $N$, so $i<N$ is a valid index. Apply the indexed-segment reading fact (`Light.SegN.read`) at this index: it identifies $\mu(a+i)$ with the integer cast of the default-zero lookup. This is the asserted equality.

**Key facts.** `Light.SegN.read`.
