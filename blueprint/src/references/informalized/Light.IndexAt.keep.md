<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/ArrayAt.lean :: Light.IndexAt.keep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preserving an Indexed Segment

**Claim.** If a list satisfies the stated indexed-segment conditions for $\mu$, and $\mu$ and $\mu'$ agree throughout the segment, then the same list satisfies those conditions for $\mu'$ as well.

**Proof.** Keep the list length, entry bounds, and endpoint inequality from the original indexed-segment hypothesis. To verify the segment condition for $\mu'$, fix an index within the list. The length and endpoint hypotheses ensure that its corresponding address lies in the specified interval and below the top bound. Thus $\mu'$ agrees there with $\mu$. The original segment condition identifies the value of $\mu$ at that address with the list entry, so the same entry is obtained for $\mu'$. The transfer of the segment condition is the segment congruence fact (`Light.Seg.congr`).

**Key facts.** `Light.Seg.congr`.
