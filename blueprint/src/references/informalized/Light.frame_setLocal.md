<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Frames.lean :: Light.frame_setLocal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating a local frame entry

**Claim.** Updating the list at index $x$ to value $z$, padding with zeros if needed, makes the frame at $y$ equal to $z$ when $y=x$ and leaves it equal to the original frame value otherwise.

**Proof.** The proof follows the list and index recursion defining the update. When the index is zero, the updated head is $z$, so the frame reads $z$ at zero and retains the tail values at later indices. When the index is positive, the head is preserved and the update is applied recursively to the tail; thus index zero is unchanged, while any later index reduces to the same assertion for the tail and the predecessor index. This also covers an initially empty list: the recursive update inserts the required zero padding, and the same index-by-index reasoning applies.
