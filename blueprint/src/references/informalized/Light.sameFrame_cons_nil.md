<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Frames.lean :: Light.sameFrame_cons_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality of a Cons Frame with the Empty Frame

**Claim.** The zero-padded frame of $a::l$ equals the zero-padded frame of the empty list exactly when $a=0$ and the frame of $l$ equals the frame of the empty list.

**Proof.** If the frames agree, their values at index zero agree; the empty-list frame has value zero there, so $a=0$. At each successor index, equality of the cons frames is precisely equality of the corresponding tail-frame values, proving equality of the tail frame with the empty frame. Conversely, if the head is zero and the tail frame equals the empty frame, the cons frame agrees with the empty frame at index zero and at every successor index. Thus the frames agree everywhere.
