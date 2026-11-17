<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Frames.lean :: Light.sameFrame_cons_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality of Cons Frames

**Claim.** The zero-padded frames of $a::l$ and $b::m$ are equal exactly when $a=b$ and the zero-padded frames of $l$ and $m$ are equal.

**Proof.** If the frames agree, evaluate their equality at index zero to obtain $a=b$. Evaluating at each successor index shows that the frames of the tails agree. Conversely, assume the heads are equal and the tail frames agree. At index zero the cons frames then agree by the head equality; at every successor index their values are the corresponding tail-frame values, which agree by hypothesis. Hence the frames are equal at every index.
