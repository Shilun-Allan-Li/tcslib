<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Constructible.lean :: Complexity.b3a_embed_space -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Space bound for an embedded machine

**Claim.** Embedding a machine with $m$ work tapes into a system with $k$ tapes, starting with all unused tapes blank and their heads at the origin, uses at most $k(\operatorname{space}_R(d,t)+1)$ total space through time $t$.

**Proof.** Bound the contribution of each of the $k$ tapes. If its index is in the image of the injection, the embedded-machine visited-head lemma identifies its visited positions with those of the corresponding original tape. The space used on that original tape is at most the original machine's total space, so this contribution is at most $\operatorname{space}_R(d,t)$ and therefore at most $\operatorname{space}_R(d,t)+1$. If its index is outside the image, the frame lemma says its head stays at the origin, so it visits exactly one position and contributes $1$. Thus each of the $k$ summands is at most $\operatorname{space}_R(d,t)+1$. Summing gives the claimed bound.

**Key facts.** `Turing.embedEmitTM_visitedByTapeHead`, `Turing.MultiTapeTM.spaceUsedByTape_le_spaceUsed`, `Turing.embedEmitTM_visitedByTapeHead_frame`.
