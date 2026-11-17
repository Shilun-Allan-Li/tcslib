<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_pad_init -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Padding the Initial Configuration

**Claim.** Padding the initial configuration with state $q$ on input $x$ gives the seam configuration on the $K$-tape bank with state $\mathrm{emb}(q)$ and empty words on all tapes.

**Proof.** Compare the configuration fields. Both configurations have state $\mathrm{emb}(q)$, the initial input-head position, and empty output. The initial configuration has blank contents and zero head position on every tape; padding retains these values on the first $k$ tapes and assigns the same blank contents and zero position to every added tape. The seam configuration with empty words has precisely these contents and positions on all $K$ tapes, so the configurations agree.
