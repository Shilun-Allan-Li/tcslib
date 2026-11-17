<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Scan.lean :: Complexity.Codec.foldl_adStep_chunk -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Processing one full buffer chunk

**Claim.** Folding the update operation over a list of length $w+1$, starting at position zero with any buffer, ends at position zero with state $\delta(s,ch)$ and some buffer.

**Proof.** Write the list as $l$ followed by its last entry $a$. Since its length is $w+1$, the prefix $l$ has length $w$. The partial-buffer result says that processing this prefix leaves the state unchanged, advances the position from zero to $w$, and places the entries of $l$ in the corresponding buffer positions. Now process $a$. At position $w$, the update operation completes a full block: it writes $a$ into the last position, applies $\delta$ to the list read from the buffer, and resets the position to zero. The resulting buffer is the old buffer updated at position $w$ with $a$. Its entries agree position by position with $l$ followed by $a$, so the list supplied to $\delta$ is exactly $ch$. Hence the final state is $\delta(s,ch)$, with position zero and the claimed buffer.

**Key facts.** `Complexity.Codec.foldl_adStep_partial`.
