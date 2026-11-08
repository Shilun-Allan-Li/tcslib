<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clErase_last -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Erasing the Appended Bit

**Claim.** For every Boolean word $w$ and bit $b$, erasing the tape cell indexed by $|w|$ from the tape storing $w$ followed by $b$ gives the tape storing $w$.

**Proof.** By the append formula for the tape encoding, the tape storing $w$ followed by $b$ is obtained by updating the tape for $w$ at position $|w|$ to contain $b$. Updating again at that same position with a blank therefore leaves just the tape for $w$. To verify this pointwise, consider an integer position $z$. If $z=|w|$, the new blank agrees with the tape for $w$, which is blank there since the word has no entry at index $|w|$. If $z\ne |w|$, the erasure does not change the encoded tape's value there, and the append update did not change the tape for $w$ there either. Thus the two tapes agree at every position.

**Key facts.** `Turing.FinTM.bufferTape_append`, `Turing.FinTM.bufferTape_nat`.
