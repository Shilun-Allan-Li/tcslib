<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Transcript.lean :: CommunicationComplexity.Deterministic.Protocol.card_transcript_le_two_pow_complexity_aux -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sum Bound from Powers of Two

**Claim.** If $a\le 2^{c_a}$ and $b\le 2^{c_b}$, then $a+b\le 2^{1+\max(c_a,c_b)}$.

**Proof.** Both exponents $c_a$ and $c_b$ are at most their maximum, so monotonicity of natural-number powers gives $2^{c_a},2^{c_b}\le 2^{\max(c_a,c_b)}$. Combining these with the assumed bounds yields $a+b\le 2^{\max(c_a,c_b)}+2^{\max(c_a,c_b)}$. The sum on the right is twice that power, which equals $2^{1+\max(c_a,c_b)}$.
