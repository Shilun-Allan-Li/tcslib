<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satPairCfg_work -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symbol under the capture tape head

**Claim.** In the canonical pairing configuration, the symbol under the last work-tape head is the buffer-tape symbol for $u$ at offset $j$.

**Proof.** The last tape is the added capture tape: in the canonical configuration its contents are defined by the buffer tape for $u$, and its head position is $j$. The symbol under a tape head is its tape contents evaluated at that head position. Unfolding these definitions gives the buffer-tape symbol for $u$ at $j$.
