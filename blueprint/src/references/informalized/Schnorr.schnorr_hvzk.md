<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Cryptography/SchnorrProtocol.lean :: Schnorr.schnorr_hvzk -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Honest-Verifier Zero Knowledge

**Claim.** For fixed witness and challenge, the honest transcript as a function of the prover's randomness equals the simulator transcript supplied with the reindexed randomness.

**Proof.** Fix a randomness value $r$ and write $s=r+cw$, the reindexed randomness. The response and challenge coordinates of the two transcripts agree by definition. For the commitment coordinate, equality reduces to showing that the simulator's commitment multiplied by $(g^{w.\mathrm{val}})^{c.\mathrm{val}}$ equals the honest commitment $g^{r.\mathrm{val}}$. The Schnorr completeness equation (`schnorr_completeness`), applied to this $w,r,c$, gives exactly that identity. Multiplying by the inverse of the public-key power therefore identifies the simulator's commitment with $g^{r.\mathrm{val}}$. The transcripts agree for every $r$, so the two functions are equal.

**Key facts.** `Schnorr.schnorr_completeness`.
