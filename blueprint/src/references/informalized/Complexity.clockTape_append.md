<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.clockTape_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Appending a Captured Bit

**Claim.** The captured clock tape of $w$ followed by $b$ is obtained by updating the captured clock tape of $w$ at coordinate $|w|+1$ with the tagged bit $b$.

**Proof.** Compare the two tape functions at an arbitrary integer coordinate $z$. If $z=|w|+1$, that coordinate is nonzero, and the appended word contributes the new bit there; the clock-tape definition therefore gives the tagged bit, as does the update. Otherwise the update leaves the old tape unchanged at $z$. At the origin both tapes carry the origin marker; at every other coordinate, the buffer tape for the appended word agrees with the old buffer tape except possibly at the appended coordinate. This last fact is precisely the buffer-tape append identity (`bufferTape_append`), applied at the shifted coordinate used by the clock tape. Thus the functions agree everywhere.

**Key facts.** `Turing.FinTM.bufferTape_append`.
