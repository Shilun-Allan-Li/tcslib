<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Lib.lean :: Complexity.LogProg.update_bufferTape_end -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Appending a Bit to a Tape

**Claim.** Overwriting the tape storing $w$ at cell $|w|$ with $b$ yields exactly the tape storing $w$ followed by $b$.

**Proof.** The tape representation of an appended word is the update of the original tape at the old word's endpoint, assigning the appended symbol there. Applying the tape-append identity (`Turing.FinTM.bufferTape_append`) in reverse gives the claimed equality.

**Key facts.** `Turing.FinTM.bufferTape_append`.
