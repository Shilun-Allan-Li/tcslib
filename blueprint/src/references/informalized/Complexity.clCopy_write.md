<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clCopy_write -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Appending One Record Bit

**Claim.** Applying the specified action leaves the input head and source word unchanged, moves the source head to $z+d$, appends $b$ to the record, emits no output, and enters state $q'$.

**Proof.** The action leaves the input head fixed because its input movement is zero (`moveInputPos_zero`). On the source tape it requests no write, so the tape contents are preserved, while its head movement adds $d$ to the source-head position. On the record tape it writes $b$ at the current record head and moves that head one cell right. The finite-word tape update rule (`bufferTape_append`) identifies this updated tape with the tape for the concatenated word $record ++ [b]$. The action emits no output and sets the state to $q'$, so the resulting configuration has exactly the stated data.

**Key facts.** `Turing.moveInputPos_zero`, `Turing.FinTM.bufferTape_append`.
