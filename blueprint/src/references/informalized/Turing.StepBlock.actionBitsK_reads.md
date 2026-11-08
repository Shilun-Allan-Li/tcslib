<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.actionBitsK_reads -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Action Record and Table Reads

**Claim.** If the table tape contains the full action encoding of $a$ from its current head position, then the encoding splits into a record of length $4k+4$ and the successor-state encoding, and the corresponding consecutive tape cells contain those two parts.

**Proof.** By the fixed-prefix decomposition of the action encoding (`Turing.StepBlock.actionBitsK_split`), choose bits whose list is the length-$4k+4$ record, followed by the successor-state encoding. The decomposition immediately gives the total length. Apply the consecutive-read principle (`Turing.StepBlock.reads_append`) to the assumed tape contents and this concatenation. It shows that the cells covering the first list contain its bits, and that the cells starting immediately after it contain the successor-state bits. Since the first list is indexed by a finite type of size $4k+4$, these are exactly the two read claims.

**Key facts.** `Turing.StepBlock.actionBitsK_split`, `Turing.StepBlock.reads_append`.
