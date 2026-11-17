<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.bufferTape_reads -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading a Word Stored Between Two Lists

**Claim.** In a buffer tape storing the concatenation of a prefix, a word, and a suffix, the cell at position $|b|+r$ contains the $r$-th bit of the middle word whenever $r<|w|$.

**Proof.** First, every valid natural position in a buffer tape reads the corresponding list entry (`Turing.FinTM.bufferTape_nat`). Apply the consecutive-read principle (`Turing.StepBlock.reads_append`) to the whole concatenated list, first splitting off the prefix and then splitting the remaining word-plus-suffix. The second split says that positions starting at the prefix length contain the entries of the middle word at their corresponding offsets. Taking offset $r<|w|$ gives the stated cell content.

**Key facts.** `Turing.FinTM.bufferTape_nat`, `Turing.StepBlock.reads_append`.
