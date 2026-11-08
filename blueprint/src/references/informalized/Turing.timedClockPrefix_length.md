<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedClockPrefix_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clock Prefix Length

**Claim.** The word obtained by repeating each bit of a Boolean word four times and appending $0011$ has length $4|b|+4$.

**Proof.** Induct on the word. The empty word contributes only the four-bit suffix, giving length $4$. For a word formed by adding one bit to a tail, the flat-map portion gains a block of four copies, while the suffix remains of length four. Using the induction hypothesis, the resulting length is $4+4|\text{tail}|+4=4(|\text{tail}|+1)+4$, as required.
