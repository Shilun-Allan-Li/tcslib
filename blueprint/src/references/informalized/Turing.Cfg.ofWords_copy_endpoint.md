<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.Cfg.ofWords_copy_endpoint -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Copying a Word to an Empty Tape

**Claim.** When the destination word is empty, the specified copy operation produces the configuration determined by the updated family of words, with the destination word replaced by the source word and the state changed to the new state.

**Proof.** Compare the two configurations componentwise. Their states are both the new state, their input head positions and work tape head positions are the same, and their output tapes are both empty. It remains to compare the contents of each work tape at every integer position. If the tape index is not the destination, the update leaves its word unchanged and the specified copying condition is false, so the tape contents agree. At the destination, the updated word is the source word. The original destination tape is empty, so its contents are nowhere defined: the fact that buffering an empty word yields no symbol (`Turing.FinTM.bufferTape_nil`) gives blank contents outside the copied interval. On the copied interval, the condition selects the source word's buffered symbol at the position measured from the tape head, which is position zero. Outside that interval, both descriptions are blank: for nonnegative positions beyond the source word's length, buffering the source word gives no symbol, and for negative positions buffering also gives no symbol. Thus the work tape contents agree everywhere, and all configuration components are equal.

**Key facts.** `Turing.FinTM.bufferTape_nil`.
