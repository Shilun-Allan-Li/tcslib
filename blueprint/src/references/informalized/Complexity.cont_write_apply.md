<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.cont_write_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Appending Bits by a Write Action

**Claim.** Applying the specified write action to a loader configuration appends each present bit to its buffer, advances that buffer head exactly when it writes, changes to state $q'$, and moves the input head according to the clamped move.

**Proof.** The action sets the new state to $q'$, moves the physical input head by $m$, leaves the output unchanged, and treats the input and choice buffers independently. For either buffer, no write leaves its tape unchanged and its head stationary. When a bit is present, the tape update writes that bit at the old head position, which is the old word's length, and advances the head by one; this is exactly the buffer representing the old word with the bit appended. The buffer update identity (`Turing.FinTM.bufferTape_append`) expresses this pointwise: the representation of the extended list is the old representation updated at the old length. The unused work tapes and their head positions are unchanged. Thus all components agree with the stated loader configuration.

**Key facts.** `Turing.FinTM.bufferTape_append`.
