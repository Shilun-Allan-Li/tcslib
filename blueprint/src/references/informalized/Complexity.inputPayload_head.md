<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.inputPayload_head -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Payload at the Virtual Input Head

**Claim.** At the integer coordinate one less than the input-head position, the virtual input payload is the pair of the symbol read by the head and its boundary tag.

**Proof.** Unfold the payload and tag definitions. The buffer tape at the coordinate one less than the head position returns exactly the symbol read by the input head (`bufferTape_inputSymbol`). The coordinate equals $-1$ precisely when the head position is $0$, and equals $|x|$ precisely when the head position is $|x|+1$. Therefore the payload’s tag is $1$ at the left boundary, $2$ at the right boundary, and $0$ otherwise, as required.

**Key facts.** `Turing.FinTM.bufferTape_inputSymbol`.
