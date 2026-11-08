<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedPrefix_write -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clock Bit Writing Step

**Claim.** In the fourth clock phase for bit $b$, with the input head at position $p+1$, clock string $c$, and empty output, one parser step advances the head to $p+2$, appends $b$ to the clock, returns to the first clock phase, and leaves the output empty.

**Proof.** Compare the resulting configuration field by field. The transition in the fourth clock phase moves the input head one position to the right; the head is not at the right boundary, since $p$ is strictly less than the input length, so its new position is $p+2$ (`Turing.moveInputPos_pos_of_ne_right`). The work tape is updated at its current frontier, which is the length of the clock, to store $b$. This is exactly the tape representing the extended clock $c\mathbin{+}[b]$ (`Turing.FinTM.bufferTape_append`). The frontier itself increases by one, agreeing with the length of the extended clock, while the output remains empty and the state is the first clock phase. These component equalities give the claimed configuration.

**Key facts.** `Turing.moveInputPos_pos_of_ne_right`, `Turing.FinTM.bufferTape_append`.
