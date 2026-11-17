<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalStartup.lean :: Turing.universalCapture_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Captured Transition Preservation

**Claim.** For a nonhalted configuration of $M$, one step of the capture wrapper from its associated first-phase configuration is the first-phase configuration associated to the result of one step of $M$.

**Proof.** Write the state of the original configuration as $q$ and let $a$ be the transition action selected by $M$ at $q$, using the same input symbol and the symbols read from the first $k$ work tapes. The wrapper is in its active first-phase state, so its transition applies exactly this action to those tapes and the input head. It leaves the three right-hand tapes blank, while its middle tape records the emitted symbol, if any, at the current output length. The middle head advances by one precisely when a symbol is emitted. Thus that tape and its head agree with the buffer representation of the output after applying $a$: appending a symbol to the output updates the buffer at its old length, by the buffer-append identity (`Turing.FinTM.bufferTape_append`); with no emitted symbol, the buffer and head stay unchanged. The wrapper's external output remains empty, and its new state records the successor state of $a$ in the first phase. These componentwise agreements give the claimed equality.

**Key facts.** `Turing.FinTM.bufferTape_append`.
