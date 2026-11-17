<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean :: Turing.counter_word_exhausted -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exhausting a Counter Word

**Claim.** After as many counter iterations as the value represented by a finite Boolean word, the counter word is the all-false word of the same length.

**Proof.** At the iteration count equal to the initial represented value, the counter value formula gives represented value zero. A fixed-width decrement is undefined exactly when the represented value is zero. The decrement specification then identifies the current word itself as the all-false word of its length. The counter-word length theorem ensures that this length is the original length, proving the claim.

**Key facts.** `Turing.counterWord_value`, `Turing.counter_dec_zero`, `Turing.counter_dec_spec`, `Turing.counterWord_length`.
