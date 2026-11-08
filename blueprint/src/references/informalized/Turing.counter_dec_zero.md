<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean :: Turing.counter_dec_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero Value and Undefined Decrement

**Claim.** For every Boolean word $w$, decrement is undefined exactly when the binary value of $w$ is zero.

**Proof.** Apply the binary decrement specification and split according to whether decrement is undefined or returns a word. In the undefined case, the word is a list of false entries, whose binary value is zero. In the defined case, the specification says the value of $w$ is the value of the returned word plus one, so it cannot be zero. These two cases establish both directions.

**Key facts.** `Turing.counter_dec_spec`.
