<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean :: Turing.counter_word_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successive Counter Words

**Claim.** The counter word after $r+1$ iterations is the result of decrementing the counter word after $r$ iterations, with an undefined decrement interpreted as leaving that word unchanged.

**Proof.** The counter word is defined by iterating the operation that applies fixed-width decrement when defined and otherwise returns its input. The iteration law for a successor number of iterations says to first perform $r$ iterations and then apply this operation once. This is exactly the stated identity.
