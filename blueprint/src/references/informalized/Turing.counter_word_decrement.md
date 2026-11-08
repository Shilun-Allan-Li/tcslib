<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean :: Turing.counter_word_decrement -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decrementing a Counter Word

**Claim.** If $r$ is less than the value represented by $w$, then the fixed-width decrement of the counter word after $r$ iterations is defined and equals the counter word after $r+1$ iterations.

**Proof.** The value formula for the iterated counter word says its represented value is the original value minus $r$. Since $r$ is strictly smaller than the original value, this value is positive. A fixed-width decrement is undefined exactly at value zero, so the decrement here cannot be undefined. By the successor identity for counter words, the word after $r+1$ iterations is the defined decrement of the word after $r$ iterations. Thus the decrement is that word, as claimed.

**Key facts.** `Turing.counterWord_value`, `Turing.counter_word_succ`, `Turing.counter_dec_zero`.
