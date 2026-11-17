<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean :: Turing.counter_potential -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counter Potential Identity

**Claim.** If $r$ does not exceed the binary value of $w$, then the counter overhead after $r$ iterations plus twice the number of true entries of $w$ equals four times $r$ plus twice the number of true entries in the counter word after $r$ iterations.

**Proof.** Induct on $r$. At $r=0$, the overhead is an empty sum and the counter word is $w$, so the identity follows immediately. For the successor step, the induction hypothesis applies at $r$ because the given bound implies the corresponding bound there. The decrement specification gives the change in the number of true entries at this step: if the current word is decremented to the next one, its true count decreases by one plus the length of its initial false run (Turing.counter_dec_spec). The next iteration adds exactly twice that run length plus two to the overhead, by the definition of the overhead. Combining these changes with the induction hypothesis increases the right-hand contribution by four, matching the replacement of $r$ by $r+1$. The decrement is defined at this step because $r$ is strictly below the original binary value (Turing.counter_word_decrement), so the specification’s returned-word case applies.

**Key facts.** `Turing.counter_dec_spec`, `Turing.counter_word_decrement`.
