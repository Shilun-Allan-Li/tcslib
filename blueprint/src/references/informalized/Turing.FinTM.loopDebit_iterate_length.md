<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopDebit_iterate_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length Preservation Under Iteration

**Claim.** For every finite Boolean word $u$ and nonnegative integer $i$, applying the fixed-width decrement operation $i$ times to $u$ preserves its length.

**Proof.** Proceed by induction on $i$. When $i=0$, no decrement is performed, so the resulting word is $u$ and the lengths agree. For the successor step, the iterate after $i+1$ applications is obtained by first applying the iterate after $i$ applications and then decrementing once. By the induction hypothesis the intermediate word has length $u.length$, and the decrement operation preserves the length of every word (`loopDebit_length`). Therefore the final word also has length $u.length$.

**Key facts.** `Turing.FinTM.loopDebit_length`.
