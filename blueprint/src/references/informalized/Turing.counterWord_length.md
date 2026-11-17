<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean :: Turing.counterWord_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length preservation under counter steps

**Claim.** For every Boolean word $w$ and every natural number $r$, the counter word after $r$ decrement steps has length $|w|$.

**Proof.** Induct on $r$. At zero steps the counter word is $w$, so the lengths agree. For the successor step, the counter word is obtained by applying one fixed-width decrement to the word after $r$ steps (`counter_word_succ`). The decrement specification (`counter_dec_spec`) says that when decrement returns a new word, its length equals the input length; if it returns no word, the counter word is left unchanged by the default-value convention. In either case the successor word has the same length as the round-$r$ word, which has length $|w|$ by the induction hypothesis.

**Key facts.** `Turing.counter_word_succ`, `Turing.counter_dec_spec`.
