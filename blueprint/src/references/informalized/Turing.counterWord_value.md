<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean :: Turing.counterWord_value -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value After Counter Decrements

**Claim.** For every Boolean word $w$ and natural number $r\le V(w)$, the word obtained after $r$ counter steps has value $V(w)-r$.

**Proof.** Induct on $r$. At $r=0$, zero iterations leave the word unchanged, so the claim follows. For the successor step, apply the induction hypothesis to the intermediate word after $r$ decrements; the bound needed there follows from $r<r+1\le V(w)$. The counter decrement specification says that if the current word has a defined decrement, its value is exactly one less than the current value. If the decrement is undefined, the word has value zero. In that case the hypotheses and the induction hypothesis force the arithmetic equality as well. Thus after one further step the value is $V(w)-(r+1)$.

**Key facts.** `Turing.counter_dec_spec`, `Turing.counter_dec_zero`, `Turing.counter_word_succ`.
