<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopDebit_iterate_value -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value After Repeated Decrements

**Claim.** If $i\le R$, applying the fixed-width decrement $i$ times to the binary digit word of $R$ produces a word of value $R-i$.

**Proof.** Induct on $i$. For $i=0$, the binary digit word of $R$ has value $R$ (`loopValue_bits`), as required. For the successor step, the induction hypothesis gives value $R-i$ after $i$ decrements. Since $i+1\le R$, this value is positive. The decrement success criterion (`loopDebit_success`) therefore says that the next decrement succeeds. In the success case, one is added to the value of the decremented word to recover the previous value (`loopDebit_value`); hence the new value is $(R-i)-1=R-(i+1)$.

**Key facts.** `Turing.FinTM.loopValue_bits`, `Turing.FinTM.loopDebit_success`, `Turing.FinTM.loopDebit_value`.
