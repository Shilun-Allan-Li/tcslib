<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopDebit_iterate_value -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value After Repeated Debit

**Claim.** If $i\le R$, then applying the word-update part of the debit operation $i$ times to the binary expansion of $R$ gives a word whose value is $R-i$.

**Proof.** Induct on $i$. For $i=0$, the word is the binary expansion of $R$, whose value is $R$ (\texttt{f2\_loopValue\_bits}). For the successor step, the induction hypothesis says that after $i$ updates the value is $R-i$. Since $i<R$ in this case, that value is positive. The debit-success criterion (\texttt{f2\_loopDebit\_success}) therefore says the next debit succeeds. The debit value identity (\texttt{f2\_loopDebit\_value}) then says that the updated word's value is one less than the current value. It is consequently $R-i-1=R-(i+1)$, as required.

**Key facts.** `Turing.FinTM.f2_loopValue_bits`, `Turing.FinTM.f2_loopDebit_success`, `Turing.FinTM.f2_loopDebit_value`.
