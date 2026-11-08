<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopDebit_iterate_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length Preservation Under Repeated Updates

**Claim.** For every finite Boolean word $u$ and natural number $i$, applying the word-update part of the debit operation $i$ times preserves the length of $u$.

**Proof.** Induct on $i$. At $i=0$, no update is applied, so the word is unchanged. For the successor case, first apply $i$ updates; by the induction hypothesis the resulting word has the original length. One further update preserves length by the single-step length-preservation fact (\texttt{f2\_loopDebit\_length}). Therefore every iterate has length $|u|$.

**Key facts.** `Turing.FinTM.f2_loopDebit_length`.
