<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean :: Turing.universalStateTape_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Extending the Unary State Tape

**Claim.** Writing $1$ in cell $n+1$ of the unary state tape encoding $n$ produces the unary state tape encoding $n+1$.

**Proof.** The tape contents for state $n+1$ are obtained by appending one symbol, $1$, to the list encoding state $n$. The buffer-append identity (\texttt{Turing.FinTM.bufferTape\_append}) says that appending a symbol to a finite tape buffer is equivalent to updating the cell at the old buffer's length with that symbol. Here that length is $n+1$, so the update is exactly the stated one.

**Key facts.** `Turing.FinTM.bufferTape_append`.
