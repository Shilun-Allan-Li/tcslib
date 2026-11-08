<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedCut_StateTape_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Appending a Unary State Symbol

**Claim.** Updating the unary state tape encoding $n$ at cell $n+1$ to contain $1$ gives the unary state tape encoding $n+1$.

**Proof.** The tape encoding $n$ is the buffer of the list consisting of a leading $0$ followed by $n$ ones. Appending one more $1$ to a list’s buffer is equivalent to updating the buffer at the list’s former length to that symbol (`Turing.FinTM.bufferTape_append`). Here that length is $n+1$, and appending a $1$ changes the list to a leading $0$ followed by $n+1$ ones. Its buffer is exactly the encoding of state $n+1$, proving the identity.

**Key facts.** `Turing.FinTM.bufferTape_append`.
