<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.bufferTape_unary -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading a Unary Word

**Claim.** In a buffer tape storing $q$ copies of $1$ followed by $0$, cell $r$ contains $1$ when $r<q$ and contains $0$ when $r=q$, for $r\leq q$.

**Proof.** If $r<q$, the position lies within the replicated block of ones, so the buffer-tape lookup is that entry (`Turing.FinTM.bufferTape_nat`) and equals $1$. Otherwise $r\leq q$ forces $r=q$, the position of the final zero; the same lookup fact gives $0$. These two values are exactly the stated cases.

**Key facts.** `Turing.FinTM.bufferTape_nat`.
