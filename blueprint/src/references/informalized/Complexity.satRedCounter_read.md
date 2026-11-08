<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satRedCounter_read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading the Unary Counter

**Claim.** At every natural offset $j$, the unary counter tape of length $n$ contains true when $j<n$, and is blank when $j\ge n$.

**Proof.** At a natural offset, the buffer tape agrees with the corresponding optional entry of its underlying list (`Turing.FinTM.bufferTape_nat`). The underlying list consists of $n$ copies of true, so its entry at $j$ is true exactly when $j<n$; beyond its length there is no entry. This gives the stated alternatives.

**Key facts.** `Turing.FinTM.bufferTape_nat`.
