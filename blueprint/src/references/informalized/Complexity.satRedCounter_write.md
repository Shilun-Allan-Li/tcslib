<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satRedCounter_write -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Writing on the Unary Counter

**Claim.** If $j\le n$, writing true at offset $j$ on the unary counter tape of length $n$ yields the unary counter tape of length $\max(n,j+1)$.

**Proof.** If $j<n$, the counter already contains true at offset $j$, by the counter-reading fact (`Complexity.satRedCounter_read`). Updating a function at a point with its existing value leaves it unchanged, and $\max(n,j+1)=n$ in this case. If $j$ is not less than $n$, the assumption $j\le n$ forces $j=n$. Appending one true to the replicated word extends the buffer tape by a true at offset $n$ (`Turing.FinTM.bufferTape_append`), which is precisely the update in question; the resulting length is $n+1=\max(n,n+1)$.

**Key facts.** `Complexity.satRedCounter_read`, `Turing.FinTM.bufferTape_append`.
