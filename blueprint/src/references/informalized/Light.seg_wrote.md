<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Pass.lean :: Light.seg_wrote -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A written interval matches its list

**Claim.** If $l$ has length $n$ and its entry at each valid index $i$ is $f(i)$, then the values of the sequence written from $dst$ for length $n$ agree with $l$ starting at $dst$.

**Proof.** Fix a valid index $i$ of $l$. Since $|l|=n$, it follows that $i<n$. The write therefore places $f(i)$ at address $dst+i$ (`Light.wrote_done`). By hypothesis, the entry of $l$ at index $i$ is also $f(i)$. Hence the written sequence and the list agree at every valid index.

**Key facts.** `Light.wrote_done`.
