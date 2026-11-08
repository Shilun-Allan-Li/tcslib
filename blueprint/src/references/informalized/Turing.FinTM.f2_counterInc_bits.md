<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_counterInc_bits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Increment

**Claim.** For every natural number $n$, applying the recursive Boolean-list increment operation to the binary digits of $n$ gives the binary digits of $n+1$.

**Proof.** Use binary recursion on $n$. At zero, the operation sends the empty bit list to the one-bit list representing $1$. For a binary digit $b$ appended to the representation of $n$, first use the decomposition of the bit list of the represented number into the bits of $n$ followed by $b$. If $b$ is false, incrementing changes that final false bit to true, giving the binary representation of $2n+1$. If $b$ is true, the carry changes it to false and recursively increments the bits of $n$. By the induction hypothesis, those bits become the bits of $n+1$; the resulting list is therefore the representation of $2(n+1)$, as required.
