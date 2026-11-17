<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.taut_split_some -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successful Split Equation

**Claim.** If the bounded search with parameters $C=e=1$ returns $i$ on input $N$, then $i+(i+1)=N$.

**Proof.** A successful list search supplies its defining predicate at the returned index: $i+1\cdot(i+1)^1=N$. Since the exponent is one and multiplication by one leaves the factor unchanged, this simplifies to $i+(i+1)=N$.
