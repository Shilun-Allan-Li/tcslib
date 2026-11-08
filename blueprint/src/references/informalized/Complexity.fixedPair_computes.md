<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Reductions.lean :: Complexity.fixedPair_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Running Time of Fixed-String Pairing

**Claim.** For a fixed finite binary string $\alpha$, a finite binary-alphabet Turing machine outputs the string formed by doubling each bit of its input, then appending $01$ and $\alpha$, and halts within $2|\alpha|+|x|+3$ steps on every input $x$.

**Proof.** Apply the prefix-writing machine to the fixed prefix consisting of the string obtained by doubling each bit of $\alpha$, followed by $01$. The prefix machine appends its input $x$ after that prefix and halts in time equal to the prefix length plus $|x|+1$ (`Complexity.prefixTM_computes`). The doubled string has length $2|\alpha|$, so the fixed prefix has length $2|\alpha|+2$. Substitution gives the stated output and running-time bound.

**Key facts.** `Complexity.prefixTM_computes`.
