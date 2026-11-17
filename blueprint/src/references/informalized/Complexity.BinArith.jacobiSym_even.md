<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Jacobi.lean :: Complexity.BinArith.jacobiSym_even -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Jacobi symbol for an even numerator

**Claim.** For natural numbers $A,N$, if $A$ is even, then $(A/N)=(2/N)(A/2N)$.

**Proof.** The Jacobi symbol is multiplicative in its numerator: $(A/N)=(2(A/2)/N)=(2/N)(A/2/N)$. Evenness ensures that $A=2(A/2)$, so this is the stated identity.
