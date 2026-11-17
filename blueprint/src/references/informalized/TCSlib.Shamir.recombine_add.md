<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Cryptography/SecretSharing/Sharing.lean :: TCSlib.Shamir.recombine_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Additivity of Recombination

**Claim.** For a finite set $A$ of parties, recombination of the pointwise sum $f+g$ equals the sum of the recombinations of $f$ and $g$.

**Proof.** Recombination is the finite sum over $i\in A$ of the coefficient for $i$ multiplied by the share value at $i$. For each $i$, distributivity gives the coefficient times $(f(i)+g(i))$ as the sum of the corresponding terms for $f(i)$ and $g(i)$. Distributing the finite sum over addition then yields the sum of the two recombinations.
