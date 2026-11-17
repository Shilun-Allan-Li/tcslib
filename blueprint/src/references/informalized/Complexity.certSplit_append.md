<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Levels.lean :: Complexity.certSplit_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Certificate split of a concatenation

**Claim.** If the suffix $u$ has length $C(|x|+1)^c$, then splitting $xu$ at the certificate boundary encodes the two pieces as the self-delimiting pair of $x$ and $u$.

**Proof.** The concatenated word has length $|x|+C(|x|+1)^c$. The search therefore succeeds at index $|x|$, by the self-witness property of the split search (`Complexity.solveSplit_self`). At that index, taking the prefix of the concatenation recovers $x$, and dropping it recovers $u$. Substituting these two pieces into the definition of the certificate split gives exactly the pair encoding of $x$ and $u$.

**Key facts.** `Complexity.solveSplit_self`.
