<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHard.lean :: Complexity.PathHard.length_adjWordE -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Adjacency Word Length

**Claim.** For every machine, input, and natural numbers $s,n$, the adjacency word has length $n^2$.

**Proof.** The adjacency word is obtained by mapping one Boolean edge indicator over the range from $0$ to $n^2-1$. Mapping a function over a finite range preserves the range's length, so the resulting word has length $n^2$.
