<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.taut_split_exists -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Existence of a split solution

**Claim.** Whenever $i+(i+1)=N$, the bounded split search with parameters $C=e=1$ returns $i$ on input $N$.

**Proof.** Consider the result of the bounded search. If it returns no index, the defining property of a failed list search says that no index in the searched range satisfies the search equation. But $i$ lies in that range because $i\le N$, and the hypothesis $i+(i+1)=N$ is exactly the equation tested when $C=e=1$. This is a contradiction. Therefore the search returns some index $j$. The split-search property gives $j+(j+1)=N$. Comparing this with the assumed equation for $i$ yields $j=i$, so the search returns $i$.

**Key facts.** `Complexity.taut_split_some`.
