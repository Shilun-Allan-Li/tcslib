<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.sat_split_exists -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Existence of a Certificate Split

**Claim.** If $i+(i+1)=N$, then the split solver with parameters $C=1$ and $e=1$ at total length $N$ returns $i$.

**Proof.** Consider the solver's result. If it returns no value, its defining search condition fails for every candidate in the range (`List.find?_eq_none`). The hypothesis ensures that $i$ is in the range, and the equation $i+(i+1)=N$ says precisely that $i$ satisfies the solver's search condition, a contradiction. Therefore the solver returns some $j$. Any returned value satisfies the split equation (`sat_split_some`), so $j+(j+1)=N$. The given $i$ satisfies the same equation, and this equation determines its natural-number solution uniquely; hence $j=i$, as required.

**Key facts.** `Complexity.sat_split_some`.
