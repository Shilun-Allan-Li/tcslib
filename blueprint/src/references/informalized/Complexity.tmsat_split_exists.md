<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.tmsat_split_exists -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness of the split search

**Claim.** If natural numbers $N$ and $i$ satisfy $i+(i+1)=N$, then the bounded search `solveSplit 1 1 N` returns `some i`.

**Proof.** Split on whether the search returns nothing or some $j$. If it returns nothing, the characterization of a failed list search (`List.find?_eq_none`) says that no entry in the search range satisfies the predicate. But $i\le N$, so $i$ is in that range, and the assumed equation makes it satisfy the predicate, a contradiction. If the search returns `some j`, successful-search correctness (`Complexity.tmsat_split_some`) gives $j+(j+1)=N$. Comparing this with $i+(i+1)=N$ shows $j=i$, since the function $r\mapsto r+(r+1)$ is strictly increasing on the natural numbers. Thus the search returns `some i`.

**Key facts.** `Complexity.tmsat_split_some`.
