<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.tmsat_split_some -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equation from a successful split

**Claim.** If the bounded search `solveSplit 1 1 N` returns $i$, then $i+(i+1)=N$.

**Proof.** A successful search returns an index satisfying its search predicate. Here that predicate is $i+1\cdot(i+1)^1=N$. Since the first power is just $i+1$, this is exactly $i+(i+1)=N$.
