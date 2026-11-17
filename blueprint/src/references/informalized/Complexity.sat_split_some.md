<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.sat_split_some -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equation for a Returned Split

**Claim.** If the split solver with parameters $C=1$ and $e=1$ at total length $N$ returns $i$, then $i+(i+1)=N$.

**Proof.** A value returned by the solver's finite search satisfies its search predicate (`List.find?_some`), so $i+1\cdot(i+1)^1=N$. Simplifying the unit factor and first power gives $i+(i+1)=N$.
