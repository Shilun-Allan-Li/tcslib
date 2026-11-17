<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.a3_split_complete -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completeness of the split search

**Claim.** If $n+C\cdot 2^{(n+1)^c}=m$, then the exponential-split search with parameters $C,c,m$ returns $n$.

**Proof.** Consider whether the search returns no value or returns some $k$. If it returns no value, the failure characterization (`a3_split_none_iff`) says there is no natural number satisfying the split equation for $m$, contradicting the given witness $n$. Thus it returns some $k$. The specification of a successful search (`a3_split_spec`) gives $k+C\cdot 2^{(k+1)^c}=m$. The padding function $r\mapsto r+C\cdot 2^{(r+1)^c}$ is strictly increasing (`a3_split_strictMono`), so its values at $k$ and $n$ being equal forces $k=n$. Hence the search returns $n$.

**Key facts.** `Complexity.a3_split_none_iff`, `Complexity.a3_split_spec`, `Complexity.a3_split_strictMono`.
