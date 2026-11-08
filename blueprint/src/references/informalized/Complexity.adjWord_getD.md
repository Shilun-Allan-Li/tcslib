<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Path.lean :: Complexity.adjWord_getD -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indexing the Adjacency Word

**Claim.** In the concatenation of the rows of the Boolean-valued function $A$, the entry at position $un+v$ is $A(u,v)$.

**Proof.** View the concatenated list as rows, each of length $n$. The row-indexing fact (`Complexity.getD_flatMap_rows`) identifies the entry at position $un+v$ with the entry at position $v$ of row $u$, provided $u<n$ and $v<n$. Here these bounds hold because $u,v\in\mathrm{Fin}(n)$, and the row is the list of values $A(u,j)$ as $j$ ranges from $0$ to $n-1$. Its entry at position $v$ is therefore $A(u,v)$.

**Key facts.** `Complexity.getD_flatMap_rows`.
