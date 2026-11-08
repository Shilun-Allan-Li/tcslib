<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPath.lean :: Complexity.exists_eq_of_ushape -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding a Bit String of the Specified Shape

**Claim.** A bit string satisfying the stated unary, matrix, and binary-field shape conditions decodes to a Boolean adjacency matrix whose row-major entries agree with the corresponding bits of the string.

**Proof.** The matrix-shape condition yields a list $M$ of length $n^2$ whose entries are the undoubled matrix bits (`matRest_iff`). Define $A(u,v)$ to be the entry of $M$ at position $un+v$, using false if an index were out of range. In fact, for $u,v<n$, the row-major index is less than $n^2$ (`rowMajor_lt`), so this is an entry of the matrix. The standard row-major adjacency word for $A$ has length $n^2$ (`length_adjWord`), and its entry at $un+v$ is $A(u,v)$ (`adjWord_getD`). Thus it agrees with $M$ at every index below their common length; extensionality of lists by their entries (`ext_getD'`) gives equality of the two lists. The unary field condition is exactly the doubled encoding of $n$ true bits (`unaryRest_iff`). Combining this with the matrix-field description and the given doubled and plain binary-field conditions, the shape characterization (`eq_pathRaw_iff`) identifies $x$ with the raw encoding of the unary field, adjacency word, and binary expansions of $s,t$. Replacing the adjacency word by the equal row-major word just established yields $x=\operatorname{encodePATH}(n,A,s,t)$. Finally, at each valid row-major position, the matrix-field condition says that the relevant bit of $x$ equals the corresponding entry of $M$; by the definition of $A$, this is equivalent to $A(u,v)$ being true.

**Key facts.** `Complexity.matRest_iff`, `Complexity.rowMajor_lt`, `Complexity.length_adjWord`, `Complexity.adjWord_getD`, `Complexity.ext_getD'`, `Complexity.unaryRest_iff`, `Complexity.eq_pathRaw_iff`.
