<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.a3_split_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length bound for the split word

**Claim.** For natural numbers $C,c$ and a finite Boolean word $y$, the length of the split word of $y$ is at most $2|y|+2$.

**Proof.** If the search returns no split, the split word is empty, so the bound holds. Otherwise it returns some split point $i$. The successful-search specification (`a3_split_spec`) gives $i\le |y|$. The encoded word duplicates each of the first $i$ symbols, then inserts a two-symbol separator, and then appends the remaining $|y|-i$ symbols. Its length is therefore $2i+2+(|y|-i)=|y|+i+2$, which is at most $2|y|+2$ because $i\le |y|$.

**Key facts.** `Complexity.a3_split_spec`.
