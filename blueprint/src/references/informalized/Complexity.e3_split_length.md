<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.e3_split_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length Bound for the Split Encoding

**Claim.** For natural numbers $C,c$ and a finite binary word $y$, the word emitted by the exponential split procedure on $y$ has length at most $2|y|+2$.

**Proof.** If the split search fails, the emitter returns the empty word, so the bound holds. Otherwise it returns the pair encoding of $y.take\ i$ and $y.drop\ i$ for a found index $i$. The split-search specification gives $i\le |y|$ (`Complexity.e3_split_spec`). The encoding has length twice the prefix length, plus two delimiter bits, plus the suffix length. Since the prefix length is $i$ and the suffix length is $|y|-i$, this total is $|y|+i+2\le 2|y|+2$.

**Key facts.** `Complexity.e3_split_spec`.
