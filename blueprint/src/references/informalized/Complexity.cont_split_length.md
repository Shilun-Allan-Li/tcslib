<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.cont_split_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length Bound for the Emitted Split

**Claim.** For natural numbers $C,c$ and every binary word $y$, the word emitted by the polynomial split procedure has length at most $2|y|+2$.

**Proof.** If the bounded split search returns no index, the procedure emits the empty word, and the bound is immediate. Otherwise let $i$ be the returned index. Agreement of the split searches (`Complexity.cont_split_bridge`) identifies this result with the certificate search; the certificate specification (`Complexity.certificateSplit_spec`) therefore gives $i+(C+1)(i+1)^c=|y|$, in particular $i\le |y|$. The emitted word consists of two copies of each bit of the prefix of length $i$, followed by a two-bit separator and the suffix. Its length is thus $2i+2+|y|-i=|y|+i+2$, which is at most $2|y|+2$.

**Key facts.** `Complexity.cont_split_bridge`, `Complexity.certificateSplit_spec`.
