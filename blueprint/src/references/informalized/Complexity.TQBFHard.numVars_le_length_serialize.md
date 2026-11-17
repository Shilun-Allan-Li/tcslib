<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHardTseitin.lean :: Complexity.TQBFHard.numVars_le_length_serialize -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoding Length Bounds Variable Count

**Claim.** For every CNF formula $\varphi$ over natural-number variables, its variable count is at most the length of its binary encoding.

**Proof.** The variable count is a fold of maxima over the numbers $\ell.1+1$ arising from literals in the clauses. It is therefore enough to bound each such number by the encoding length. Choose a clause $C$ containing the literal $\ell$. The length of the literal encoding is at most the length of the concatenation of all literal encodings in $C$ (`length_le_length_flatMap`). The encoding of $C$ with its clause marker is at least that long, since it adds a leading bit and a trailing separator. Likewise, its length is at most the length of the concatenation over all clauses (`length_le_length_flatMap`), which is at most the full formula encoding length after the final separator is added. Finally, the literal encoding has length $(\ell.1+1)+2=\ell.1+3$, so in particular $\ell.1+1$ is bounded by the full encoding length. Taking the maximum fold preserves this bound (`foldr_max_le`).

**Key facts.** `Complexity.TQBFHard.length_le_length_flatMap`, `Complexity.TQBFHard.foldr_max_le`.
