<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean :: Complexity.eq_pairEncode_of_pairFstD_ne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reconstruction from a Nonempty First Projection

**Claim.** If a finite Boolean word $z$ has nonempty total first projection under the pairing parser, then $z$ is the pairing of its total first and second projections, using the encoding that doubles every bit of the first word, appends the separator $01$, and then appends the second word.

**Proof.** Inspect the parser's result on $z$. If parsing fails, its first decoded projection defaults to the empty word, contradicting the assumed nonemptiness. Thus parsing returns a pair $(a,b)$. The parser reconstruction theorem (`Turing.eq_pairEncode_of_pairDecode`) says that $z$ is the pairing encoding of this decoded pair. The two projection recovery facts (`Complexity.pairFstD_pairEncode` and `Complexity.pairSndD_pairEncode`) identify the total first and second projections of that encoding with $a$ and $b$, respectively. Substituting these identities yields the stated reconstruction.

**Key facts.** `Turing.eq_pairEncode_of_pairDecode`, `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`.
