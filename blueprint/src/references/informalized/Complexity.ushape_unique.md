<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPath.lean :: Complexity.ushape_unique -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniqueness of Encoded Shape Parameters

**Claim.** If one bit string has the prescribed shape for both parameter triples $(n,s,t)$ and $(n',s',t')$, then $n=n'$, $s=s'$, and $t=t'$.

**Proof.** The two unary-shape conditions determine the same unary block, so uniqueness of its stopping position (`unaryRest_unique`) gives $n=n'$. With this equality, the two binary-delimited blocks for the source endpoint begin at the same position. Uniqueness of a block with a fixed start and delimiter (`dblAt_unique`) shows that the encoded source bit lists coincide. Since the natural-number binary encoding is injective (`LogProg.bits_injective`), this yields $s=s'$. The target blocks now also begin at the same position, because both $n$ and $s$ agree. Uniqueness for plain, length-delimited blocks (`plainAt_unique`) identifies their target bit lists, and injectivity of the binary encoding gives $t=t'$.

**Key facts.** `Complexity.unaryRest_unique`, `Complexity.dblAt_unique`, `Complexity.LogProg.bits_injective`, `Complexity.plainAt_unique`.
