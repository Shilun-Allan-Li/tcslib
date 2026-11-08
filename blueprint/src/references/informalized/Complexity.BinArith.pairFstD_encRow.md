<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/DetMod.lean :: Complexity.BinArith.pairFstD_encRow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First projection of an encoded row

**Claim.** For a finite list $r$ of natural numbers, the first projection of its row encoding is the binary expansion of its first entry, with the first entry taken as $0$ when $r$ is empty.

**Proof.** If $r$ is empty, its row encoding is empty, whose first projection is empty; this is the binary expansion of zero. If $r$ has a first entry $n$, its row encoding begins with the encoding of $\operatorname{bits}(n)$, followed by the encodings of the remaining entries. The first projection therefore recovers $\operatorname{bits}(n)$, which is the binary expansion of $r.headD\,0$.

**Key facts.** `Complexity.pairFstD_nil`.
