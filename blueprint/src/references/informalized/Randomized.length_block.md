<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/NPPoly.lean :: Randomized.length_block -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of a List Block

**Claim.** If a list has length $Kc$ and $i<K$, then dropping its first $ic$ entries and taking the next $c$ entries produces a list of length $c$.

**Proof.** From $i<K$ we have $i+1\le K$, and multiplying by $c$ gives $ic+c\le Kc$. The list remaining after dropping $ic$ entries therefore has length at least $c$. Taking its first $c$ entries consequently gives a list of length exactly $c$.
