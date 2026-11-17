<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.tribeFrequencyPart_biUnion -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Block Decomposition of an Index Set

**Claim.** The union over all blocks of the mapped offsets selected by a finite set $T$ is exactly $T$.

**Proof.** To prove equality, check membership in both directions. If an index lies in the union, it comes from some block $i$ and an offset $o$ selected in that block; by the characterization of block frequency membership (`mem_tribeFrequencyPart`), the paired index corresponding to $(i,o)$ lies in $T$. Conversely, given $j\in T$, write its inverse image under the product-index equivalence as a pair $(i,o)$. The equivalence sends this pair back to $j$, so the membership characterization shows that $o$ is selected in block $i$, and its embedded image is $j$. Hence $j$ belongs to the union.

**Key facts.** `FABL.mem_tribeFrequencyPart`.
