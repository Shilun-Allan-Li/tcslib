<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clChunks_before -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Chunks Before the Final Round

**Claim.** For every $j\le R$, concatenating chunks at indices $0,\ldots,j-1$ gives the fragment formed from the concatenation of the formulas at those indices.

**Proof.** Proceed by induction on $j$. When $j=0$, both concatenations are empty. For the successor step, append the chunk at index $j$ to the chunks through index $j-1$. The induction hypothesis identifies the earlier chunks with the fragment of the earlier formulas. Since $j\le R$, we have $j\ne R$, so this chunk has no extra final separator. The fragment of a concatenation of formulas is the concatenation of their fragments (`Complexity.clFragment_append`), which gives the desired identity.

**Key facts.** `Complexity.clFragment_append`.
