<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Matching.lean :: Randomized.Matching.eq_encodeBPM_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterization of valid graph encodings

**Claim.** A bit string equals the encoding built from the length of its parsed first component and the adjacency matrix decoded from its parsed second component exactly when it is the pair encoding of a word of that length in ones and the parsed second component has length equal to the square of that length.

**Proof.** Write $u$ and $v$ for the parsed first and second components, and let $m=|u|$. Suppose first that $x$ equals the encoding formed from $m$ and the matrix decoded from $v$. Since the row-by-row adjacency word of that decoded matrix has length $m^2$ (length_adjWord), the assumed equality and the second-component parser identity show that $v$ is precisely this adjacency word. Thus $|v|=m^2$, and substituting this equality back into the encoding shows that $x$ is the pair encoding of the length-$m$ word of ones and $v$. Conversely, assume that $x$ is that pair encoding and $|v|=m^2$. Decoding the adjacency word of length $m^2$ and then listing its entries recovers the word (adjWord_adjOfWord). Consequently the encoding formed from the decoded matrix is exactly the given pair encoding, hence equals $x$.

**Key facts.** `Randomized.Matching.length_adjWord`, `Randomized.Matching.adjWord_adjOfWord`.
