<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Advice.lean :: Complexity.pairEncode_getElem? -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positions in a Pair Encoding

**Claim.** Each bit of $x$ occurs twice consecutively in the doubled portion of its pair encoding; the next two positions are $0$ and $1$, and subsequent positions reproduce $\alpha$, with out-of-range coordinates undefined.

**Proof.** Write the pair encoding as the doubled $x$ followed by $01$ and then $\alpha$. The doubled-string coordinate identity (`Complexity.doubled_getElem?`) gives, for each $p<|x|$, the bit $x_p$ at positions $2p$ and $2p+1$. The doubled-string length identity (`Complexity.length_doubled`) places the separator immediately after those $2|x|$ positions. Thus the next two positions contain $0$ and $1$. Every later position $2|x|+2+i$ is position $i$ in the final suffix $\alpha$, as follows by shifting past the doubled portion and the two separator bits. The coordinate assertions use partial indexing, so positions beyond a list's end are represented by undefined values.

**Key facts.** `Complexity.doubled_getElem?`, `Complexity.length_doubled`.
