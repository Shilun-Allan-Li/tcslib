<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathWalk.lean :: Complexity.dblAt_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Bit Decomposition of a Doubled Encoding

**Claim.** The doubled encoding of $b::u$ beginning at position $q$ holds exactly when $x$ has $b$ at positions $q$ and $q+1$, and the doubled encoding of $u$ begins at position $q+2$.

**Proof.** Unfold the definition of the doubled encoding and use $|b::u|=|u|+1$. In the forward direction, the encoding conditions at index $0$ give the two copies of $b$. For each index $i$ of $u$, apply the original conditions at index $i+1$; the identities $q+2(i+1)=q+2+2i$ and the list-tail indexing rule identify these with the conditions for $u$ starting at $q+2$. The delimiter positions likewise shift by two. Conversely, combine the two given copies of $b$ with the conditions for $u$ starting at $q+2$: index zero is handled by the copies of $b$, and every successor index reduces, by the same index identity and list-tail rule, to the corresponding condition for $u$. The shifted delimiter conditions give the delimiter for the whole word.
