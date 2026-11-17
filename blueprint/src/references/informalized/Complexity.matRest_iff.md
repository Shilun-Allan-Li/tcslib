<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathWalk.lean :: Complexity.matRest_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterization of the Matrix Remainder Condition

**Claim.** The paired-bit and final-marker conditions in the matrix remainder statement hold exactly when there is a word of length $n^2$ whose bits give the common value in each successive pair, with final bits $0,1$.

**Proof.** For the forward implication, define $M$ by taking, for each $j<n^2$, the bit of $x$ at position $2n+2+2j$. This word has length $n^2$. Its $j$th bit is therefore the first bit of the $j$th pair, and the assumed equality of the pair's two bits makes it the second bit as well. The assumed final-marker conditions give the required $0,1$ values at the positions following all $n^2$ pairs. Conversely, suppose such an $M$ exists. Its length is $n^2$, and the two entries at each pair of positions both equal the corresponding bit of $M$. Hence those entries agree for every $j<n^2$; the required final values follow directly from the stated marker conditions.
