<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/NPPoly.lean :: Randomized.length_flatMap_range -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of Concatenated List Blocks

**Claim.** If each list $g(j)$ has length $c$ for $j<K$, then concatenating $g(0),\ldots,g(K-1)$ gives a list of length $Kc$.

**Proof.** Induct on $K$. For $K=0$, the range is empty and the concatenation has length zero. For $K+1$, the range consists of the first $K$ indices followed by the final index $K$. By the induction hypothesis the first part contributes length $Kc$, and the hypothesis on $g$ gives length $c$ for the final list. Thus the total length is $Kc+c=(K+1)c$.
