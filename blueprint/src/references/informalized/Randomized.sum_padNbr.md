<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkMixingPad.lean :: Randomized.sum_padNbr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sum over padded neighbors

**Claim.** For a decidable relation on the indices with $n\le D$, the sum of $f$ over the $D$ padded neighbors of $s$ equals the sum over the indices related to $s$, plus $D$ minus the number of related indices, multiplied by $f(s)$.

**Proof.** Write $D=n+c$, using $n\le D$. Split the sum over the first $n$ positions and the remaining $c$ positions. In the first part, the padded neighbor at index $u$ is $u$ when $r(s,u)$ holds and is $s$ otherwise; in the remaining positions it is always $s$. Thus the first part contributes the sum of $f(u)$ over related indices together with one copy of $f(s)$ for each index not related to $s$, and the second part contributes $c$ further copies of $f(s)$. The related and unrelated indices partition the $n$ indices, so the number of copies of $f(s)$ is $(n-\#\{u:r(s,u)\})+c=D-\#\{u:r(s,u)\}$. Combining these terms gives the stated identity.
