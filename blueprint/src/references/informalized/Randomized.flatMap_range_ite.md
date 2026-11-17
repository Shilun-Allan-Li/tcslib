<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/QuasiPolyHierarchy.lean :: Randomized.flatMap_range_ite -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of a filtered concatenation

**Claim.** Among the indices $i<R$, exactly $\min(R,m)$ satisfy $i<m$. Each such index contributes $m$ copies of false, so the concatenated list is $m\min(R,m)$ copies of false.

**Proof.** Induct on $R$. When $R=0$, both lists are empty. For the successor step, append the contribution from index $R$ to the concatenation for the first $R$ indices. If $R<m$, that contribution is a list of $m$ false values, and the number of qualifying indices increases from $\min(R,m)=R$ to $R+1$, so the total number of copies increases by $m$. If $R\not<m$, the new contribution is empty and the minimum remains $m$. In each case the induction hypothesis gives the stated list.
