<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.polyCost_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nested-Loop Cost Bound

**Claim.** For positive $q$, the recursively defined cost satisfies $\kappa_{q,C}(r)\le (C+1+5r)q^r$ for every $r$.

**Proof.** Proceed by induction on $r$. At $r=0$, the recursive definition gives $\kappa_{q,C}(0)=C+1$, which is the claimed bound. For the step, use the induction hypothesis in the recursion to obtain $\kappa_{q,C}(r+1)\le (C+1+5r)q^{r+1}+3q+2$. Since $q>0$, we have $q\le q^{r+1}$ and $1\le q^{r+1}$; hence $3q+2\le 5q^{r+1}$. Combining these estimates and collecting terms yields $(C+1+5(r+1))q^{r+1}$, as required.
