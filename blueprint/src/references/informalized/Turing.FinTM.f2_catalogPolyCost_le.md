<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_catalogPolyCost_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Cost Bound

**Claim.** For natural numbers $q,C$ with $q>0$, and every natural number $r$, the recursively defined cost satisfies $\mathrm{cost}(q,C,r)\le (C+1+5r)q^r$.

**Proof.** Induct on $r$. At $r=0$, the cost is $C+1$, equal to the proposed bound. For the induction step, apply the recurrence and the induction hypothesis to obtain
\[
\mathrm{cost}(q,C,r+1)\le (C+1+5r)q^{r+1}+3q+2.
\]
Since $q>0$, we have $q\le q^{r+1}$ and $1\le q^{r+1}$. Thus $3q+2\le 5q^{r+1}$. Adding this to the first term gives $(C+1+5r+5)q^{r+1}$, which is the desired bound at $r+1$.
